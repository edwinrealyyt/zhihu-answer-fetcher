// ==UserScript==
// @name         知乎小助手
// @namespace    https://github.com/yourname/zhihu-answer-fetcher
// @version      1.0.0
// @description  知乎回答与评论全量获取助手，支持按点赞数/时间排序，让知乎内容阅读与分析更高效。
// @author       EdwinYyt
// @license      MIT
// @match        https://www.zhihu.com/question/*
// @grant        unsafeWindow
// @grant        GM_addStyle
// @run-at       document-start
// ==/UserScript==

(function () {
  'use strict';

  const QID = location.pathname.match(/\/question\/(\d+)/)?.[1];
  if (!QID) return;

  // 赞助收款码配置（支持在线图片 URL 或 Base64 编码，留空则显示配置提示）
  const WECHAT_QR = 'https://g.imgtg.com/uploads/10010/6a4c781c564cd.png';  // 微信收款码
  const ALIPAY_QR = 'https://g.imgtg.com/uploads/10010/6a4c781c4f672.jpg';  // 支付宝收款码

  // ═══════════════════════════════════════════════════════════
  // § 全局状态
  // ═══════════════════════════════════════════════════════════

  let rawAnswers    = [];
  let allAnswers    = [];
  let isFetching    = false;
  let isRequesting  = false;  // 防并发锁
  let activeRequests = 0;     // 当前活跃请求数
  const MAX_CONCURRENCY = 2;  // 最大并发通道数
  const failedOffsets = [];   // 失败重试队列

  // feeds API 状态（cursor 分页）
  let feedsNextUrl  = null;
  let feedsDone     = false;

  // answers API 状态（offset 分页，数据更完整）
  let answersOffset = 0;
  let answersDone   = false;
  let answersApiFailed = 0;  // 连续失败次数，超限后放弃直连
  let feedsApiFailed = 0;    // feeds 连续失败次数

  let capturedHdrs  = null;  // 拦截到的请求头，供直连复用
  let triggerTimer  = null;
  let watchdogTimer = null;
  let lastDataTs    = 0;
  let retryCount    = 0;
  let cntDirect     = 0;
  let cntIO         = 0;

  let origContainer = null;
  let resultEl      = null;
  let origSidebar   = null;
  let origSidebarDisplay = '';
  let origMainCol   = null;
  let origMainColWidth = '';
  let origMainColMaxWidth = '';
  let currentSorted = [];
  let currentPage   = 1;
  let itemsPerPage  = 50;
  let showImages    = false;  // 图片默认不加载

  const ioTrackers = [];
  const debugFailedAuthors = [];

  // 同时拦截两个端点
  const FEEDS_RE   = new RegExp('/api/v4/questions/' + QID + '/feeds');
  // 匹配 answers 但排除 /comments 子路径
  const ANSWERS_RE = new RegExp('/api/v4/questions/' + QID + '/answers(\\?|$)');

  // answers API 字段（含 comment_count 供评论按钮使用）
  const ANS_INCLUDE = encodeURIComponent(
    'data[*].is_normal,content,voteup_count,created_time,author,excerpt,comment_count'
  );

  let _origFetch = null;


  // ═══════════════════════════════════════════════════════════
  // § 1. Hook IntersectionObserver（必须在 Zhihu JS 之前）
  // ═══════════════════════════════════════════════════════════
  (function hookIO() {
    const _Orig = unsafeWindow.IntersectionObserver;
    if (!_Orig || unsafeWindow.__ZF_IO_HOOKED__) return;
    unsafeWindow.__ZF_IO_HOOKED__ = true;

    function ZfIO(callback, options) {
      const tracker = { callback, targets: [], io: null };
      ioTrackers.push(tracker);
      const io = new _Orig(callback, options);
      const _obs = io.observe.bind(io), _unobs = io.unobserve.bind(io);
      io.observe   = el => { tracker.targets.push(el); return _obs(el); };
      io.unobserve = el => { tracker.targets = tracker.targets.filter(x => x !== el); return _unobs(el); };
      tracker.io = io;
      return io;
    }
    ZfIO.prototype = _Orig.prototype;
    Object.setPrototypeOf(ZfIO, _Orig);
    unsafeWindow.IntersectionObserver = ZfIO;
    console.log('[ZF v0.9] ✅ IntersectionObserver hook OK');
  })();

  function fireAllIO() {
    if (!ioTrackers.length) return false;
    const now = performance.now();
    let fired = 0;
    for (const t of ioTrackers) {
      const targets = t.targets.length ? t.targets.slice(-2) : [];
      if (!targets.length) continue;
      for (const el of targets) {
        let rect;
        try { rect = el.getBoundingClientRect(); } catch { rect = new DOMRect(0, window.innerHeight - 2, 10, 2); }
        try {
          t.callback([{
            isIntersecting: true, intersectionRatio: 1.0,
            boundingClientRect: rect, intersectionRect: rect,
            rootBounds: null, target: el, time: now
          }], t.io);
          fired++;
        } catch (e) { console.warn('[ZF v0.9] IO cb error:', e.message); }
        break;
      }
    }
    if (fired) cntIO++;
    console.log(`[ZF v0.9] IO fire: ${fired}/${ioTrackers.length}`);
    return fired > 0;
  }


  // ═══════════════════════════════════════════════════════════
  // § 2. Hook fetch（同时拦截 feeds 和 answers 两个端点）
  //
  //   知乎在页面初始化时会通过 answers API 加载精选/置顶回答，
  //   这部分数据不在 feeds 里，必须单独拦截才不会缺失。
  // ═══════════════════════════════════════════════════════════
  (function installFetchHook() {
    if (typeof unsafeWindow.fetch !== 'function') { setTimeout(installFetchHook, 50); return; }
    if (unsafeWindow.__ZF_FETCH_HOOKED__) return;
    unsafeWindow.__ZF_FETCH_HOOKED__ = true;
    _origFetch = unsafeWindow.fetch.bind(unsafeWindow);

    unsafeWindow.fetch = async function (input, init) {
      const url = typeof input === 'string' ? input : (input?.url || String(input));

      const isFeeds   = FEEDS_RE.test(url);
      const isAnswers = ANSWERS_RE.test(url) && !url.includes('/comments');

      if (!isFeeds && !isAnswers) return _origFetch(input, init);

      console.log('[ZF v0.9] ▶', isFeeds ? 'feeds' : 'answers', url.slice(0, 100));

      // 捕获请求头供直连复用
      try {
        const h = init?.headers;
        capturedHdrs = h instanceof Headers ? Object.fromEntries(h.entries()) : (h ? { ...h } : {});
      } catch { /* ignore */ }

      let realResp;
      try { realResp = await _origFetch(input, init); }
      catch (e) { onRequestError(e.message); throw e; }

      let json;
      try { json = await realResp.clone().json(); } catch { return realResp; }

      const batch = [];
      if (isFeeds) {
        // feeds 结构：item.target 或 item.answer 包裹回答
        for (const item of (json.data || [])) {
          const ans = extractFromFeedsItem(item);
          if (ans) batch.push(ans);
        }
        feedsNextUrl = json.paging?.next || null;
        if (json.paging?.is_end) feedsDone = true;
      } else {
        // answers 结构：item 直接就是回答对象
        for (const item of (json.data || [])) {
          if (isAnswerObject(item)) batch.push(item);
        }
        if (json.paging?.is_end) answersDone = true;
      }

      rawAnswers.push(...batch);
      console.log(`[ZF v0.9] 被动 +${batch.length} | 累计 ${rawAnswers.length}`);
      onBatchReceived(batch.length, rawAnswers.length, false, isFeeds ? '被动/feeds' : '被动/answers');

      await new Promise(r => setTimeout(r, 100));
      return realResp;
    };

    console.log('[ZF v0.9] ✅ fetch hook OK, QID=' + QID);
  })();

  // feeds item → answer object
  function extractFromFeedsItem(item) {
    const t = item.target;
    // 严格限定 type='answer'，避免把文章(article)误判为回答
    if (t && t.type === 'answer') return t;
    // 兼容少数没有 type 字段但有回答特征的结构
    if (t && t.voteup_count != null && t.created_time != null && !t.type) return t;
    const a = item.answer;
    if (a && a.voteup_count != null) return a;
    return null;
  }

  // 判断一个对象是否为回答（用于 answers API 响应）
  function isAnswerObject(item) {
    return item && item.type === 'answer' && item.voteup_count != null;
  }


  // ═══════════════════════════════════════════════════════════
  // § 3. 直连 API
  //
  //   优先直连 answers API（offset 分页，数据最全）：
  //   能获取到知乎「默认排序」下的全部回答，包括精选/高赞回答。
  //   若 x-zse-96 签名被拒绝（4xx），自动回退到 feeds 直连。
  // ═══════════════════════════════════════════════════════════

  // 3a. 直连 answers API（主力，offset 分页，每次 20 条）
  async function tryDirectAnswers() {
    if (answersDone || !_origFetch || !capturedHdrs) return false;
    if (answersApiFailed >= 3) return false; // 连续失败 3 次则放弃
    if (activeRequests >= MAX_CONCURRENCY) return false;

    activeRequests++;

    // 优先从失败队列拉取，没有则使用最新的递增 offset
    let currentOffset;
    let isRetryingFailed = false;
    if (failedOffsets.length > 0) {
      currentOffset = failedOffsets.shift();
      isRetryingFailed = true;
    } else {
      currentOffset = answersOffset;
      answersOffset += 20; // 预增 20 条
    }

    const url = `https://www.zhihu.com/api/v4/questions/${QID}/answers`
      + `?include=${ANS_INCLUDE}&limit=20&offset=${currentOffset}&platform=desktop&sort_by=default`;

    try {
      console.log(`[ZF v0.9] → answers API offset=${currentOffset}${isRetryingFailed ? ' (重试)' : ''}`);
      const resp = await _origFetch(url, { method: 'GET', headers: capturedHdrs, credentials: 'include', mode: 'cors' });

      if (!resp.ok) {
        console.warn(`[ZF v0.9] answers API HTTP ${resp.status}`);
        answersApiFailed++;
        if (!isRetryingFailed) failedOffsets.push(currentOffset); // 压入重试队列
        return false;
      }

      const json = await resp.json();
      if (!Array.isArray(json.data)) {
        answersApiFailed++;
        if (!isRetryingFailed) failedOffsets.push(currentOffset);
        return false;
      }

      answersApiFailed = 0; // 重置失败计数
      const batch = json.data.filter(isAnswerObject);
      rawAnswers.push(...batch);

      // 到头判定：当前返回是 is_end，且没有积压的重试任务时，才算真正 Done
      if (json.paging?.is_end || (batch.length === 0 && !isRetryingFailed)) {
        if (failedOffsets.length === 0) {
          answersDone = true;
        }
      }

      cntDirect++;
      console.log(`[ZF v0.9] ✅ answers直连 +${batch.length} offset=${currentOffset} end=${answersDone}`);
      onBatchReceived(batch.length, rawAnswers.length, answersDone, '直连/answers');
      return true;
    } catch (e) {
      console.warn('[ZF v0.9] answers直连异常:', e.message);
      answersApiFailed++;
      if (!isRetryingFailed) failedOffsets.push(currentOffset);
      return false;
    } finally {
      activeRequests--;
      // 释放后立刻唤醒下一次调度，试图填满并发通道
      if (isFetching && !answersDone) {
        scheduleFetch(50);
      }
    }
  }

  // 3b. 直连 feeds paging.next（备用）
  async function tryDirectFeeds() {
    if (feedsDone || !feedsNextUrl || !_origFetch || !capturedHdrs) return false;
    if (feedsApiFailed >= 3) return false;
    if (isRequesting) return false;

    isRequesting = true;
    try {
      const resp = await _origFetch(feedsNextUrl, { method: 'GET', headers: capturedHdrs, credentials: 'include', mode: 'cors' });
      if (!resp.ok) {
        console.warn(`[ZF v0.9] feeds API HTTP ${resp.status}`);
        feedsApiFailed++;
        return false;
      }
      const json = await resp.json();
      if (!Array.isArray(json.data)) {
        feedsApiFailed++;
        return false;
      }

      feedsApiFailed = 0; // 重置失败计数
      const batch = [];
      for (const item of json.data) {
        const ans = extractFromFeedsItem(item);
        if (ans) batch.push(ans);
      }
      rawAnswers.push(...batch);
      feedsNextUrl = json.paging?.next || null;
      if (json.paging?.is_end) feedsDone = true;

      cntDirect++;
      onBatchReceived(batch.length, rawAnswers.length, false, '直连/feeds');
      return true;
    } catch (e) {
      console.warn('[ZF v0.9] feeds直连异常:', e.message);
      feedsApiFailed++;
      return false;
    } finally {
      isRequesting = false;
    }
  }


  // ═══════════════════════════════════════════════════════════
  // § 4. 触发引擎（三级策略）
  // ═══════════════════════════════════════════════════════════
  function scheduleFetch(delay) {
    clearTimeout(triggerTimer);
    triggerTimer = setTimeout(async () => {
      if (!isFetching) return;

      const answersDoneOrFailed = answersDone || answersApiFailed >= 3;
      const feedsDoneOrFailed = feedsDone || feedsApiFailed >= 3 || (!feedsNextUrl && (Date.now() - lastDataTs > 2000));

      if (answersDoneOrFailed && feedsDoneOrFailed && activeRequests === 0) {
        onFetchComplete(false);
        return;
      }

      let startedAny = false;

      // 循环填充并发通道（至多 MAX_CONCURRENCY 个并发请求）
      while (activeRequests < MAX_CONCURRENCY && !answersDone && isFetching) {
        const ansOk = await tryDirectAnswers();
        if (!ansOk) break;
        startedAny = true;
        // 适当微小间隔（约 80ms），既可以极速并发，又能防止请求撞在同一毫秒内被安全风控判定
        await new Promise(r => setTimeout(r, 80));
      }

      // 如果直连没有在运行（通道数为0）且备用 feeds 直连未做完，降级走 feeds
      if (activeRequests === 0 && !feedsDone && isFetching) {
        const feedsOk = await tryDirectFeeds();
        if (feedsOk) {
          startedAny = true;
          feedsApiFailed = 0; // 重置 feeds 失败计数
        } else {
          // 兜底：IO + 滚动
          fireAllIO();
          unsafeWindow.scrollTo({ top: document.body.scrollHeight });
          unsafeWindow.dispatchEvent(new Event('scroll'));
          document.dispatchEvent(new Event('scroll'));
        }
      }

      // 如果没有启动任何新请求，且当前有请求在运行，我们等运行完的回调来调度。
      // 如果完全没有请求在运行，为了防止卡死，我们在 1 秒后再次调度检查完成状态。
      if (!startedAny && activeRequests === 0 && isFetching) {
        scheduleFetch(1000);
      }
    }, delay);
  }

  function startWatchdog() {
    const POLL = 3000, TIMEOUT = 14000, MAX = 4;
    watchdogTimer = setInterval(async () => {
      if (!isFetching) { clearInterval(watchdogTimer); return; }
      if (Date.now() - lastDataTs < TIMEOUT) return;
      retryCount++;
      if (retryCount > MAX) { clearInterval(watchdogTimer); onFetchComplete(true); return; }
      console.log(`[ZF v0.9] 看门狗 retry ${retryCount}/${MAX}`);
      lastDataTs = Date.now();
      updateStatus(`⚠️ 重试 ${retryCount}/${MAX}...`);
      unsafeWindow.scrollTo({ top: 0 });
      await new Promise(r => setTimeout(r, 300));
      fireAllIO();
      scheduleFetch(400);
    }, POLL);
  }


  // ═══════════════════════════════════════════════════════════
  // § 5. 数据回调
  // ═══════════════════════════════════════════════════════════
  function onBatchReceived(batchLen, total, ended, method) {
    if (!isFetching && allAnswers.length > 0) return;

    if (isFetching) {
      lastDataTs = Date.now();
      retryCount = 0;
    }

    // 实时去重并更新界面统计
    const seen = new Set();
    const uniqueAnswers = rawAnswers.filter(a => {
      const id = a.id ?? a.answer_id;
      if (id == null) return true;
      if (seen.has(id)) return false;
      seen.add(id); return true;
    });

    updateCount(uniqueAnswers.length);

    if (ended) {
      onFetchComplete(false);
    } else if (isFetching) {
      const bg = document.hidden ? '📱 后台' : '⏳';
      updateStatus(`${bg} ${uniqueAnswers.length} 条（+${batchLen}）<br><small>${method}</small>`);
      scheduleFetch(250);
    }
  }

  function onRequestError(msg) {
    updateStatus(`❌ 请求出错: ${msg}`);
    if (isFetching) scheduleFetch(3000);
  }

  function onFetchComplete(isTimeout) {
    clearTimeout(triggerTimer);
    clearInterval(watchdogTimer);
    isFetching = false;

    // 去重（按 answer id）
    const seen = new Set();
    allAnswers = rawAnswers.filter(a => {
      const id = a.id ?? a.answer_id;
      if (id == null) return true;
      if (seen.has(id)) return false;
      seen.add(id); return true;
    });

    const btn = document.getElementById('zf-btn-fetch');
    if (btn) { btn.disabled = false; btn.textContent = '🔄 重新获取'; }
    document.getElementById('zf-btn-stop')?.remove();
    updateCount(allAnswers.length);
    setSortEnabled(allAnswers.length > 0);

    const stats = `直连 ${cntDirect} · IO ${cntIO}`;
    updateStatus(isTimeout
      ? `⚠️ 超时停止<br>${allAnswers.length} 条可排序<br><small>${stats}</small>`
      : `✅ 完成！共 ${allAnswers.length} 条<br><small>${stats}</small>`
    );
    const bar = document.getElementById('zf-progress-bar');
    if (bar) bar.style.width = '100%';
    if (!isTimeout) setTimeout(() => unsafeWindow.scrollTo({ top: 0, behavior: 'smooth' }), 300);
  }


  // ═══════════════════════════════════════════════════════════
  // § 6. 抓取控制
  // ═══════════════════════════════════════════════════════════
  async function onFetchAll() {
    if (isFetching) return;
    isFetching = true; retryCount = 0; cntDirect = 0; cntIO = 0;
    isRequesting = false;
    activeRequests = 0;
    failedOffsets.length = 0;
    rawAnswers = []; allAnswers = [];
    feedsNextUrl = null; feedsDone = false; feedsApiFailed = 0;
    answersOffset = 0; answersDone = false; answersApiFailed = 0;

    setSortEnabled(false); updateCount(0);
    const btn = document.getElementById('zf-btn-fetch');
    if (btn) { btn.disabled = true; btn.textContent = '⏳ 抓取中...'; }
    addStopButton();
    updateStatus('🚀 启动抓取...<br><small>可切换到其他标签页</small>');

    unsafeWindow.scrollTo({ top: 0 });
    await new Promise(r => setTimeout(r, 400));
    lastDataTs = Date.now();

    // 首次触发三管齐下
    unsafeWindow.scrollTo({ top: document.body.scrollHeight });
    unsafeWindow.dispatchEvent(new Event('scroll'));
    fireAllIO();
    scheduleFetch(500);
    startWatchdog();
  }

  function onStopFetch() {
    if (!isFetching) return;
    clearTimeout(triggerTimer); clearInterval(watchdogTimer);
    onFetchComplete(true);
  }


  // ═══════════════════════════════════════════════════════════
  // § 7. 评论功能
  // ═══════════════════════════════════════════════════════════
  const CMT_INCLUDE = encodeURIComponent(
    'data[*].author,data[*].author.url_token,data[*].content,data[*].vote_count,data[*].voteup_count,data[*].created_time,' +
    'data[*].reply_to_author,data[*].reply_to_author.url_token,data[*].reply_to_comment,data[*].is_author,data[*].collapsed,data[*].child_comment_count,' +
    'data[*].child_comments[*].author,data[*].child_comments[*].author.url_token,data[*].child_comments[*].content,data[*].child_comments[*].vote_count,data[*].child_comments[*].created_time,data[*].child_comments[*].reply_to_author,data[*].child_comments[*].reply_to_author.url_token,data[*].child_comments[*].reply_to_comment'
  );

  const CHILD_CMT_INCLUDE = encodeURIComponent(
    'data[*].author,data[*].author.url_token,data[*].content,data[*].vote_count,data[*].voteup_count,data[*].created_time,' +
    'data[*].reply_to_author,data[*].reply_to_author.url_token,data[*].reply_to_comment'
  );

  async function loadComments(answerId, offset) {
    if (!_origFetch || !capturedHdrs) throw new Error('请先点击「获取所有回答」以初始化鉴权');
    const url = `https://www.zhihu.com/api/v4/answers/${answerId}/comments`
      + `?include=${CMT_INCLUDE}&order_by=score&limit=20&offset=${offset}&status=open`;
    const resp = await _origFetch(url, { headers: capturedHdrs, credentials: 'include', mode: 'cors' });
    if (!resp.ok) throw new Error('HTTP ' + resp.status);
    return resp.json();
  }

  async function loadChildComments(commentId, offset) {
    if (!_origFetch || !capturedHdrs) throw new Error('未初始化鉴权');
    const url = `https://www.zhihu.com/api/v4/comments/${commentId}/child_comments`
      + `?include=${CHILD_CMT_INCLUDE}&limit=20&offset=${offset}`;
    const resp = await _origFetch(url, { headers: capturedHdrs, credentials: 'include', mode: 'cors' });
    if (!resp.ok) throw new Error('HTTP ' + resp.status);
    return resp.json();
  }

  async function loadAllComments(answerId) {
    let allData = [];
    let offset = 0;
    let isEnd = false;
    let maxRequests = 40; 
    let reqCount = 0;

    while (!isEnd && reqCount < maxRequests) {
      const json = await loadComments(answerId, offset);
      if (json.data && Array.isArray(json.data)) {
        allData.push(...json.data);
      }
      isEnd = json.paging?.is_end ?? true;
      if (!isEnd) {
        offset += json.data?.length ?? 20;
      }
      reqCount++;
      if (!isEnd) {
        await new Promise(r => setTimeout(r, 120));
      }
    }
    return {
      data: allData,
      paging: { is_end: true, totals: allData.length }
    };
  }

  async function loadAllChildComments(commentId) {
    let allData = [];
    let offset = 0;
    let isEnd = false;
    let maxRequests = 25; 
    let reqCount = 0;

    while (!isEnd && reqCount < maxRequests) {
      const json = await loadChildComments(commentId, offset);
      if (json.data && Array.isArray(json.data)) {
        allData.push(...json.data);
      }
      isEnd = json.paging?.is_end ?? true;
      if (!isEnd) {
        offset += json.data?.length ?? 20;
      }
      reqCount++;
      if (!isEnd) {
        await new Promise(r => setTimeout(r, 120));
      }
    }
    return allData;
  }

  async function openReplyModal(commentId, commentAuthor, totalCount) {
    // 废弃，已由一级弹窗后台自动全量补全和原样展现取代
  }

  async function openCommentModal(answerId, commentCount, authorName) {
    if (!capturedHdrs) {
      updateStatus('⚠️ 请先完成一次「获取所有回答」<br><small>需要鉴权信息才能加载评论</small>');
      return;
    }

    document.getElementById('zf-comment-modal')?.remove();

    const modal = document.createElement('div');
    modal.id = 'zf-comment-modal';
    modal.className = 'zf-modal-mask';

    const container = document.createElement('div');
    container.className = 'zf-modal-container';

    const header = document.createElement('div');
    header.className = 'zf-modal-header';
    header.innerHTML = `
      <div class="zf-modal-title">
        💬 评论 (${commentCount} 条) <span style="font-size:12px; font-weight:normal; color:#8e8e93; margin-left:8px;">回答作者: ${authorName}</span>
      </div>
      <button class="zf-modal-close-btn">&times;</button>
    `;
    container.appendChild(header);

    const body = document.createElement('div');
    body.className = 'zf-modal-body';

    const loadingDiv = document.createElement('div');
    loadingDiv.style.cssText = 'text-align:center; padding:50px 0; color:#8e8e93; font-size:13px;';
    loadingDiv.innerHTML = '⏳ 正在加载评论...';
    body.appendChild(loadingDiv);
    container.appendChild(body);
    modal.appendChild(container);
    document.body.appendChild(modal);
    updateBodyScroll();

    const closeModal = () => {
      modal.style.animation = 'zf-fade-in 0.15s ease-out reverse';
      container.style.animation = 'zf-scale-up 0.15s ease-out reverse';
      setTimeout(() => {
        modal.remove();
        updateBodyScroll();
      }, 140);
    };

    header.querySelector('.zf-modal-close-btn').onclick = closeModal;
    modal.onclick = (e) => {
      if (e.target === modal) closeModal();
    };

    const escHandler = (e) => {
      if (e.key === 'Escape') {
        closeModal();
        document.removeEventListener('keydown', escHandler);
      }
    };
    document.addEventListener('keydown', escHandler);

    try {
      const json = await loadAllComments(answerId);

      // 统一的名字获取器，兼容不同版本的接口作者名字封装
      const getAuthorName = (c) => {
        if (!c || !c.author) return '知乎用户';
        return c.author.member?.name || c.author.name || (c.author.role === 'anonymous' ? 'anonymous' : '知乎用户');
      };

      // 1. 同步预整合扁平 Map，提取所有真实的和需要生成的虚拟根评论节点
      if (json.data && Array.isArray(json.data)) {
        const flatCommentsMap = new Map();
        const feedIntoMap = (c) => {
          if (!c || !c.id) return;
          const idStr = String(c.id);
          if (!flatCommentsMap.has(idStr)) {
            flatCommentsMap.set(idStr, c);
          }
          if (c.child_comments && Array.isArray(c.child_comments)) {
            c.child_comments.forEach(feedIntoMap);
          }
        };
        json.data.forEach(feedIntoMap);

        const allFlatComments = Array.from(flatCommentsMap.values());
        const commentMap = new Map();
        allFlatComments.forEach(c => {
          commentMap.set(String(c.id), c);
        });

        // 探测出所有缺失的虚拟根评论对象 (如知乎已注销、删除的父 ID)
        const virtualRootsMap = new Map();
        allFlatComments.forEach(c => {
          const idStr = String(c.id);
          const parentId = c.reply_comment_id || c.reply_to_comment?.id || c.reply_to_comment_id || c.reply_root_comment_id || c.root_comment_id;
          if (parentId && String(parentId) !== idStr) {
            const pIdStr = String(parentId);
            
            if (!commentMap.has(pIdStr)) {
              let placeholderAuthor = '知乎用户';
              const replyCommentId = c.reply_comment_id || c.reply_to_comment?.id || c.reply_to_comment_id;
              const replyAuthorName = c.reply_to_author?.member?.name || c.reply_to_author?.name;
              if (replyAuthorName && String(replyCommentId) === pIdStr) {
                placeholderAuthor = replyAuthorName;
              } else {
                const anyReply = allFlatComments.find(
                  x => String(x.reply_comment_id || x.reply_to_comment?.id || x.reply_to_comment_id || x.reply_root_comment_id || x.root_comment_id) === pIdStr && (x.reply_to_author?.member?.name || x.reply_to_author?.name)
                );
                if (anyReply) placeholderAuthor = anyReply.reply_to_author?.member?.name || anyReply.reply_to_author?.name || '知乎用户';
              }

              // 预构建虚拟根节点加入 Map，以防丢失补全的扫描
              const virtualRoot = {
                id: parentId,
                content: `<span style="color:#ef4444;font-size:12px;opacity:0.85;font-style:italic;">⚠️ 原始主评论未在列表中载入（可能被知乎折叠或已删除）</span>`,
                created_time: (c.created_time || 0) - 1, 
                vote_count: 0,
                child_comments_count: 1, 
                author: { member: { name: placeholderAuthor } },
                _isVirtualPlaceholder: true,
                child_comments: []
              };
              
              commentMap.set(pIdStr, virtualRoot);
              virtualRootsMap.set(pIdStr, virtualRoot);
            }
          }
        });

        // 2. 收集所有实锤含有子回复的根卡片 ID
        // 采用双重检索：(A) 物理 ID 关联判定  (B) 物理 ID 缺失时的作者名字模糊关联判定 (用于知乎外置的高赞回复)
        const rootIdsToFetch = new Set();
        allFlatComments.forEach(c => {
          const idStr = String(c.id);
          
          // 2.1 物理 ID 直接判定
          const parentId = c.reply_comment_id || c.reply_to_comment?.id || c.reply_to_comment_id || c.reply_root_comment_id || c.root_comment_id;
          if (parentId && String(parentId) !== idStr) {
            rootIdsToFetch.add(String(parentId));
            return;
          }
          
          // 2.2 名字模糊判定兜底 (补齐外置子评论的关系网)
          const replyAuthorName = c.reply_to_author?.member?.name || c.reply_to_author?.name;
          if (replyAuthorName) {
            const isCommonName = replyAuthorName === '匿名用户' || (replyAuthorName.startsWith('知乎用户') && replyAuthorName.length <= 6);
            const matchingComment = allFlatComments.find(
              x => getAuthorName(x) === replyAuthorName && (!isCommonName || String(x.id) !== idStr)
            );
            if (matchingComment) {
              rootIdsToFetch.add(String(matchingComment.id));
            }
          }
        });

        const pendingNodes = [];
        rootIdsToFetch.forEach(pIdStr => {
          if (commentMap.has(pIdStr)) {
            const targetNode = commentMap.get(pIdStr);
            pendingNodes.push({
              commentId: pIdStr,
              targetNode: targetNode,
              loadedCount: 0,
              isVirtual: !!targetNode._isVirtualPlaceholder
            });
          }
        });

        // 3. 执行补全拉取
        if (pendingNodes.length > 0) {
          loadingDiv.innerHTML = `⏳ 正在后台自动补全二级回复 (0/${pendingNodes.length})...`;
          
          let completed = 0;
          let activeChildRequests = 0;
          let cursor = 0;
          
          await new Promise((resolve) => {
            const next = async () => {
              if (cursor >= pendingNodes.length) {
                if (activeChildRequests === 0) resolve();
                return;
              }
              
              const node = pendingNodes[cursor++];
              activeChildRequests++;
              
              try {
                const allChildData = [];
                let isChildEnd = false;
                let childOffset = 0; // 强行从 0 开始翻页拉取，防止因混合热度/时间排序差异导致的漏拉
                let maxChildRequests = 15; // 最多拉取 300 条回复，防止无限刷
                let childReqCount = 0;
                
                while (!isChildEnd && childReqCount < maxChildRequests) {
                  const childJson = await loadChildComments(node.commentId, childOffset);
                  if (childJson.data && Array.isArray(childJson.data)) {
                    allChildData.push(...childJson.data);
                  }
                  isChildEnd = childJson.paging?.is_end ?? true;
                  if (!isChildEnd) {
                    childOffset += childJson.data?.length ?? 20;
                  }
                  childReqCount++;
                  if (!isChildEnd) {
                    await new Promise(r => setTimeout(r, 60)); // 频控保护
                  }
                }
                
                if (!node.targetNode.child_comments) {
                  node.targetNode.child_comments = [];
                }
                // 去重合入
                const existingIds = new Set(node.targetNode.child_comments.map(x => String(x.id)));
                allChildData.forEach(ch => {
                  if (!existingIds.has(String(ch.id))) {
                    node.targetNode.child_comments.push(ch);
                  }
                });

                // 刷新子回复统计
                node.targetNode.child_comments_count = node.targetNode.child_comments.length;
                
              } catch (err) {
                console.warn('[ZF] 自动补全回复数据失败:', node.commentId, err);
              } finally {
                completed++;
                activeChildRequests--;
                loadingDiv.innerHTML = `⏳ 正在后台自动补全二级回复 (${completed}/${pendingNodes.length})...`;
                next();
              }
            };
            
            // 采用并发度 2，安全稳定地高速拉取数据
            for (let i = 0; i < Math.min(2, pendingNodes.length); i++) {
              next();
            }
          });
        }

        // 把在预扫描里成功补全好数据的虚拟卡片们，也统一塞入 json.data 数组中，以便后续 buildCommentSection 能够渲染
        virtualRootsMap.forEach((vRoot) => {
          if (vRoot.child_comments && vRoot.child_comments.length > 0) {
            json.data.push(vRoot);
          }
        });
      }

      loadingDiv.remove();
      const section = buildCommentSection(json, answerId, 0);
      body.appendChild(section);
    } catch (e) {
      loadingDiv.innerHTML = `❌ 评论加载失败: ${e.message || e}<br><br><button class="zf-sort-btn" style="background:#7c3aed;color:#fff;padding:5px 12px;" id="zf-modal-retry">点击重试</button>`;
      const retryBtn = loadingDiv.querySelector('#zf-modal-retry');
      if (retryBtn) {
        retryBtn.onclick = () => {
          modal.remove();
          updateBodyScroll();
          document.removeEventListener('keydown', escHandler);
          openCommentModal(answerId, commentCount, authorName);
        };
      }
      console.error('[ZF v0.9] 评论加载失败:', e);
    }
  }

  // 统一的页面滚动控制器，防止弹窗滚动穿透到背景页面
  function updateBodyScroll() {
    const hasModal = document.querySelector('.zf-modal-mask') || document.getElementById('zf-comment-modal');
    if (hasModal) {
      document.body.style.overflow = 'hidden';
    } else {
      document.body.style.overflow = '';
    }
  }

  // 辅助函数：根据知乎返回的扁平列表重组并渲染评论
  function renderGroupedComments(comments, listContainer, sortBy = 'default') {
    // 统一的名字获取器，完美兼容 V4（c.author.name）与 V5（c.author.member.name）接口数据结构
    const getAuthorName = (c) => {
      if (!c || !c.author) return '知乎用户';
      return c.author.member?.name || c.author.name || (c.author.role === 'anonymous' ? 'anonymous' : '知乎用户');
    };

    // 1. 扁平化整合：由于知乎返回的 comments 中，每个评论对象可能都内嵌了 child_comments 列表
    // 为了进行彻底和正确的树状重组，我们把所有内嵌的子评论也提取出来，合并成一个包含所有评论的去重扁平数组
    const flatCommentsMap = new Map();
    const feedIntoMap = (c) => {
      if (!c || !c.id) return;
      const idStr = String(c.id);
      if (!flatCommentsMap.has(idStr)) {
        flatCommentsMap.set(idStr, c);
      }
      if (c.child_comments && Array.isArray(c.child_comments)) {
        c.child_comments.forEach(feedIntoMap);
      }
    };
    comments.forEach(feedIntoMap);

    const allFlatComments = Array.from(flatCommentsMap.values());

    // 2. 初始化 Map 结构
    const commentMap = new Map();
    const roots = [];
    allFlatComments.forEach(c => {
      const idStr = String(c.id);
      commentMap.set(idStr, {
        data: c,
        children: []
      });
    });

    // 2.5 扫描：如果发现某个子评论的父级 ID (parentId) 在当前 Map 中不存在，则在 Map 中自动创建对应的虚拟占位根卡片
    // 这样做能避免该根评论下的子评论（如高赞被直接返回的评论）在最外层散落，全部整齐地缩进在主分支下
    // 同时也完美解决了根评论被知乎删除、折叠后，子评论无家可归独自沦为独立卡片的 bug
    allFlatComments.forEach(c => {
      const idStr = String(c.id);
      const parentId = c.reply_comment_id || c.reply_to_comment?.id || c.reply_to_comment_id || c.reply_root_comment_id || c.root_comment_id;
      
      if (parentId && String(parentId) !== idStr) {
        const pIdStr = String(parentId);
        
        // 如果当前 commentMap 里没有它的父级评论
        if (!commentMap.has(pIdStr)) {
          // 寻找该根评论的作者名字
          let placeholderAuthor = '知乎用户';
          const replyCommentId = c.reply_comment_id || c.reply_to_comment?.id || c.reply_to_comment_id;
          const replyAuthorName = c.reply_to_author?.member?.name || c.reply_to_author?.name;
          if (replyAuthorName && String(replyCommentId) === pIdStr) {
            placeholderAuthor = replyAuthorName;
          } else {
            // 兜底：从当前同属该根评论的兄弟评论里找被回复人
            const anyReply = allFlatComments.find(
              x => String(x.reply_comment_id || x.reply_to_comment?.id || x.reply_to_comment_id || x.reply_root_comment_id || x.root_comment_id) === pIdStr && (x.reply_to_author?.member?.name || x.reply_to_author?.name)
            );
            if (anyReply) placeholderAuthor = anyReply.reply_to_author?.member?.name || anyReply.reply_to_author?.name || '知乎用户';
          }
          
          const virtualRoot = {
            id: parentId,
            content: `<span style="color:#ef4444;font-size:12px;opacity:0.85;font-style:italic;">⚠️ 原始主评论未在列表中载入（可能被知乎折叠或已删除）</span>`,
            created_time: (c.created_time || 0) - 1, 
            vote_count: 0,
            child_comments_count: 1, 
            author: {
              member: {
                name: placeholderAuthor
              }
            },
            _isVirtualPlaceholder: true
          };
          
          commentMap.set(pIdStr, {
            data: virtualRoot,
            children: []
          });
          
          roots.push(commentMap.get(pIdStr));
        }
      }
    });

    // 3. 将所有子评论重新分配到各自 the parent
    allFlatComments.forEach(c => {
      const idStr = String(c.id);
      const wrapped = commentMap.get(idStr);
      if (wrapped.data._isVirtualPlaceholder) return; // 占位符本身已经在 roots 中，无需再分配
      
      // 寻找父级评论 ID
      const parentId = c.reply_comment_id || c.reply_to_comment?.id || c.reply_to_comment_id || c.reply_root_comment_id || c.root_comment_id;
      const parentIdStr = parentId ? String(parentId) : null;
      const rootCommentIdStr = (c.reply_root_comment_id || c.root_comment_id) ? String(c.reply_root_comment_id || c.root_comment_id) : null;

      // 兜底：如果 API 没返回 parentId 但存在回复作者，尝试匹配当前列表中该作者的最后一条评论
      let targetParentIdStr = parentIdStr;
      if (!targetParentIdStr) {
        const replyAuthorName = c.reply_to_author?.member?.name || c.reply_to_author?.name;
        if (replyAuthorName) {
          const isCommonName = replyAuthorName === '匿名用户' || (replyAuthorName.startsWith('知乎用户') && replyAuthorName.length <= 6);
          const matchingComment = allFlatComments.find(
            x => getAuthorName(x) === replyAuthorName && (!isCommonName || String(x.id) !== idStr)
          );
          if (matchingComment) targetParentIdStr = String(matchingComment.id);
        }
      }

      if (targetParentIdStr && targetParentIdStr !== idStr && commentMap.has(targetParentIdStr)) {
        // 递归找到最顶层的根评论节点（保证所有回复均折叠在根评论下方）
        let rootNode = commentMap.get(targetParentIdStr);
        const visited = new Set([idStr]);
        while (rootNode) {
          const rId = rootNode.data.reply_comment_id || rootNode.data.reply_to_comment_id || rootNode.data.reply_to_comment?.id || rootNode.data.reply_root_comment_id || rootNode.data.root_comment_id;
          const rIdStr = rId ? String(rId) : null;
          if (rIdStr && rIdStr !== String(rootNode.data.id) && commentMap.has(rIdStr) && !visited.has(rIdStr)) {
            visited.add(rIdStr);
            rootNode = commentMap.get(rIdStr);
          } else {
            break;
          }
        }
        rootNode.children.push(wrapped);
      } 
      // 兜底：如果直接父级在 Map 中不存在，但所属的根评论在 Map 中存在，则归入该根评论下
      else if (rootCommentIdStr && rootCommentIdStr !== idStr && commentMap.has(rootCommentIdStr)) {
        let rootNode = commentMap.get(rootCommentIdStr);
        rootNode.children.push(wrapped);
      } 
      // 确实是根评论
      else {
        roots.push(wrapped);
      }
    });

    // 4. 对根评论进行排序
    if (sortBy === 'votes') {
      roots.sort((a, b) => {
        const va = a.data.vote_count ?? a.data.voteup_count ?? a.data.up_count ?? 0;
        const vb = b.data.vote_count ?? b.data.voteup_count ?? b.data.up_count ?? 0;
        return vb - va;
      });
    } else if (sortBy === 'replies') {
      roots.sort((a, b) => {
        const ca = a.data.child_comments_count ?? a.data.child_comment_count ?? a.data.children_count ?? a.data.reply_count ?? a.children.length ?? 0;
        const cb = b.data.child_comments_count ?? b.data.child_comment_count ?? b.data.children_count ?? b.data.reply_count ?? b.children.length ?? 0;
        return cb - ca;
      });
    } else if (sortBy === 'time-desc') {
      roots.sort((a, b) => (b.data.created_time || 0) - (a.data.created_time || 0));
    } else if (sortBy === 'time-asc') {
      roots.sort((a, b) => (a.data.created_time || 0) - (b.data.created_time || 0));
    } else {
      // 还原默认顺序 (API 原生排序)
      roots.sort((a, b) => (a.data._origIdx ?? 0) - (b.data._origIdx ?? 0));
    }

    // 5. 渲染
    roots.forEach(root => {
      const rootEl = buildCommentItem(root.data, false);
      const total = root.data.child_comments_count ?? root.data.child_comment_count ?? root.data.children_count ?? root.data.reply_count ?? 0;

      // 在进行了彻底的重新归类分配后，我们递归压平并去重收集该根评论下属的所有子孙评论 (完美解决深层嵌套 Level 3/4 二级回复截断缺失 Bug)
      const seenChildIds = new Set();
      const mergedChildren = [];
      const collectAllDescendants = (node) => {
        if (!node || !node.children) return;
        node.children.forEach(ch => {
          const chIdStr = String(ch.data.id);
          if (!seenChildIds.has(chIdStr)) {
            seenChildIds.add(chIdStr);
            mergedChildren.push(ch);
            collectAllDescendants(ch);
          }
        });
      };
      collectAllDescendants(root);
      
      if (mergedChildren.length > 0 || total > 0) {
        // 创建子回复容器
        const box = document.createElement('div');
        box.className = 'zf-replies-box';
        const repliesList = document.createElement('div');
        box.appendChild(repliesList);
        
        if (mergedChildren.length > 0) {
          // 子回复始终按时间正序排列
          mergedChildren.sort((a, b) => (a.data.created_time || 0) - (b.data.created_time || 0));
          mergedChildren.forEach(child => {
            repliesList.appendChild(buildCommentItem(child.data, true));
          });
        }
        
        rootEl.appendChild(box);
        
        // 彻底取消所有用于“查看全部”或“展开更多”的按钮，直接依靠后台在载入时全量静默补齐数据并完美铺开
      }
      
      listContainer.appendChild(rootEl);
    });
  }

function buildCommentSection(json, answerId, startOffset) {
    const section = document.createElement('div');
    section.className = 'zf-comment-section';

    const sortBar = document.createElement('div');
    sortBar.className = 'zf-comment-sort-bar';
    sortBar.innerHTML = `
      <span class="zf-sort-label">排序方式：</span>
      <button class="zf-sort-btn active" data-sort="default">🔥 默认</button>
      <button class="zf-sort-btn" data-sort="votes">👍 点赞数</button>
      <button class="zf-sort-btn" data-sort="replies">💬 回复数</button>
      <button class="zf-sort-btn" data-sort="time-desc">🕐 最新</button>
      <button class="zf-sort-btn" data-sort="time-asc">🕑 最早</button>
    `;
    section.appendChild(sortBar);

    const list = document.createElement('div');
    list.className = 'zf-comment-list';
    section.appendChild(list);

    let allComments = [...(json.data || [])];
    allComments.forEach((c, idx) => {
      if (c._origIdx === undefined) c._origIdx = idx;
    });

    let currentSort = 'default';

    sortBar.querySelectorAll('.zf-sort-btn').forEach(btn => {
      btn.onclick = () => {
        sortBar.querySelectorAll('.zf-sort-btn').forEach(b => b.classList.remove('active'));
        btn.classList.add('active');
        currentSort = btn.dataset.sort;
        list.innerHTML = '';
        renderGroupedComments(allComments, list, currentSort);
      };
    });

    renderGroupedComments(allComments, list, currentSort);

    if (json.paging?.is_end === false) {
      const moreBtn = document.createElement('button');
      moreBtn.className = 'zf-load-more-comments';
      let nextOffset = startOffset + allComments.length;
      const renderMore = (t) => t ? `加载更多评论（已显示 ${nextOffset}/${t} 条）` : '加载更多评论';
      moreBtn.textContent = renderMore(json.paging?.totals);
      
      moreBtn.onclick = async () => {
        moreBtn.textContent = '⏳ 加载中...'; moreBtn.disabled = true;
        try {
          const nextJson = await loadComments(answerId, nextOffset);
          const newBatch = nextJson.data || [];
          newBatch.forEach((c, idx) => {
            if (c._origIdx === undefined) c._origIdx = allComments.length + idx;
          });
          allComments.push(...newBatch);
          list.innerHTML = '';
          renderGroupedComments(allComments, list, currentSort);
          nextOffset += newBatch.length;
          if (nextJson.paging?.is_end !== false) {
            moreBtn.remove();
          } else {
            moreBtn.textContent = renderMore(nextJson.paging?.totals);
            moreBtn.disabled = false;
          }
        } catch (e) {
          moreBtn.textContent = '❌ 加载失败，点击重试'; moreBtn.disabled = false;
        }
      };
      section.appendChild(moreBtn);
    }
    return section;
  }

  function buildCommentItem(c, isChild) {
    const item = document.createElement('div');
    item.className = isChild ? 'zf-comment-item zf-comment-child' : 'zf-comment-item';

    const authorObj  = c.author;
    const isAnon     = !authorObj || authorObj.role === 'anonymous';
    const authorName = isAnon ? '匿名用户' : (authorObj.member?.name || authorObj.name || '知乎用户');
    const urlToken   = isAnon ? null : (authorObj.member?.url_token || authorObj.url_token || authorObj.member?.id || authorObj.id);
    const authorUrl  = urlToken && urlToken !== 'people' ? `https://www.zhihu.com/people/${urlToken}` : null;

    if (!isAnon && !authorUrl) {
      if (!debugFailedAuthors.some(x => x.name === authorName)) {
        debugFailedAuthors.push({
          id: c.id,
          name: authorName,
          rawAuthor: authorObj
        });
      }
    }

    const time  = c.created_time ? new Date(c.created_time * 1000).toLocaleString('zh-CN') : '?';
    const votes = c.vote_count ?? c.voteup_count ?? c.up_count ?? 0;

    const replyAuthorObj = c.reply_to_author;
    const rName = replyAuthorObj?.member?.name
      || (replyAuthorObj?.role === 'anonymous' ? '匿名用户' : null)
      || replyAuthorObj?.name
      || null;
    const rUrlToken = replyAuthorObj?.member?.url_token || replyAuthorObj?.url_token || replyAuthorObj?.member?.id || replyAuthorObj?.id;
    const rUrl = rUrlToken && rUrlToken !== 'people' ? `https://www.zhihu.com/people/${rUrlToken}` : null;

    let replyTag = '';
    if (rName) {
      if (rUrl) {
        replyTag = `<span class="zf-reply-tag">回复 <a class="zf-reply-name" href="${rUrl}" target="_blank" rel="noopener">${rName}</a></span> `;
      } else {
        replyTag = `<span class="zf-reply-tag">回复 <span class="zf-reply-name">${rName}</span></span> `;
      }
    }

    const content    = c.content ?? '';

    item.innerHTML = `
      <div class="zf-comment-meta">
        ${authorUrl
          ? `<a class="zf-comment-author" href="${authorUrl}" target="_blank" rel="noopener">${authorName}</a>`
          : `<span class="zf-comment-author zf-author-anon">${authorName}</span>`
        }
        <span class="zf-comment-time">${time}</span>
        ${votes > 0 ? `<span class="zf-comment-vote">👍 ${votes}</span>` : ''}
      </div>
      <div class="zf-comment-content"></div>
    `;

    const contentDiv = item.querySelector('.zf-comment-content');
    if (contentDiv) {
      contentDiv.innerHTML = replyTag + content;
      // 对于裸露的 img 图片元素，外层包裹支持新标签页打开的 a 链接
      contentDiv.querySelectorAll('img').forEach(img => {
        const src = img.dataset.actualsrc || img.dataset.src || img.src;
        if (src) {
          const parentA = img.closest('a');
          if (parentA) {
            parentA.target = '_blank';
            parentA.rel = 'noopener noreferrer';
          } else {
            const link = document.createElement('a');
            link.href = src;
            link.target = '_blank';
            link.rel = 'noopener noreferrer';
            img.parentNode.insertBefore(link, img);
            link.appendChild(img);
          }
        }
      });
      // 确保评论内容区所有的链接都在新标签页打开
      contentDiv.querySelectorAll('a').forEach(a => {
        a.target = '_blank';
        a.rel = 'noopener noreferrer';
      });
    }

    return item;
  }


  // ═══════════════════════════════════════════════════════════
  // § 8. CSS
  // ═══════════════════════════════════════════════════════════
  GM_addStyle(`
    #zf-panel {
      position: fixed; top: 80px; right: 14px; z-index: 99999;
      width: 236px; background: #12122a;
      border: 1px solid #3a3a7a; border-radius: 12px; padding: 14px 12px;
      font-family: -apple-system, BlinkMacSystemFont, 'PingFang SC', 'Segoe UI', sans-serif;
      font-size: 13px; color: #dde0ff;
      box-shadow: 0 6px 32px rgba(60,60,180,0.45);
      user-select: none;
    }
    #zf-panel.zf-collapsed #zf-body { display: none; }
    #zf-panel h3 {
      margin: 0 0 10px; font-size: 13px; color: #9090ee;
      text-align: center; letter-spacing: 1px;
      border-bottom: 1px solid #2a2a5a; padding-bottom: 8px;
      cursor: pointer; display: flex; align-items: center; justify-content: center; gap: 6px;
    }
    #zf-panel h3:hover { color: #b0b0ff; }
    #zf-panel button {
      display: block; width: 100%; margin: 5px 0; padding: 8px 0;
      border: none; border-radius: 7px; cursor: pointer;
      font-size: 12px; font-weight: 600; letter-spacing: .3px;
      transition: filter .15s, transform .1s;
    }
    #zf-panel button:hover:not(:disabled) { filter: brightness(1.18); transform: translateY(-1px); }
    #zf-panel button:active:not(:disabled) { transform: translateY(0); }
    #zf-panel button:disabled { opacity: .38; cursor: not-allowed; }
    #zf-btn-fetch   { background: linear-gradient(135deg,#4f46e5,#7c3aed); color:#fff; }
    #zf-btn-stop    { background: #b91c1c; color:#fff; margin-top:2px; }
    #zf-btn-votes   { background: #0284c7; color:#fff; }
    #zf-btn-newest  { background: #059669; color:#fff; }
    #zf-btn-oldest  { background: #7c3aed; color:#fff; }
    #zf-btn-restore { background: #9f1239; color:#fff; }
    #zf-btn-debug   { background: #1e293b; color:#64748b; font-size:11px; padding:5px 0; margin-top:8px; }
    .zf-row { display:flex; align-items:center; gap:6px; margin:6px 0; }
    .zf-row label { font-size:11px; color:#7777bb; white-space:nowrap; }
    .zf-row input[type=number] {
      width:60px; padding:3px 6px;
      background:#1e1e40; border:1px solid #3a3a7a;
      border-radius:5px; color:#dde0ff; font-size:12px;
    }
    #zf-progress { margin:6px 0 2px; height:4px; background:#252550; border-radius:2px; overflow:hidden; }
    #zf-progress-bar {
      height:100%; background:linear-gradient(90deg,#4f46e5,#06b6d4);
      width:0; transition:width .4s ease; border-radius:2px;
    }
    #zf-status {
      margin-top:8px; font-size:11px; color:#7777bb;
      word-break:break-all; min-height:32px; line-height:1.6; text-align:center;
    }
    #zf-status small { font-size:10px; color:#44446a; }
    #zf-count { text-align:center; font-size:12px; color:#60a5fa; font-weight:bold; margin:4px 0; }
    .zf-divider { border:none; border-top:1px solid #2a2a5a; margin:8px 0; }

    /* ── 调试弹层 ── */
    #zf-debug-overlay {
      position:fixed; top:50%; left:50%; transform:translate(-50%,-50%);
      z-index:100000; background:#0f172a; border:1px solid #334155;
      border-radius:12px; padding:20px 22px; width:640px;
      max-height:78vh; overflow-y:auto;
      font-family:'Courier New',monospace; font-size:12px; color:#94a3b8;
      box-shadow:0 12px 48px rgba(0,0,0,.8);
    }
    #zf-debug-overlay h4 { color:#60a5fa; margin:0 0 14px; font-size:14px; }
    .dbg-sec { margin-bottom:14px; }
    .dbg-lbl { color:#f59e0b; margin-bottom:4px; font-weight:bold; font-size:11px; text-transform:uppercase; }
    #zf-debug-overlay pre {
      background:#1e293b; border-radius:6px; padding:10px;
      white-space:pre-wrap; word-break:break-all;
      max-height:180px; overflow-y:auto; color:#a3e635; margin:0; font-size:11px;
    }
    #zf-debug-close { position:absolute; top:12px; right:16px; cursor:pointer; background:none; border:none; color:#ef4444; font-size:22px; }

    /* ── 图片占位 ── */
    .zf-img-ph {
      display:inline-flex; align-items:center; gap:5px;
      margin:4px 0; padding:6px 12px;
      background:#f1f5f9; border:1px dashed #94a3b8; border-radius:6px;
      color:#64748b; cursor:pointer; font-size:12px;
      transition:background .15s;
    }
    .zf-img-ph:hover:not(:disabled) { background:#e2e8f0; color:#334155; }
    .zf-img-ph:disabled { opacity:.55; cursor:not-allowed; }
    .zf-img-loaded { max-width:100%; height:auto; border-radius:4px; display:block; margin:4px 0; }

    /* ── 结果区域 ── */
    #zf-result { margin:16px auto; max-width:1000px; padding:0 16px; }
    .zf-result-header {
      display:flex; align-items:center; justify-content:space-between;
      padding:12px 0; font-size:15px; font-weight:bold;
      color:#333; border-bottom:2px solid #e8e8e8; margin-bottom:14px;
    }
    .zf-img-toggle {
      flex-shrink:0; padding:5px 12px;
      background:#f1f5f9; border:1px solid #e2e8f0; border-radius:6px;
      cursor:pointer; font-size:12px; color:#475569; font-weight:500;
      transition:all .15s;
    }
    .zf-img-toggle:hover { background:#e2e8f0; color:#1e293b; }
    .zf-img-toggle.active { background:#4f46e5; color:#fff; border-color:#4f46e5; }
    .zf-answer-card {
      border:1px solid #e4e4e4; border-radius:10px;
      padding:14px 18px; margin-bottom:14px;
      background:#fff; box-shadow:0 1px 5px rgba(0,0,0,.06);
      transition:box-shadow .2s;
    }
    .zf-answer-card:hover { box-shadow:0 3px 14px rgba(0,0,0,.1); }
    .zf-answer-meta { display:flex; gap:10px; align-items:center; margin-bottom:10px; font-size:13px; flex-wrap:wrap; }
    .zf-rank { color:#ccc; font-size:11px; }
    .zf-vote-badge { background:#eff6ff; color:#1d4ed8; border-radius:5px; padding:2px 9px; font-weight:bold; font-size:12px; }
    .zf-time-badge { color:#999; font-size:12px; }
    .zf-author { font-weight:bold; color:#111; text-decoration:none; }
    .zf-author:hover { text-decoration:underline; color:#4f46e5; }
    .zf-answer-content { font-size:14px; color:#333; line-height:1.8; overflow:hidden; }
    .zf-answer-content.collapsed {
      max-height:160px;
      -webkit-mask-image:linear-gradient(to bottom,black 50%,transparent 100%);
      mask-image:linear-gradient(to bottom,black 50%,transparent 100%);
    }
    .zf-answer-content img { max-width:100%; height:auto; border-radius:4px; }
    .zf-card-actions { display:flex; gap:8px; margin-top:10px; flex-wrap:wrap; align-items:center; }
    .zf-expand-btn, .zf-comment-btn {
      cursor:pointer; font-size:12px; background:none; border:none; padding:3px 8px;
      border-radius:4px; transition:background .15s, color .15s;
    }
    .zf-expand-btn { color:#4f46e5; }
    .zf-expand-btn:hover { background:#eef2ff; }
    .zf-comment-btn { color:#6b7280; border:1px solid #e5e7eb; }
    .zf-comment-btn:hover:not(:disabled) { color:#4f46e5; border-color:#c7d2fe; background:#eef2ff; }
    .zf-comment-btn:disabled { opacity:.5; cursor:not-allowed; }

    /* ── 评论区 ── */
    .zf-comment-section {
      margin-top: 12px; border-top: 1px solid #f0f0f0; padding-top: 10px;
    }
    .zf-comment-sort-bar {
      display: flex; align-items: center; gap: 4px;
      margin-bottom: 10px; padding-bottom: 8px;
      border-bottom: 1px solid #f2f2f7;
      font-size: 11px;
    }
    .zf-sort-label { color: #8e8e93; font-weight: 500; margin-right: 4px; }
    .zf-sort-btn {
      background: #f2f2f7; border: none; padding: 3px 8px;
      border-radius: 5px; color: #8e8e93; cursor: pointer;
      font-size: 11px; transition: all .15s; font-weight: 500;
    }
    .zf-sort-btn:hover { background: #e5e5ea; color: #3a3a3c; }
    .zf-sort-btn.active { background: #7c3aed; color: #fff; font-weight: bold; }
    .zf-comment-list { display:flex; flex-direction:column; }
    .zf-comment-item { padding:9px 0; border-bottom:1px solid #f5f5f5; }
    .zf-comment-item:last-child { border-bottom:none; }
    /* 子评论（回复）：左侧竖线缩进 */
    .zf-comment-child {
      margin: 2px 0 2px 18px;
      padding: 7px 0 7px 12px;
      border-left: 2px solid #e0e7ff;
      border-bottom: none;
      background: #fafbff;
      border-radius: 0 4px 4px 0;
    }
    .zf-replies-box {
      margin-top: 6px;
      display: flex; flex-direction: column;
    }
    /* 展开回复按钮 */
    .zf-expand-replies {
      display: inline-block; margin-top:5px;
      padding:2px 8px; background:none;
      border:1px solid #e0e7ff; border-radius:4px;
      font-size:12px; color:#6366f1; cursor:pointer;
      transition:background .15s;
    }
    .zf-expand-replies:hover:not(:disabled) { background:#eef2ff; }
    .zf-expand-replies:disabled { opacity:.5; cursor:not-allowed; }
    /* 加载更多回复（在子评论框内） */
    .zf-load-more-replies {
      margin-left:18px; margin-top:4px; padding:4px 10px;
      background:none; border:1px dashed #d1d5db; border-radius:4px;
      font-size:12px; color:#9ca3af; cursor:pointer;
    }
    .zf-load-more-replies:hover:not(:disabled) { color:#6b7280; border-color:#9ca3af; }
    .zf-load-more-replies:disabled { opacity:.5; }
    .zf-comment-meta { display:flex; gap:8px; align-items:center; margin-bottom:3px; flex-wrap:wrap; }
    .zf-comment-author { font-size:12px; font-weight:600; color:#374151; text-decoration:none; }
    .zf-comment-author:hover { color:#4f46e5; text-decoration:underline; }
    .zf-author-anon { font-size:12px; font-weight:500; color:#9ca3af; font-style:italic; }
    .zf-comment-time { font-size:11px; color:#9ca3af; }
    .zf-comment-vote { font-size:11px; color:#60a5fa; }
    .zf-comment-content { font-size:13px; color:#4b5563; line-height:1.65; }
    /* 回复标签：「回复 @xxx」 */
    .zf-reply-tag { font-size:12px; color:#9ca3af; margin-right:4px; }
    .zf-reply-name { color:#6366f1; font-weight:500; text-decoration:none; }
    .zf-reply-name:hover { text-decoration:underline; }
    .zf-load-more-comments {
      display:block; width:100%; margin-top:8px; padding:7px;
      background:#f9fafb; border:1px dashed #d1d5db; border-radius:6px;
      cursor:pointer; font-size:12px; color:#6b7280; transition:background .15s;
    }
    .zf-load-more-comments:hover:not(:disabled) { background:#f0f0f0; color:#374151; }
    .zf-load-more-comments:disabled { opacity:.5; cursor:not-allowed; }

    /* ── 分页 ── */
    .zf-pagination { display:flex; align-items:center; justify-content:center; gap:6px; padding:14px 0; flex-wrap:wrap; border-top:1px solid #f0f0f0; margin-top:10px; }
    .zf-pagination button { padding:5px 12px; border:1px solid #d1d5db; border-radius:5px; background:#fff; color:#374151; cursor:pointer; font-size:13px; transition:background .15s; }
    .zf-pagination button:hover:not(:disabled) { background:#f3f4f6; }
    .zf-pagination button.active { background:#4f46e5; color:#fff; border-color:#4f46e5; }
    .zf-pagination button:disabled { opacity:.4; cursor:not-allowed; }
    .zf-pg-info { font-size:13px; color:#666; white-space:nowrap; }
    .zf-pagination input[type=number] { width:50px; padding:4px 6px; border:1px solid #d1d5db; border-radius:5px; font-size:13px; text-align:center; }
    .zf-pg-jump-btn { padding:5px 10px; background:#4f46e5; color:#fff; border:none; border-radius:5px; cursor:pointer; font-size:12px; }

    /* ── 评论弹窗浮层 ── */
    .zf-modal-mask {
      position: fixed; top: 0; left: 0; right: 0; bottom: 0;
      z-index: 100000; background: rgba(15, 23, 42, 0.45);
      backdrop-filter: blur(8px);
      display: flex; align-items: center; justify-content: center;
      animation: zf-fade-in 0.2s ease-out;
    }
    .zf-modal-container {
      width: 680px; max-width: 90vw; height: 80vh; max-height: 85vh;
      background: #fff; border-radius: 16px;
      box-shadow: 0 20px 25px -5px rgba(0, 0, 0, 0.1), 0 10px 10px -5px rgba(0, 0, 0, 0.04);
      display: flex; flex-direction: column;
      overflow: hidden; border: 1px solid #e2e8f0;
      animation: zf-scale-up 0.25s cubic-bezier(0.34, 1.56, 0.64, 1);
    }
    @keyframes zf-fade-in {
      from { opacity: 0; }
      to { opacity: 1; }
    }
    @keyframes zf-scale-up {
      from { transform: scale(0.95); opacity: 0; }
      to { transform: scale(1); opacity: 1; }
    }
    .zf-modal-header {
      padding: 16px 20px; border-bottom: 1px solid #f1f5f9;
      display: flex; align-items: center; justify-content: space-between;
      background: #f8fafc;
    }
    .zf-modal-title {
      font-size: 15px; font-weight: 700; color: #0f172a;
    }
    .zf-modal-close-btn {
      background: none; border: none; font-size: 24px; color: #94a3b8;
      cursor: pointer; transition: color 0.15s; padding: 0 4px; line-height: 1;
    }
    .zf-modal-close-btn:hover { color: #ef4444; }
    .zf-modal-body {
      flex: 1; overflow-y: auto; padding: 0 20px 20px;
    }

    /* ── Light Theme 配色 ── */
    #zf-panel.zf-theme-light {
      background: #ffffff;
      border: 1px solid #cbd5e1;
      color: #1e293b;
      box-shadow: 0 10px 25px -5px rgba(0, 0, 0, 0.1), 0 8px 10px -6px rgba(0, 0, 0, 0.05);
    }
    #zf-panel.zf-theme-light h3 {
      color: #4f46e5;
      border-bottom: 1px solid #e2e8f0;
    }
    #zf-panel.zf-theme-light h3:hover {
      color: #6366f1;
    }
    #zf-panel.zf-theme-light .zf-row label {
      color: #475569;
    }
    #zf-panel.zf-theme-light .zf-row input[type=number] {
      background: #f8fafc;
      border: 1px solid #cbd5e1;
      color: #0f172a;
    }
    #zf-panel.zf-theme-light #zf-progress {
      background: #e2e8f0;
    }
    #zf-panel.zf-theme-light #zf-status {
      color: #475569;
    }
    #zf-panel.zf-theme-light #zf-status small {
      color: #64748b;
    }
    #zf-panel.zf-theme-light #zf-count {
      color: #2563eb;
    }
    #zf-panel.zf-theme-light #zf-btn-debug {
      background: #f8fafc;
      color: #64748b;
      border: 1px solid #e2e8f0;
    }
    #zf-panel.zf-theme-light #zf-btn-donate {
      background: #fef3c7;
      color: #b45309;
      border: 1px solid #fde68a;
    }
    #zf-theme-toggle:hover {
      transform: scale(1.2);
    }
  `);


  // ═══════════════════════════════════════════════════════════
  // § 9. 控制面板与主题切换
  // ═══════════════════════════════════════════════════════════
  let currentTheme = localStorage.getItem('zf-theme') || 'dark';

  function applyTheme() {
    const el = document.getElementById('zf-panel');
    if (!el) return;
    const toggleBtn = document.getElementById('zf-theme-toggle');
    if (currentTheme === 'light') {
      el.classList.add('zf-theme-light');
      if (toggleBtn) toggleBtn.textContent = '🌙';
    } else {
      el.classList.remove('zf-theme-light');
      if (toggleBtn) toggleBtn.textContent = '☀️';
    }
  }

  function toggleTheme() {
    currentTheme = currentTheme === 'light' ? 'dark' : 'light';
    localStorage.setItem('zf-theme', currentTheme);
    applyTheme();
  }

  function injectPanel() {
    if (document.getElementById('zf-panel')) return;
    const el = document.createElement('div');
    el.id = 'zf-panel';
    el.innerHTML = `
      <h3 id="zf-title">
        <span style="display: flex; align-items: center; gap: 4px;">📦 知乎回答抓取 v1.0.0</span>
        <div style="display: flex; align-items: center; gap: 8px;">
          <span id="zf-theme-toggle" style="cursor: pointer; font-size: 12px; transition: transform 0.2s;" title="切换配色">☀️</span>
          <span id="zf-collapse-indicator">▾</span>
        </div>
      </h3>
      <div id="zf-body">
        <button id="zf-btn-fetch">⬇ 获取所有回答</button>
        <hr class="zf-divider">
        <button id="zf-btn-votes"   disabled>👍 按赞同数排序</button>
        <button id="zf-btn-newest"  disabled>🕐 按时间倒序</button>
        <button id="zf-btn-oldest"  disabled>🕑 按时间正序</button>
        <div class="zf-row">
          <label>每页条数</label>
          <input id="zf-per-page" type="number" value="50" min="10" max="500">
        </div>
        <button id="zf-btn-restore" disabled>♻ 恢复原始页面</button>
        <div id="zf-progress"><div id="zf-progress-bar"></div></div>
        <div id="zf-count"></div>
        <div id="zf-status">⏳ 准备就绪<br><small>点击「获取所有回答」开始<br>支持切换到其他标签页</small></div>
        <div style="display: flex; gap: 8px;">
          <button id="zf-btn-debug" style="flex: 1; margin: 0;">🔍 调试信息</button>
          <button id="zf-btn-donate" style="flex: 1; margin: 0; background: #b45309; color: #fff;">☕ 赞助支持</button>
        </div>
      </div>
    `;
    document.body.appendChild(el);

    // Apply initial theme
    applyTheme();

    const themeToggle = document.getElementById('zf-theme-toggle');
    if (themeToggle) {
      themeToggle.onclick = (e) => {
        e.stopPropagation();
        toggleTheme();
      };
    }

    // Make panel draggable
    let isDragging = false;
    let hasMoved = false;
    let startX = 0, startY = 0;
    let initialLeft = 0, initialTop = 0;
    const titleEl = document.getElementById('zf-title');

    // Load persisted position if any
    const savedLeft = localStorage.getItem('zf-panel-left');
    const savedTop = localStorage.getItem('zf-panel-top');
    if (savedLeft !== null && savedTop !== null) {
      el.style.left = savedLeft;
      el.style.top = savedTop;
      el.style.right = 'auto';
    }

    titleEl.style.cursor = 'move';
    titleEl.addEventListener('mousedown', (e) => {
      // Only drag with left click, and do not drag if clicked the theme toggle
      if (e.button !== 0 || e.target === themeToggle) return;
      
      const rect = el.getBoundingClientRect();
      initialLeft = rect.left;
      initialTop = rect.top;
      startX = e.clientX;
      startY = e.clientY;
      isDragging = true;
      hasMoved = false;
      document.addEventListener('mousemove', onMouseMove);
      document.addEventListener('mouseup', onMouseUp);
      e.preventDefault(); // Prevent text selection
    });

    function onMouseMove(e) {
      if (!isDragging) return;
      const dx = e.clientX - startX;
      const dy = e.clientY - startY;
      if (Math.abs(dx) > 3 || Math.abs(dy) > 3) {
        hasMoved = true;
      }
      let newLeft = initialLeft + dx;
      let newTop = initialTop + dy;
      
      const viewportWidth = window.innerWidth;
      const viewportHeight = window.innerHeight;
      const panelWidth = el.offsetWidth;
      const panelHeight = el.offsetHeight;
      
      if (newLeft < 0) newLeft = 0;
      if (newLeft + panelWidth > viewportWidth) newLeft = viewportWidth - panelWidth;
      if (newTop < 0) newTop = 0;
      if (newTop + panelHeight > viewportHeight) newTop = viewportHeight - panelHeight;
      
      el.style.left = newLeft + 'px';
      el.style.top = newTop + 'px';
      el.style.right = 'auto';
    }

    function onMouseUp() {
      if (isDragging) {
        isDragging = false;
        document.removeEventListener('mousemove', onMouseMove);
        document.removeEventListener('mouseup', onMouseUp);
        localStorage.setItem('zf-panel-left', el.style.left);
        localStorage.setItem('zf-panel-top', el.style.top);
      }
    }

    titleEl.addEventListener('click', (e) => {
      // If we dragged, or if we clicked the theme toggle, don't collapse/expand
      if (hasMoved || e.target === themeToggle) {
        e.preventDefault();
        e.stopPropagation();
        return;
      }
      el.classList.toggle('zf-collapsed');
    });

    document.getElementById('zf-btn-fetch').onclick  = onFetchAll;
    document.getElementById('zf-btn-votes').onclick  = () => sortAndRender('votes');
    document.getElementById('zf-btn-newest').onclick = () => sortAndRender('newest');
    document.getElementById('zf-btn-oldest').onclick = () => sortAndRender('oldest');
    document.getElementById('zf-btn-restore').onclick= onRestore;
    document.getElementById('zf-btn-debug').onclick  = showDebug;
    document.getElementById('zf-btn-donate').onclick = showDonate;
  }

  function addStopButton() {
    if (document.getElementById('zf-btn-stop')) return;
    const btn = document.createElement('button');
    btn.id = 'zf-btn-stop'; btn.textContent = '⛔ 停止抓取'; btn.onclick = onStopFetch;
    document.getElementById('zf-btn-fetch')?.insertAdjacentElement('afterend', btn);
  }

  // ═══════════════════════════════════════════════════════════
  // § 7. 渲染与面板更新
  // ═══════════════════════════════════════════════════════════
  function updateStatus(t) { const el = document.getElementById('zf-status'); if (el) el.innerHTML = t; }
  function updateCount(n) {
    const el = document.getElementById('zf-count');
    if (el) el.textContent = n > 0 ? `已截获 ${n} 条` : '';
    const bar = document.getElementById('zf-progress-bar');
    if (bar) bar.style.width = Math.min(100, (n / 1000) * 100) + '%';
  }
  function setSortEnabled(on) {
    ['zf-btn-votes','zf-btn-newest','zf-btn-oldest','zf-btn-restore'].forEach(id => {
      const b = document.getElementById(id); if (b) b.disabled = !on;
    });
  }


  // ═══════════════════════════════════════════════════════════
  // § 10. 调试面板
  // ═══════════════════════════════════════════════════════════
  function showDebug() {
    document.getElementById('zf-debug-overlay')?.remove();

    // 重复数据统计与分析
    const idCounts = {};
    rawAnswers.forEach(a => {
      const id = a.id ?? a.answer_id;
      if (id != null) {
        idCounts[id] = (idCounts[id] || 0) + 1;
      }
    });
    const dupCount = rawAnswers.length - allAnswers.length;
    const sortedDups = Object.entries(idCounts)
      .filter(([_, count]) => count > 1)
      .map(([id, count]) => {
        const found = rawAnswers.find(x => String(x.id ?? x.answer_id) === id);
        return { id, count, author: found?.author?.name ?? '匿名用户' };
      })
      .sort((a, b) => b.count - a.count);

    const topDupsStr = sortedDups.slice(0, 5)
      .map(d => `  - ${d.author} (ID: ${d.id}): 重复出现 ${d.count} 次`)
      .join('\n');

    const first = rawAnswers[0];
    const firstStr = first
      ? `字段: ${Object.keys(first).join(', ')}\n\nvoteup_count  = ${first.voteup_count}\ncreated_time  = ${first.created_time}\nauthor.name   = ${first.author?.name}\ncomment_count = ${first.comment_count}\ncontent.len   = ${first.content?.length ?? 'N/A'}\n\nJSON（前600字）:\n${JSON.stringify(first).slice(0, 600)}`
      : '（尚未抓取数据）';
    const ov = document.createElement('div');
    ov.id = 'zf-debug-overlay';
    ov.innerHTML = `
      <button id="zf-debug-close">✕</button>
      <h4>🔍 ZhihuFetcher v0.9 调试面板</h4>
      <div class="dbg-sec">
        <div class="dbg-lbl">Hook 状态</div>
        <pre>fetch hook:    ${!!unsafeWindow.__ZF_FETCH_HOOKED__}
IO hook:       ${!!unsafeWindow.__ZF_IO_HOOKED__}  (${ioTrackers.length} 个 observer)
capturedHdrs:  ${capturedHdrs ? '✅ 已捕获 ' + Object.keys(capturedHdrs).length + ' 个 Header' : '❌ 未捕获'}
feedsNextUrl:  ${feedsNextUrl ? '✅ ' + feedsNextUrl.slice(0,70) : '❌ 无'}
answersOffset: ${answersOffset}  answersDone=${answersDone}  apiFailed=${answersApiFailed}</pre>
      </div>
      <div class="dbg-sec">
        <div class="dbg-lbl">抓取统计</div>
        <pre>rawAnswers  = ${rawAnswers.length} 条
allAnswers  = ${allAnswers.length} 条（去重后）
直连成功    = ${cntDirect} 次
IO触发成功  = ${cntIO} 次
页面可见    = ${!document.hidden}</pre>
      </div>
      <div class="dbg-sec">
        <div class="dbg-lbl">重复数据分析</div>
        <pre>重复数据总数: ${dupCount} 条 (占比 ${rawAnswers.length ? ((dupCount / rawAnswers.length) * 100).toFixed(1) : 0}%)
Top 5 重复出现的回答:
${topDupsStr || '  (暂无重复回答)'}</pre>
      </div>
      <div class="dbg-sec">
        <div class="dbg-lbl">第1条数据分析</div>
        <pre>${firstStr}</pre>
      </div>
      <div class="dbg-sec">
        <div class="dbg-lbl">链接解析失败的评论作者（前20条）</div>
        <pre style="max-height:250px;overflow-y:auto;">${debugFailedAuthors.length > 0 ? JSON.stringify(debugFailedAuthors, null, 2) : '（暂无数据）'}</pre>
      </div>
    `;
    document.body.appendChild(ov);
    document.getElementById('zf-debug-close').onclick = () => ov.remove();
  }

  // ═══════════════════════════════════════════════════════════
  // § 10.5 赞助支持面板
  // ═══════════════════════════════════════════════════════════
  function showDonate() {
    document.getElementById('zf-donate-overlay')?.remove();

    const isLight = currentTheme === 'light';
    const bg = isLight ? '#ffffff' : '#1e1b4b';
    const color = isLight ? '#1e293b' : '#dde0ff';
    const subColor = isLight ? '#64748b' : '#8e8e93';
    const border = isLight ? '1px solid #cbd5e1' : '1px solid #3a3a7a';

    const ov = document.createElement('div');
    ov.id = 'zf-donate-overlay';
    ov.style.cssText = `
      position: fixed; top: 0; left: 0; width: 100%; height: 100%;
      background: rgba(15, 23, 42, 0.45); backdrop-filter: blur(8px);
      display: flex; align-items: center; justify-content: center;
      z-index: 1000002; font-family: -apple-system, BlinkMacSystemFont, 'PingFang SC', 'Segoe UI', sans-serif;
      animation: zf-fade-in 0.2s ease-out;
    `;

    ov.innerHTML = `
      <div style="background: ${bg}; color: ${color}; border: ${border}; border-radius: 16px; width: 480px; max-width: 95vw; padding: 24px; box-shadow: 0 20px 25px -5px rgba(0, 0, 0, 0.1), 0 10px 10px -5px rgba(0, 0, 0, 0.04); position: relative; animation: zf-scale-up 0.25s cubic-bezier(0.34, 1.56, 0.64, 1);">
        <button id="zf-donate-close" style="position: absolute; top: 12px; right: 16px; cursor: pointer; background: none; border: none; color: #ef4444; font-size: 24px; line-height: 1; padding: 0;">✕</button>
        <h4 style="margin: 0 0 12px; font-size: 16px; text-align: center; font-weight: bold; color: ${isLight ? '#4f46e5' : '#60a5fa'};">☕ 赞助支持</h4>
        <p style="margin: 0 0 20px; font-size: 13px; color: ${subColor}; text-align: center; line-height: 1.6; padding: 0 8px;">
          如果您觉得「知乎小助手」对您有所帮助，欢迎请作者喝杯咖啡！您的支持是持续优化与维护的动力。
        </p>
        
        <div style="display: flex; gap: 20px; justify-content: center; flex-wrap: wrap;">
          <!-- 微信支付 -->
          <div style="text-align: center; flex: 1; min-width: 180px;">
            <div style="font-weight: 600; font-size: 13px; color: #10b981; margin-bottom: 8px; display: flex; align-items: center; justify-content: center; gap: 4px;">
              <span style="font-size: 14px;">💬</span> 微信扫码
            </div>
            <div style="width: 200px; height: 200px; border-radius: 8px; border: ${WECHAT_QR ? '1px solid #10b981' : '1px dashed #10b981'}; background: ${isLight ? '#f0fdf4' : '#064e3b'}; display: flex; align-items: center; justify-content: center; margin: 0 auto; overflow: hidden; position: relative;">
              ${WECHAT_QR 
                ? `<img src="${WECHAT_QR}" style="width: 100%; height: 100%; object-fit: contain; transform: scale(1.35); transform-origin: center; image-rendering: -webkit-optimize-contrast; image-rendering: crisp-edges; image-rendering: pixelated;">`
                : `<div style="font-size: 11px; color: #10b981; padding: 12px; line-height: 1.4; text-align: center;">未配置微信收款码</div>`
              }
            </div>
          </div>

          <!-- 支付宝 -->
          <div style="text-align: center; flex: 1; min-width: 180px;">
            <div style="font-weight: 600; font-size: 13px; color: #0284c7; margin-bottom: 8px; display: flex; align-items: center; justify-content: center; gap: 4px;">
              <span style="font-size: 14px;">💳</span> 支付宝扫码
            </div>
            <div style="width: 200px; height: 200px; border-radius: 8px; border: ${ALIPAY_QR ? '1px solid #0284c7' : '1px dashed #0284c7'}; background: ${isLight ? '#f0f9ff' : '#0c4a6e'}; display: flex; align-items: center; justify-content: center; margin: 0 auto; overflow: hidden; position: relative;">
              ${ALIPAY_QR 
                ? `<img src="${ALIPAY_QR}" style="width: 100%; height: 100%; object-fit: contain; transform: scale(1.35); transform-origin: center; image-rendering: -webkit-optimize-contrast; image-rendering: crisp-edges; image-rendering: pixelated;">`
                : `<div style="font-size: 11px; color: #0284c7; padding: 12px; line-height: 1.4; text-align: center;">未配置支付宝码</div>`
              }
            </div>
          </div>
        </div>
      </div>
    `;

    document.body.appendChild(ov);
    document.getElementById('zf-donate-close').onclick = () => ov.remove();
    ov.onclick = (e) => { if (e.target === ov) ov.remove(); };
  }


  // ═══════════════════════════════════════════════════════════
  // § 11. 排序与分页渲染
  // ═══════════════════════════════════════════════════════════
  function sortAndRender(mode) {
    if (!allAnswers.length) { updateStatus('❌ 请先获取回答'); return; }
    const sorted = [...allAnswers];
    if (mode === 'votes')  sorted.sort((a, b) => (b.voteup_count || 0) - (a.voteup_count || 0));
    if (mode === 'newest') sorted.sort((a, b) => (b.created_time || 0) - (a.created_time || 0));
    if (mode === 'oldest') sorted.sort((a, b) => (a.created_time || 0) - (b.created_time || 0));
    currentSorted = sorted; currentPage = 1;
    itemsPerPage  = Math.max(10, parseInt(document.getElementById('zf-per-page')?.value || '50', 10));
    const labels = { votes:'👍 赞同数降序', newest:'🕐 时间倒序', oldest:'🕑 时间正序' };
    initResultContainer(labels[mode]);
    renderPage(1);
  }

  function initResultContainer(modeLabel) {
    const SELS = ['.QuestionAnswer-content', '.Question-mainColumn .List', '.Question-mainColumn > div'];
    if (!origContainer) {
      for (const s of SELS) { const e = document.querySelector(s); if (e) { origContainer = e; break; } }
    }
    if (origContainer) origContainer.style.display = 'none';

    // 隐藏右侧边栏（广告、热搜等）并拉伸左侧主内容区，提供更宽敞的阅读空间
    if (!origSidebar) {
      origSidebar = document.querySelector('.Question-sideColumn, .Question-sidebar, div[class*="sideColumn"]');
    }
    if (origSidebar) {
      origSidebarDisplay = origSidebar.style.display;
      origSidebar.style.display = 'none';
    }
    if (!origMainCol) {
      origMainCol = document.querySelector('.Question-mainColumn, div[class*="mainColumn"]');
    }
    if (origMainCol) {
      origMainColWidth = origMainCol.style.width;
      origMainColMaxWidth = origMainCol.style.maxWidth;
      origMainCol.style.width = '100%';
      origMainCol.style.maxWidth = 'none';
    }

    resultEl?.remove();
    resultEl = document.createElement('div');
    resultEl.id = 'zf-result';
    resultEl.innerHTML = `
      <div class="zf-result-header">
        <span>📦 脚本渲染（${modeLabel}）—— 共 ${currentSorted.length} 条 | 每页 ${itemsPerPage} 条</span>
        <button id="zf-img-toggle" class="zf-img-toggle">${showImages ? '🖼 隐藏图片' : '🖼 显示图片'}</button>
      </div>
      <div id="zf-pg-top"></div>
      <div id="zf-cards"></div>
      <div id="zf-pg-bot"></div>
    `;
    (origContainer?.parentNode || document.body).insertBefore(resultEl, origContainer);

    // 图片显示开关：原地替换 DOM，不重渲整页（避免丢失已展开的评论）
    document.getElementById('zf-img-toggle').onclick = () => {
      showImages = !showImages;
      const t = document.getElementById('zf-img-toggle');
      if (t) { t.textContent = showImages ? '🖼 隐藏图片' : '🖼 显示图片'; t.classList.toggle('active', showImages); }

      const cardsEl = document.getElementById('zf-cards');
      if (!cardsEl) return;
      if (showImages) {
        // 占位按钮 → 真实图片
        cardsEl.querySelectorAll('.zf-img-ph[data-real-src]').forEach(ph => {
          const src = ph.dataset.realSrc;
          const img = new Image();
          img.className = 'zf-img-loaded';
          img.onload  = () => ph.replaceWith(img);
          img.onerror = () => { ph.innerHTML = '❌ 图片加载失败'; ph.disabled = true; };
          ph.innerHTML = '⏳ 加载中...'; ph.disabled = true;
          img.src = src;
        });
      } else {
        // 真实图片 → 占位按钮
        cardsEl.querySelectorAll('img.zf-img-loaded').forEach(img => {
          img.replaceWith(createImgPlaceholder(img.src));
        });
      }
    };
  }

  function renderPage(page) {
    const total = currentSorted.length;
    const totalPages = Math.ceil(total / itemsPerPage);
    page = Math.max(1, Math.min(page, totalPages));
    currentPage = page;
    const start = (page - 1) * itemsPerPage;
    const slice = currentSorted.slice(start, start + itemsPerPage);
    const cards = document.getElementById('zf-cards');
    if (!cards) return;
    cards.innerHTML = '';
    const frag = document.createDocumentFragment();
    slice.forEach((ans, i) => frag.appendChild(buildCard(ans, start + i)));
    cards.appendChild(frag);
    const pgHTML = buildPaginationHTML(page, totalPages, total);
    ['zf-pg-top', 'zf-pg-bot'].forEach(id => {
      const el = document.getElementById(id); if (!el) return;
      el.innerHTML = pgHTML;
      el.querySelectorAll('[data-pg]').forEach(btn => {
        btn.addEventListener('click', () => {
          const p = parseInt(btn.dataset.pg, 10);
          if (!isNaN(p)) { renderPage(p); resultEl?.scrollIntoView({ behavior: 'smooth' }); }
        });
      });
      const ji = el.querySelector('.zf-pg-jump-input'), jb = el.querySelector('.zf-pg-jump-btn');
      if (ji && jb) {
        jb.addEventListener('click', () => {
          const p = parseInt(ji.value, 10);
          if (p >= 1 && p <= totalPages) { renderPage(p); resultEl?.scrollIntoView({ behavior: 'smooth' }); }
        });
        ji.addEventListener('keydown', e => { if (e.key === 'Enter') jb.click(); });
      }
    });
  }

  function buildPaginationHTML(page, total, count) {
    if (total <= 1) return '';
    const nums = genPageNums(page, total);
    const btnHTML = nums.map(p =>
      p === '…' ? `<span style="padding:0 4px;color:#aaa">…</span>`
                : `<button data-pg="${p}" ${p === page ? 'class="active"' : ''}>${p}</button>`
    ).join('');
    return `<div class="zf-pagination">
      <button data-pg="${page-1}" ${page<=1?'disabled':''}>← 上页</button>
      ${btnHTML}
      <button data-pg="${page+1}" ${page>=total?'disabled':''}>下页 →</button>
      <span class="zf-pg-info">第${page}/${total}页 | 共${count}条</span>
      <input class="zf-pg-jump-input" type="number" min="1" max="${total}" placeholder="${page}">
      <button class="zf-pg-jump-btn">GO</button>
    </div>`;
  }

  function genPageNums(cur, total) {
    if (total <= 7) return Array.from({ length: total }, (_, i) => i + 1);
    const set = new Set([1, total, cur]);
    for (let d = -2; d <= 2; d++) { const p = cur + d; if (p >= 1 && p <= total) set.add(p); }
    const sorted = [...set].sort((a, b) => a - b);
    const out = []; let prev = 0;
    for (const p of sorted) { if (p - prev > 1) out.push('…'); out.push(p); prev = p; }
    return out;
  }

  /**
   * 创建图片占位按钮（含 onclick，避免 innerHTML 序列化丢失事件）
   */
  function createImgPlaceholder(realSrc) {
    const ph = document.createElement('button');
    ph.className = 'zf-img-ph';
    ph.innerHTML = '🖼 点击加载图片';
    ph.title = realSrc;
    ph.dataset.realSrc = realSrc;  // 供「显示图片」全局开关复用
    ph.onclick = () => {
      const img = new Image();
      img.className = 'zf-img-loaded';
      ph.innerHTML = '⏳ 加载中...'; ph.disabled = true;
      img.onload  = () => ph.replaceWith(img);
      img.onerror = () => { ph.innerHTML = '❌ 图片加载失败'; ph.disabled = true; };
      img.src = realSrc;
    };
    return ph;
  }

  /**
   * 将回答 HTML 直接填充到 container 并原地处理 <img>。
   *
   * ⚠️ 不能用 return innerHTML 字符串再赋给别处！
   *    DOM onclick 不能序列化为 HTML 字符串，赋值后点击无效。
   *    必须在真实 DOM 上直接操作。
   */
  function populateContent(container, rawHtml) {
    if (!rawHtml) { container.textContent = '（无内容）'; return; }
    container.innerHTML = rawHtml;
    container.querySelectorAll('noscript').forEach(n => n.remove());
    container.querySelectorAll('img').forEach(img => {
      const real = img.dataset.actualsrc || img.dataset.src || img.getAttribute('src') || '';
      const isBad = !real || real.startsWith('data:image/svg') ||
        real.includes('empty.gif') || real.includes('transparent') || !real.startsWith('http');
      if (isBad) { img.remove(); return; }

      if (showImages) {
        img.src = real;
        img.className = 'zf-img-loaded';
        img.removeAttribute('data-actualsrc'); img.removeAttribute('data-src');
      } else {
        img.replaceWith(createImgPlaceholder(real));
      }
    });
  }

  function buildCard(ans, idx) {
    const card = document.createElement('div');
    card.className = 'zf-answer-card';
    const votes   = ans.voteup_count ?? 0;
    const ts      = ans.created_time ?? 0;
    const author  = ans.author?.name ?? '匿名用户';
    const aUrlToken = ans.author?.url_token || ans.author?.id;
    const aUrl    = aUrlToken ? `https://www.zhihu.com/people/${aUrlToken}` : '#';
    const time    = ts ? new Date(ts * 1000).toLocaleString('zh-CN') : '?';
    const rawHtml = ans.content || ans.excerpt || '（无内容）';
    const cntCmt  = ans.comment_count ?? 0;

    const meta = document.createElement('div');
    meta.className = 'zf-answer-meta';
    meta.innerHTML = `
      <span class="zf-rank">#${idx + 1}</span>
      <span class="zf-vote-badge">👍 ${votes.toLocaleString()}</span>
      <span class="zf-time-badge">🕐 ${time}</span>
      <a class="zf-author" href="${aUrl}" target="_blank" rel="noopener">${author}</a>
    `;

    const contentDiv = document.createElement('div');
    contentDiv.className = 'zf-answer-content collapsed';
    // 用 populateContent 原地填充，保留图片 onclick 事件
    populateContent(contentDiv, rawHtml);

    const actions = document.createElement('div');
    actions.className = 'zf-card-actions';

    const expandBtn = document.createElement('button');
    expandBtn.className = 'zf-expand-btn';
    expandBtn.textContent = '▼ 展开全文';
    let expanded = false;
    expandBtn.onclick = () => {
      expanded = !expanded;
      contentDiv.classList.toggle('collapsed', !expanded);
      expandBtn.textContent = expanded ? '▲ 收起' : '▼ 展开全文';
    };

    const commentBtn = document.createElement('button');
    commentBtn.className = 'zf-comment-btn';
    commentBtn.textContent = cntCmt > 0 ? `💬 ${cntCmt} 条评论` : '💬 查看评论';
    commentBtn.onclick = () => openCommentModal(ans.id, cntCmt, author);

    actions.appendChild(expandBtn);
    actions.appendChild(commentBtn);

    card.appendChild(meta);
    card.appendChild(contentDiv);
    card.appendChild(actions);
    return card;
  }

  function onRestore() {
    resultEl?.remove(); resultEl = null;
    if (origContainer) { origContainer.style.display = ''; origContainer = null; }

    // 恢复右侧边栏和左侧主内容区的原始样式
    if (origSidebar) {
      origSidebar.style.display = origSidebarDisplay;
      origSidebar = null;
    }
    if (origMainCol) {
      origMainCol.style.width = origMainColWidth;
      origMainCol.style.maxWidth = origMainColMaxWidth;
      origMainCol = null;
    }

    currentSorted = []; currentPage = 1;
    updateStatus('✅ 已恢复原始页面');
    setSortEnabled(allAnswers.length > 0);
  }


  // ═══════════════════════════════════════════════════════════
  // § 12. 初始化
  // ═══════════════════════════════════════════════════════════
  function waitForBody() {
    if (document.body) injectPanel();
    else setTimeout(waitForBody, 80);
  }
  waitForBody();

  // 监听网页可见性变化，切换回标签页时立刻触发一次抓取与状态检查，提升挂机唤醒体验
  document.addEventListener('visibilitychange', () => {
    if (!document.hidden && isFetching) {
      console.log('[ZhihuFetcher] Tab became active, triggering instant status check...');
      scheduleFetch(50);
    }
  });

  console.log(`[ZhihuFetcher] v0.9 初始化完成，QID=${QID}`);
})();
