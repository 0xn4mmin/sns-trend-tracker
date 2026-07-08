#!/usr/bin/env python3
"""TrendPulse 서버 — 유튜브/쇼츠/릴스/틱톡/X/스레드 인기 콘텐츠와 AI 영상 소식 API.
외부 패키지 없이 파이썬 표준 라이브러리만 사용합니다.

실행:  python3 server.py
배포:  HOST/PORT 환경변수를 읽으므로 Render·Railway·Fly.io 등에 그대로 올릴 수 있습니다.
       (Dockerfile / Procfile 포함 — README.md 참고)
"""
import base64
import email.utils
import gzip
import http.cookiejar
import json
import os
import random
import re
import threading
import time
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, quote, urlencode

HOST = os.environ.get("HOST", "0.0.0.0")
PORT = int(os.environ.get("PORT", "8778"))
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
# 계정 목록 저장 위치 (배포 환경에서는 볼륨 경로를 DATA_DIR로 지정하면 영속화됩니다)
DATA_DIR = os.environ.get("DATA_DIR", BASE_DIR)
CACHE_TTL = int(os.environ.get("CACHE_TTL", "3600"))  # 초 단위, 기본 1시간
CACHE_MAX = 300          # 데이터 캐시 키 상한
IMG_CACHE_MAX = 600      # 썸네일 프록시 캐시 개수 상한
STARTED_AT = time.time()
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

_cache = {}
_cache_lock = threading.Lock()
_img_cache = {}
_img_lock = threading.Lock()

# 원본(인스타/X 등)이 401/429로 차단하면 일정 시간 요청을 멈춰 차단이 길어지는 것을 막습니다.
_cooldown = {}
_cooldown_lock = threading.Lock()


def in_cooldown(source: str) -> bool:
    with _cooldown_lock:
        return time.time() < _cooldown.get(source, 0)


def set_cooldown(source: str, seconds: int):
    with _cooldown_lock:
        _cooldown[source] = max(_cooldown.get(source, 0), time.time() + seconds)
    print("[cooldown] %s: %d초 대기" % (source, seconds))


# ================================================================ 로그인 세션
# 사용자가 '자기 브라우저에서' 얻은 세션 쿠키를 넣으면 인증 요청으로 수집합니다.
# (비밀번호/자동 로그인은 다루지 않습니다 — 안전과 안티봇 회피 모두를 위해)
# 우선순위: 런타임 설정 파일(sessions.json) > 환경변수. 없으면 무인증으로 폴백합니다.
SESSIONS_FILE = os.path.join(DATA_DIR, "sessions.json")
ADMIN_TOKEN = os.environ.get("ADMIN_TOKEN", "")
# 쿠키는 반드시 '그 플랫폼 자신의 도메인'으로만 전송됩니다.
# 틱톡은 제3자 프록시(tikwm)를 경유하므로 세션 쿠키를 넣지 않습니다(유출 방지 + 무인증으로도 동작).
SESSION_ENV = {
    "instagram": "IG_COOKIE",   # instagram.com / threads.com (동일 Meta 로그인)
    "x": "X_COOKIE",            # x.com
    "threads": "THREADS_COOKIE",  # threads.com (비우면 instagram 쿠키 공유)
    "youtube": "YT_COOKIE",     # youtube.com
}
_sessions = {}
_sessions_lock = threading.Lock()


def load_sessions():
    """환경변수 + sessions.json을 병합해 플랫폼별 쿠키 문자열 dict를 만듭니다."""
    merged = {}
    for plat, env in SESSION_ENV.items():
        v = os.environ.get(env, "").strip()
        if v:
            merged[plat] = v
    try:
        with open(SESSIONS_FILE) as f:
            data = json.load(f)
        if isinstance(data, dict):
            for plat, v in data.items():
                if plat in SESSION_ENV and isinstance(v, str) and v.strip():
                    merged[plat] = v.strip()  # 파일(UI 설정)이 환경변수를 덮어씀
    except (OSError, json.JSONDecodeError):
        pass
    with _sessions_lock:
        _sessions.clear()
        _sessions.update(merged)
    return merged


def session_cookie(platform: str) -> str:
    with _sessions_lock:
        return _sessions.get(platform, "")


def cookie_value(cookie_str: str, name: str) -> str:
    m = re.search(r"(?:^|;\s*)%s=([^;]+)" % re.escape(name), cookie_str or "")
    return m.group(1) if m else ""


def save_sessions_file(patch: dict):
    """UI에서 넘어온 쿠키를 sessions.json에 병합 저장합니다. 빈 문자열은 삭제로 처리."""
    try:
        with open(SESSIONS_FILE) as f:
            data = json.load(f)
        if not isinstance(data, dict):
            data = {}
    except (OSError, json.JSONDecodeError):
        data = {}
    for plat, v in patch.items():
        if plat not in SESSION_ENV:
            continue
        if isinstance(v, str) and v.strip():
            data[plat] = v.strip()
        else:
            data.pop(plat, None)
    with open(SESSIONS_FILE, "w") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    load_sessions()


def sessions_status():
    """쿠키 값은 절대 노출하지 않고, 어떤 플랫폼이 설정됐는지 여부만 반환합니다."""
    with _sessions_lock:
        return {plat: bool(_sessions.get(plat)) for plat in SESSION_ENV}

USERNAME_RE = re.compile(r"^[A-Za-z0-9._\-]{1,40}$")

# ---------------------------------------------------------------- 유튜브
# 카테고리 → 유튜브 검색어 매핑
CATEGORIES = {
    "먹방": "먹방",
    "뷰티/패션": "뷰티 메이크업 패션",
    "브이로그": "브이로그",
    "예능/코미디": "예능 웃긴 영상",
    "영화/드라마": "영화 드라마 리뷰",
    "테크/IT": "테크 리뷰",
    "지식/교육": "지식 교양",
    "여행": "여행",
    "동물": "강아지 고양이",
}
# "전체" 탭은 아래 카테고리들을 합쳐 조회수순으로 재정렬
ALL_MERGE = ["먹방", "브이로그", "예능/코미디", "뷰티/패션", "영화/드라마", "여행"]

# 검색 필터 protobuf: 업로드 날짜 (2=오늘, 3=이번 주, 4=이번 달)
PERIOD_CODE = {"day": 2, "week": 3, "month": 4}

# 검색 결과에 섞여 오는 추천 섹션 영상이 기간 필터를 우회하는 경우를 걸러내기 위한
# 기간별 제외 문구 ("N일 전" 형태의 게시일 텍스트 기준)
PERIOD_EXCLUDE = {
    "day": ("일 전", "주 전", "개월 전", "년 전"),
    "week": ("주 전", "개월 전", "년 전"),
    "month": ("개월 전", "년 전"),
}

# ---------------------------------------------------------------- 구독 계정
IG_APP_ID = "936619743392459"           # instagram.com 웹이 쓰는 공개 앱 ID
IG_APP_ID_THREADS = "238260118697367"   # threads.com 웹이 쓰는 공개 앱 ID

DEFAULT_IG_ACCOUNTS = [
    "openai", "runwayapp", "pika_labs", "lumalabsai", "midjourney",
    "klingai_official", "heygen_official", "higgsfield.ai", "googledeepmind",
]
DEFAULT_X_ACCOUNTS = [
    "OpenAI", "runwayml", "Kling_ai", "GoogleDeepMind", "midjourney",
    "LumaLabsAI", "pika_labs", "heygen_com", "elevenlabsio", "AIatMeta",
]
DEFAULT_THREADS_ACCOUNTS = [
    "openai", "runway", "google", "meta.ai", "zuck",
]
DEFAULT_TIKTOK_ACCOUNTS = [
    "openai", "runwayapp", "krea.ai", "elevenlabs", "sora",
    "zachking", "khaby.lame", "google",
]

# 계정 목록을 쓰는 소스별 설정 (파일 경로, 기본 계정)
ACCOUNT_SOURCES = {
    "reels": (os.path.join(DATA_DIR, "reels_accounts.json"), DEFAULT_IG_ACCOUNTS),
    "x": (os.path.join(DATA_DIR, "x_accounts.json"), DEFAULT_X_ACCOUNTS),
    "threads": (os.path.join(DATA_DIR, "threads_accounts.json"), DEFAULT_THREADS_ACCOUNTS),
    "tiktok": (os.path.join(DATA_DIR, "tiktok_accounts.json"), DEFAULT_TIKTOK_ACCOUNTS),
}

# ---------------------------------------------------------------- 틱톡(TikTok)
# tikwm 무료 공개 API가 서명(X-Bogus/msToken)을 대신 처리해 조회수·좋아요·댓글까지 반환합니다.
TIKWM_BASE = "https://www.tikwm.com/api"
TIKTOK_REGION = os.environ.get("TIKTOK_REGION", "KR")

# ---------------------------------------------------------------- AI 영상 탭
AI_YT_QUERIES = ["AI 영상 제작", "AI 영상 생성", "sora ai video", "runway kling veo"]
NEWS_FEEDS = [
    ("국내", "https://news.google.com/rss/search?q=" +
     quote('AI 영상 생성 OR "AI 비디오" OR 영상생성모델') + "&hl=ko&gl=KR&ceid=KR:ko"),
    ("해외", "https://news.google.com/rss/search?q=" +
     quote('"AI video" model OR Sora OR Runway OR Kling OR Veo') + "&hl=en-US&gl=US&ceid=US:en"),
]
HF_PIPELINES = ["text-to-video", "image-to-video"]
# 이미지 프록시로 가져올 수 있는 호스트 (핫링크/차단 우회용)
IMG_PROXY_ALLOW = (".cdninstagram.com", ".fbcdn.net", ".ytimg.com",
                   ".googleusercontent.com", ".twimg.com",
                   ".tiktokcdn.com", ".tiktokcdn-eu.com", ".tiktokcdn-us.com")


def within_period(published: str, period: str) -> bool:
    if not published:
        return True  # 게시일 정보가 없으면(라이브 등) 통과
    return not any(word in published for word in PERIOD_EXCLUDE.get(period, ()))


def build_search_params(period: str, shorts: bool = False) -> str:
    """정렬=조회수(3) + 필터(업로드날짜, 동영상 타입, 길이) protobuf를 base64로 만듭니다."""
    filters = bytes([0x08, PERIOD_CODE.get(period, 3), 0x10, 0x01])
    if shorts:
        filters += bytes([0x18, 0x01])  # 길이: 4분 미만
    raw = bytes([0x08, 0x03, 0x12, len(filters)]) + filters
    return base64.urlsafe_b64encode(raw).decode()


def http_get(url: str, payload=None, headers=None, timeout=15, retries=1):
    data = json.dumps(payload).encode() if payload is not None else None
    last_err = None
    for attempt in range(retries + 1):
        req = urllib.request.Request(url, data=data)
        req.add_header("User-Agent", UA)
        if payload is not None:
            req.add_header("Content-Type", "application/json")
        for k, v in (headers or {}).items():
            req.add_header(k, v)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.headers.get("Content-Type", ""), resp.read()
        except Exception as e:
            last_err = e
            if attempt < retries:
                time.sleep(0.6)
    raise last_err


def http_json(url: str, payload=None, headers=None, timeout=15, retries=1):
    _, body = http_get(url, payload, headers, timeout, retries)
    return json.loads(body.decode())


def parse_view_count(text: str) -> int:
    digits = re.sub(r"[^\d]", "", text or "")
    return int(digits) if digits else 0


def cached(key, force, fetch_fn):
    """TTL 캐시 + 장애 폴백: 원본 조회가 실패하거나 비어 있으면 만료된 캐시라도 반환합니다."""
    now = time.time()
    with _cache_lock:
        hit = _cache.get(key)
    if hit and not force and now - hit[0] < CACHE_TTL:
        return hit[1], hit[0]
    try:
        result = fetch_fn()
    except Exception:
        result = None
    is_empty = result is None or (isinstance(result, (list, dict)) and not result)
    if is_empty:
        if hit:
            return hit[1], hit[0]  # 원본 장애 시 stale 데이터 유지
        # 빈 결과는 캐시하지 않아 다음 요청에서 즉시 재시도됩니다 (일시 장애가 1시간 눌러붙는 것 방지)
        return ([] if result is None else result), time.time()
    fetched_at = time.time()
    with _cache_lock:
        if len(_cache) >= CACHE_MAX:
            oldest = min(_cache, key=lambda k: _cache[k][0])
            _cache.pop(oldest, None)
        _cache[key] = (fetched_at, result)
    return result, fetched_at


# ================================================================ 유튜브
def extract_videos(node, out):
    """응답 트리를 순회하며 videoRenderer를 수집합니다."""
    if isinstance(node, dict):
        if "videoRenderer" in node:
            v = node["videoRenderer"]
            title = "".join(r.get("text", "") for r in v.get("title", {}).get("runs", []))
            views_text = v.get("viewCountText", {}).get("simpleText", "")
            thumbs = v.get("thumbnail", {}).get("thumbnails", [])
            out.append({
                "id": v.get("videoId", ""),
                "title": title,
                "channel": "".join(r.get("text", "") for r in v.get("ownerText", {}).get("runs", [])),
                "views": parse_view_count(views_text),
                "viewsText": views_text,
                "length": v.get("lengthText", {}).get("simpleText", ""),
                "published": v.get("publishedTimeText", {}).get("simpleText", ""),
                "thumbnail": thumbs[-1]["url"] if thumbs else "",
            })
        for value in node.values():
            extract_videos(value, out)
    elif isinstance(node, list):
        for item in node:
            extract_videos(item, out)


def yt_search(query: str, period: str, shorts: bool):
    payload = {
        "context": {"client": {
            "clientName": "WEB",
            "clientVersion": "2.20250624.01.00",
            "hl": "ko", "gl": "KR",
        }},
        "query": query,
        "params": build_search_params(period, shorts),
    }
    yc = session_cookie("youtube")
    try:
        data = http_json("https://www.youtube.com/youtubei/v1/search", payload,
                         headers={"Cookie": yc} if yc else None)
    except Exception:
        return []
    videos = []
    extract_videos(data, videos)
    seen, unique = set(), []
    for v in videos:
        if v["id"] and v["id"] not in seen and within_period(v["published"], period):
            seen.add(v["id"])
            unique.append(v)
    return unique


def yt_like_count(video_id: str):
    """youtubei/v1/next로 영상 1개의 좋아요 수를 가져옵니다(검색 API엔 없음)."""
    payload = {"context": {"client": {
        "clientName": "WEB", "clientVersion": "2.20250624.01.00", "hl": "ko", "gl": "KR"}},
        "videoId": video_id}
    yc = session_cookie("youtube")
    try:
        _, body = http_get("https://www.youtube.com/youtubei/v1/next",
                           payload=payload, timeout=10, retries=0,
                           headers={"Cookie": yc} if yc else None)
        s = body.decode("utf-8", "ignore")
        m = re.search(r"다른 사용자 ([0-9,]+)명", s) or re.search(r"along with ([0-9,]+) other", s)
        return int(m.group(1).replace(",", "")) + 1 if m else 0
    except Exception:
        return 0


def enrich_likes(videos, limit=45):
    """영상 리스트에 좋아요 수(likes)를 병렬로 채웁니다. 이미 채워진 항목은 건너뜁니다."""
    todo = [v for v in videos[:limit] if not v.get("likes")]
    if not todo:
        return videos
    with ThreadPoolExecutor(max_workers=12) as pool:
        counts = pool.map(lambda v: yt_like_count(v["id"]), todo)
    for v, c in zip(todo, counts):
        v["likes"] = c
    return videos


def merge_yt_searches(queries, period, shorts):
    with ThreadPoolExecutor(max_workers=6) as pool:
        results = pool.map(lambda q: yt_search(q, period, shorts), queries)
    merged, seen = [], set()
    for chunk in results:
        for v in chunk:
            if v["id"] not in seen:
                seen.add(v["id"])
                merged.append(v)
    merged.sort(key=lambda v: v["views"], reverse=True)
    return merged


def get_videos(category: str, period: str, shorts: bool, force: bool, enrich: bool = False, query: str = ""):
    def fetch():
        if query:
            queries = [query]
        elif category == "전체":
            queries = [CATEGORIES[c] for c in ALL_MERGE]
        elif category == "AI":
            queries = AI_YT_QUERIES
        else:
            queries = [CATEGORIES.get(category, category)]
        vids = merge_yt_searches(queries, period, shorts)
        if enrich:
            enrich_likes(vids)
        return vids
    return cached(("yt", query or category, period, shorts, enrich), force, fetch)


# ================================================================ 계정 목록
def load_accounts(path, defaults):
    try:
        with open(path) as f:
            accounts = json.load(f)
            if isinstance(accounts, list) and accounts:
                return accounts
    except (OSError, json.JSONDecodeError):
        pass
    return list(defaults)


def save_accounts(path, accounts):
    with open(path, "w") as f:
        json.dump(accounts, f, ensure_ascii=False, indent=2)


# ================================================================ 인스타그램 릴스
def _ig_opener():
    """instagram.com 홈을 먼저 방문해 쿠키(csrftoken 등)를 받은 opener를 만듭니다."""
    cj = http.cookiejar.CookieJar()
    op = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(cj))
    op.addheaders = [("User-Agent", UA), ("Accept-Language", "ko-KR,ko;q=0.9,en;q=0.8")]
    try:
        op.open("https://www.instagram.com/", timeout=10).read()
    except Exception:
        pass
    csrf = next((c.value for c in cj if c.name == "csrftoken"), "")
    return op, csrf


def ig_profile_json(username: str, opener=None, csrf: str = ""):
    """web_profile_info를 호출합니다. 401/403/429는 HTTPError로 올려 쿨다운 판단에 씁니다.
    로그인 세션 쿠키가 설정돼 있으면 인증 요청으로 보내 차단을 우회합니다."""
    url = ("https://www.instagram.com/api/v1/users/web_profile_info/?username="
           + quote(username))
    req = urllib.request.Request(url)
    req.add_header("User-Agent", UA)
    req.add_header("x-ig-app-id", IG_APP_ID)
    req.add_header("Accept", "*/*")
    req.add_header("Referer", "https://www.instagram.com/%s/" % quote(username))
    cookie = session_cookie("instagram")
    if cookie:
        req.add_header("Cookie", cookie)
        csrf = cookie_value(cookie, "csrftoken") or csrf
    if csrf:
        req.add_header("x-csrftoken", csrf)
    # 인증 쿠키가 있으면 IP 기반 opener 프라이밍이 불필요
    opener_fn = urllib.request.urlopen if cookie else (opener.open if opener else urllib.request.urlopen)
    with opener_fn(req, timeout=12) as resp:
        return json.loads(resp.read().decode())


def ig_feed_json(user_id: str, cookie: str, csrf: str, username: str):
    """로그인 세션으로 계정 피드(미디어 목록)를 가져옵니다. 401/403/429는 전파합니다."""
    url = "https://www.instagram.com/api/v1/feed/user/%s/?count=12" % quote(str(user_id))
    req = urllib.request.Request(url)
    req.add_header("User-Agent", UA)
    req.add_header("x-ig-app-id", IG_APP_ID)
    req.add_header("Cookie", cookie)
    if csrf:
        req.add_header("x-csrftoken", csrf)
    req.add_header("Referer", "https://www.instagram.com/%s/" % quote(username))
    with urllib.request.urlopen(req, timeout=12) as resp:
        return json.loads(resp.read().decode())


def _ig_reel_item(m, username):
    """피드 아이템(미디어)에서 릴스(영상, media_type=2)만 표준 형태로 변환합니다."""
    if not isinstance(m, dict) or m.get("media_type") != 2:
        return None
    cap = m.get("caption")
    title = (cap.get("text", "").split("\n")[0][:120] if isinstance(cap, dict) else "") or "(설명 없음)"
    cands = (m.get("image_versions2") or {}).get("candidates") or []
    return {
        "account": username,
        "title": title,
        "views": m.get("play_count") or m.get("ig_play_count") or 0,
        "likes": m.get("like_count") or 0,
        "comments": m.get("comment_count") or 0,
        "thumbnail": cands[0]["url"] if cands else "",
        "url": "https://www.instagram.com/reel/%s/" % m.get("code", ""),
        "takenAt": m.get("taken_at") or 0,
    }


def fetch_ig_reels(username: str, opener=None, csrf: str = ""):
    """계정의 최근 릴스를 가져옵니다.
    - 로그인 세션이 있으면: 프로필로 user_id 확보 → 피드 API로 미디어 수집(현재 유일하게 안정적).
    - 없으면: 무인증 web_profile_info(대부분 차단됨) 폴백.
    차단 관련 HTTPError(401/403/429)는 호출자에게 전파해 쿨다운 판단에 씁니다."""
    cookie = session_cookie("instagram")
    try:
        data = ig_profile_json(username, opener, csrf)
    except urllib.error.HTTPError as e:
        if e.code in (401, 403, 429):
            raise
        return []
    except Exception:
        return []
    user = (data.get("data") or {}).get("user") or {}

    # 1) 인증 상태: 피드 API로 실제 미디어 수집
    if cookie and user.get("id"):
        eff_csrf = cookie_value(cookie, "csrftoken") or csrf
        try:
            feed = ig_feed_json(user["id"], cookie, eff_csrf, username)
        except urllib.error.HTTPError as e:
            if e.code in (401, 403, 429):
                raise
            feed = {}
        except Exception:
            feed = {}
        items = feed.get("items") or feed.get("profile_grid_items") or []
        reels, seen = [], set()
        for it in items:
            m = it.get("media") if isinstance(it.get("media"), dict) else it
            r = _ig_reel_item(m, username)
            if r and r["url"] not in seen:
                seen.add(r["url"])
                reels.append(r)
        if reels:
            return reels

    # 2) 무인증 폴백: 예전 web_profile_info 그래프 구조(현재는 대부분 빈 값)
    reels = []
    for edge in (user.get("edge_owner_to_timeline_media") or {}).get("edges", []):
        n = edge.get("node", {})
        if not n.get("is_video"):
            continue
        caps = (n.get("edge_media_to_caption") or {}).get("edges") or []
        title = caps[0]["node"]["text"].split("\n")[0][:120] if caps else ""
        reels.append({
            "account": username,
            "title": title or "(설명 없음)",
            "views": n.get("video_view_count") or 0,
            "likes": (n.get("edge_liked_by") or {}).get("count", 0),
            "comments": (n.get("edge_media_to_comment") or {}).get("count", 0),
            "thumbnail": n.get("thumbnail_src") or "",
            "url": "https://www.instagram.com/reel/%s/" % n.get("shortcode", ""),
            "takenAt": n.get("taken_at_timestamp") or 0,
        })
    return reels


def get_reels(force: bool):
    path, defaults = ACCOUNT_SOURCES["reels"]
    accounts = load_accounts(path, defaults)

    def fetch():
        # 인스타그램은 병렬·고빈도 무인증 요청에 IP 차단(401)을 걸므로 순차 + 간격으로 순하게 수집합니다.
        # 로그인 세션이 있으면 차단이 잘 걸리지 않아 조금 더 빠르게 수집하고, 쿨다운도 건너뜁니다.
        authed = bool(session_cookie("instagram"))
        if in_cooldown("ig") and not authed:
            return []
        opener, csrf = (None, "") if authed else _ig_opener()
        gap = (0.3, 0.4) if authed else (1.0, 0.8)
        merged = []
        for i, username in enumerate(accounts):
            if i:
                time.sleep(gap[0] + random.random() * gap[1])
            try:
                merged.extend(fetch_ig_reels(username, opener, csrf))
            except urllib.error.HTTPError:
                # 인증 상태면 쿠키 만료 문제일 수 있으니 짧게, 무인증이면 IP 차단이므로 길게 쿨다운
                set_cooldown("ig", 120 if authed else 900)
                break
        merged.sort(key=lambda r: r["views"], reverse=True)
        return merged
    reels, fetched_at = cached(("reels", tuple(accounts)), force, fetch)
    return reels, accounts, fetched_at


# ================================================================ X (트위터)
def _find_timeline_entries(node):
    """syndication __NEXT_DATA__에서 timeline entries 리스트를 찾습니다."""
    if isinstance(node, dict):
        tl = node.get("timeline")
        if isinstance(tl, dict) and isinstance(tl.get("entries"), list):
            return tl["entries"]
        for v in node.values():
            r = _find_timeline_entries(v)
            if r:
                return r
    elif isinstance(node, list):
        for v in node:
            r = _find_timeline_entries(v)
            if r:
                return r
    return None


# X 웹앱 공개 베어러(모든 브라우저가 동일하게 사용) + GraphQL 쿼리 ID.
# 쿼리 ID는 X가 수시로 바꾸므로, 수집이 안 되면 여기 값을 최신으로 갱신하세요.
X_BEARER = ("AAAAAAAAAAAAAAAAAAAAANRILgAAAAAAnNwIzUejRCOuH5E6I8xnZz4puTs%3D"
            "1Zv7ttfk8LF81IUq16cHjhLTvJu4FA33AGWWjCpTnA")
X_QID_USER = "G3KGOASz96M-Qu0nwmGXNg"    # UserByScreenName
X_QID_TWEETS = "E3opETHurmVJflFsUBVuUQ"  # UserTweets
X_FEATURES = {
    "hidden_profile_likes_enabled": True,
    "hidden_profile_subscriptions_enabled": True,
    "responsive_web_graphql_exclude_directive_enabled": True,
    "verified_phone_label_enabled": False,
    "subscriptions_verification_info_is_identity_verified_enabled": True,
    "subscriptions_verification_info_verified_since_enabled": True,
    "highlights_tweets_tab_ui_enabled": True,
    "responsive_web_twitter_article_notes_tab_enabled": True,
    "creator_subscriptions_tweet_preview_api_enabled": True,
    "responsive_web_graphql_skip_user_profile_image_extensions_enabled": False,
    "responsive_web_graphql_timeline_navigation_enabled": True,
    "c9s_tweet_anatomy_moderator_badge_enabled": True,
    "tweetypie_unmention_optimization_enabled": True,
    "responsive_web_edit_tweet_api_enabled": True,
    "graphql_is_translatable_rweb_tweet_is_translatable_enabled": True,
    "view_counts_everywhere_api_enabled": True,
    "longform_notetweets_consumption_enabled": True,
    "responsive_web_twitter_article_tweet_consumption_enabled": True,
    "tweet_awards_web_tipping_enabled": False,
    "freedom_of_speech_not_reach_fetch_enabled": True,
    "standardized_nudges_misinfo": True,
    "tweet_with_visibility_results_prefer_gql_limited_actions_policy_enabled": True,
    "rweb_video_timestamps_enabled": True,
    "longform_notetweets_rich_text_read_enabled": True,
    "longform_notetweets_inline_media_enabled": True,
    "responsive_web_enhance_cards_enabled": False,
    "articles_preview_enabled": True,
    "rweb_tipjar_consumption_enabled": True,
    "communities_web_enable_tweet_community_results_fetch": True,
    "creator_subscriptions_quote_tweet_preview_enabled": False,
}

# 게스트 토큰(쿠키 없이도 GraphQL을 쓸 수 있게 해주는 공개 토큰). 3시간 캐시.
_x_guest = {"token": "", "ts": 0}
_x_guest_lock = threading.Lock()


def x_guest_token(force=False):
    with _x_guest_lock:
        if not force and _x_guest["token"] and time.time() - _x_guest["ts"] < 10000:
            return _x_guest["token"]
    try:
        req = urllib.request.Request("https://api.twitter.com/1.1/guest/activate.json", data=b"")
        req.add_header("Authorization", "Bearer " + X_BEARER)
        req.add_header("User-Agent", UA)
        with urllib.request.urlopen(req, timeout=10) as r:
            tok = json.loads(r.read())["guest_token"]
        with _x_guest_lock:
            _x_guest["token"] = tok
            _x_guest["ts"] = time.time()
        return tok
    except Exception:
        return ""


def _x_headers(authed: bool):
    """authed=True면 로그인 쿠키(auth_token+ct0)로, 아니면 게스트 토큰으로 인증합니다."""
    h = {"Authorization": "Bearer " + X_BEARER, "User-Agent": UA,
         "Content-Type": "application/json", "x-twitter-active-user": "yes"}
    if authed:
        cookie = session_cookie("x")
        ct0 = cookie_value(cookie, "ct0")
        if not ct0:
            return None
        h["Cookie"] = cookie
        h["x-csrf-token"] = ct0
        h["x-twitter-auth-type"] = "OAuth2Session"
    else:
        gt = x_guest_token()
        if not gt:
            return None
        h["x-guest-token"] = gt
    return h


def _x_gql(qid, op, variables, headers, retry_guest=True):
    url = "https://x.com/i/api/graphql/%s/%s?variables=%s&features=%s" % (
        qid, op, quote(json.dumps(variables)), quote(json.dumps(X_FEATURES)))
    req = urllib.request.Request(url)
    for k, v in headers.items():
        req.add_header(k, v)
    try:
        with urllib.request.urlopen(req, timeout=12) as resp:
            return json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        # 게스트 토큰 만료(401/403)면 새로 발급받아 한 번 재시도
        if retry_guest and e.code in (401, 403) and "x-guest-token" in headers:
            gt = x_guest_token(force=True)
            if gt:
                headers = dict(headers, **{"x-guest-token": gt})
                return _x_gql(qid, op, variables, headers, retry_guest=False)
        raise


def _x_pick_media(lg):
    for mm in ((lg.get("extended_entities") or {}).get("media") or []):
        if mm.get("media_url_https"):
            return mm["media_url_https"]
    return ""


def _parse_x_graphql(data, username):
    """UserTweets 응답의 timeline instructions에서 이 계정의 원본 트윗만 추립니다
    (리트윗·인용된 남의 트윗 제외)."""
    posts, seen = [], set()

    def add_tweet(t):
        if not isinstance(t, dict):
            return
        if t.get("__typename") == "TweetWithVisibilityResults":
            t = t.get("tweet") or {}
        lg = t.get("legacy")
        if not isinstance(lg, dict) or lg.get("favorite_count") is None:
            return
        if lg.get("retweeted_status_result"):  # 리트윗 제외
            return
        tid = lg.get("id_str", "")
        if not tid or tid in seen:
            return
        user = (((t.get("core") or {}).get("user_results") or {}).get("result") or {})
        ulg = user.get("legacy") or {}
        screen = ulg.get("screen_name", "")
        # 이 계정 본인 글만 (대소문자 무시)
        if screen and screen.lower() != username.lower():
            return
        seen.add(tid)
        posts.append({
            "account": username, "name": ulg.get("name", username),
            "text": (lg.get("full_text") or "").strip(),
            "likes": lg.get("favorite_count") or 0,
            "replies": lg.get("reply_count") or 0,
            "retweets": lg.get("retweet_count") or 0,
            "views": int((t.get("views") or {}).get("count", 0) or 0),
            "media": _x_pick_media(lg),
            "url": "https://x.com/%s/status/%s" % (username, tid),
            "createdAt": lg.get("created_at", ""),
        })

    def walk_entries(o):
        # itemContent.tweet_results.result 만 훑어 인용/중첩 트윗 오염을 막습니다.
        if isinstance(o, dict):
            if "tweet_results" in o and isinstance(o["tweet_results"], dict):
                add_tweet(o["tweet_results"].get("result"))
            for v in o.values():
                walk_entries(v)
        elif isinstance(o, list):
            for v in o:
                walk_entries(v)
    walk_entries(data)
    return posts


def fetch_x_graphql(username: str, authed: bool):
    """X GraphQL로 계정의 트윗을 가져옵니다. authed=True면 로그인 쿠키, 아니면 게스트 토큰.
    실패하면 [] 반환 → 상위에서 다음 방법으로 폴백."""
    headers = _x_headers(authed)
    if headers is None:
        return []
    try:
        u = _x_gql(X_QID_USER, "UserByScreenName",
                   {"screen_name": username, "withSafetyModeUserFields": True}, headers)
        uid = (((u.get("data") or {}).get("user") or {}).get("result") or {}).get("rest_id")
        if not uid:
            return []
        t = _x_gql(X_QID_TWEETS, "UserTweets",
                   {"userId": uid, "count": 20, "includePromotedContent": False,
                    "withQuickPromoteEligibilityTweetFields": False,
                    "withVoice": True, "withV2Timeline": True}, headers)
        return _parse_x_graphql(t, username)
    except Exception:
        return []


def fetch_x_posts(username: str):
    """계정의 최근 트윗을 가져옵니다. 우선순위:
    1) 로그인 세션(있으면) → 2) 게스트 토큰 GraphQL(쿠키 불필요) → 3) syndication 폴백."""
    if session_cookie("x"):
        r = fetch_x_graphql(username, authed=True)
        if r:
            return r
    r = fetch_x_graphql(username, authed=False)
    if r:
        return r
    url = "https://syndication.twitter.com/srv/timeline-profile/screen-name/" + quote(username)
    try:
        _, body = http_get(url, headers={"Accept": "text/html"}, timeout=12, retries=0)
        html = body.decode("utf-8", "ignore")
        m = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.S)
        if not m:
            return []
        data = json.loads(m.group(1))
    except urllib.error.HTTPError as e:
        if e.code == 429:
            raise
        return []
    except Exception:
        return []
    entries = _find_timeline_entries(data) or []
    posts = []
    for e in entries:
        content = e.get("content", {}) if isinstance(e, dict) else {}
        t = content.get("tweet")
        if not isinstance(t, dict):
            tr = content.get("tweetResult") or {}
            t = tr.get("result") if isinstance(tr, dict) else None
        if not isinstance(t, dict) or t.get("favorite_count") is None:
            continue
        user = t.get("user", {}) if isinstance(t.get("user"), dict) else {}
        media = ""
        for mm in (t.get("mediaDetails") or []):
            if mm.get("media_url_https"):
                media = mm["media_url_https"]
                break
        posts.append({
            "account": username,
            "name": user.get("name", username),
            "text": (t.get("full_text") or t.get("text") or "").strip(),
            "likes": t.get("favorite_count") or 0,
            "replies": t.get("reply_count") or 0,
            "retweets": t.get("retweet_count") or 0,
            "views": int(t.get("views", {}).get("count", 0)) if isinstance(t.get("views"), dict) else 0,
            "media": media,
            "url": "https://x.com/%s/status/%s" % (username, t.get("id_str", "")),
            "createdAt": t.get("created_at", ""),
        })
    return posts


def get_x_posts(force: bool):
    path, defaults = ACCOUNT_SOURCES["x"]
    accounts = load_accounts(path, defaults)

    def fetch():
        # 게스트 토큰/로그인 GraphQL은 syndication보다 안정적이라 대부분 여기서 성공합니다.
        # 쿨다운은 무인증 syndication 폴백에만 해당하므로, GraphQL 경로는 항상 시도합니다.
        posts = []
        misses = 0
        for i, acct in enumerate(accounts):
            if i:
                time.sleep(0.3 + random.random() * 0.4)
            try:
                chunk = fetch_x_posts(acct)
            except urllib.error.HTTPError:
                set_cooldown("x", 900)  # syndication 429
                chunk = []
            posts.extend(chunk)
            misses = 0 if chunk else misses + 1
            if misses >= 5:  # 연속 실패는 서비스 쪽 문제 — 중단
                break
        return posts
    posts, fetched_at = cached(("x", tuple(accounts)), force, fetch)
    return posts, accounts, fetched_at


# ================================================================ 스레드(Threads)
def threads_cookie():
    # 스레드는 인스타그램 로그인을 공유하므로 threads 쿠키가 없으면 instagram 쿠키를 씁니다.
    return session_cookie("threads") or session_cookie("instagram")


def _threads_lsd_and_userid(username: str):
    """스레드 프로필 페이지에서 LSD 토큰을, 인스타 API에서 user_id를 얻습니다.
    ※ 스레드 페이지에는 로그인 쿠키를 붙이지 않습니다 — 붙이면 404가 납니다(무인증으로 받아야 LSD가 나옴)."""
    lsd = None
    try:
        _, body = http_get("https://www.threads.com/@" + quote(username), timeout=12)
        m = re.search(r'"LSD",\[\],\{"token":"([^"]+)"', body.decode("utf-8", "ignore"))
        lsd = m.group(1) if m else None
    except Exception:
        pass
    user_id = None
    if not in_cooldown("ig"):  # 인스타 API를 함께 쓰므로 쿨다운을 공유
        try:
            info = ig_profile_json(username)
            user_id = (info.get("data") or {}).get("user", {}).get("id")
        except urllib.error.HTTPError as e:
            if e.code in (401, 403, 429):
                set_cooldown("ig", 900)
        except Exception:
            pass
    return lsd, user_id


# 스레드 프로필 탭 쿼리의 doc_id는 수시로 바뀌므로, 알려진 후보를 순서대로 시도합니다.
THREADS_DOC_IDS = [
    "25073444226023094", "7451607104958938", "23996318550159868",
    "9925907010825989", "26286467210919721",
]


def fetch_threads_posts(username: str):
    lsd, user_id = _threads_lsd_and_userid(username)
    if not lsd or not user_id:
        return []
    cookie = threads_cookie()
    logged_in = bool(cookie)
    headers = {
        "X-FB-LSD": lsd, "X-IG-App-ID": IG_APP_ID_THREADS,
        "Sec-Fetch-Site": "same-origin",
        "X-FB-Friendly-Name": "BarcelonaProfileThreadsTabQuery",
        "Content-Type": "application/x-www-form-urlencoded",
    }
    if cookie:
        headers["Cookie"] = cookie
    for doc_id in THREADS_DOC_IDS:
        payload = urlencode({
            "lsd": lsd, "doc_id": doc_id,
            "variables": json.dumps({"userID": str(user_id), "__relay_internal__pv__BarcelonaIsLoggedInrelayprovider": logged_in}),
        }).encode()
        req = urllib.request.Request("https://www.threads.com/api/graphql", data=payload)
        req.add_header("User-Agent", UA)
        for k, v in headers.items():
            req.add_header(k, v)
        try:
            with urllib.request.urlopen(req, timeout=12) as resp:
                data = json.loads(resp.read().decode())
        except Exception:
            continue
        if data.get("errors"):
            continue
        posts = _parse_threads(data, username)
        if posts:
            return posts
    return []


def _parse_threads(data, username):
    posts = []

    def walk(o):
        if isinstance(o, dict):
            if "post" in o and isinstance(o["post"], dict) and o["post"].get("caption") is not None:
                p = o["post"]
                caption = (p.get("caption") or {}).get("text", "") if isinstance(p.get("caption"), dict) else ""
                info = p.get("text_post_app_info", {}) or {}
                imgs = (p.get("image_versions2") or {}).get("candidates") or []
                posts.append({
                    "account": username,
                    "text": caption[:280],
                    "likes": p.get("like_count") or 0,
                    "replies": info.get("direct_reply_count") or 0,
                    "reposts": info.get("repost_count") or 0,
                    "views": 0,
                    "media": imgs[0]["url"] if imgs else "",
                    "url": "https://www.threads.com/@%s/post/%s" % (username, p.get("code", "")),
                    "createdAt": p.get("taken_at") or 0,
                })
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)
    walk(data)
    return posts


def get_threads_posts(force: bool):
    path, defaults = ACCOUNT_SOURCES["threads"]
    accounts = load_accounts(path, defaults)

    def fetch():
        with ThreadPoolExecutor(max_workers=3) as pool:
            results = pool.map(fetch_threads_posts, accounts)
        return [p for chunk in results for p in chunk]
    posts, fetched_at = cached(("threads", tuple(accounts)), force, fetch)
    return posts, accounts, fetched_at


# ================================================================ 틱톡(TikTok)
def _tiktok_item(v):
    author = v.get("author", {}) if isinstance(v.get("author"), dict) else {}
    handle = author.get("unique_id", "")
    vid = v.get("video_id", "")
    return {
        "account": handle,
        "name": author.get("nickname", handle),
        "title": (v.get("title") or "").strip() or "(설명 없음)",
        "views": v.get("play_count") or 0,
        "likes": v.get("digg_count") or 0,
        "comments": v.get("comment_count") or 0,
        "shares": v.get("share_count") or 0,
        "thumbnail": v.get("cover") or v.get("origin_cover") or "",
        "url": "https://www.tiktok.com/@%s/video/%s" % (handle, vid),
        "id": vid,
        "createdAt": v.get("create_time") or 0,
    }


def fetch_tiktok_user(handle: str):
    url = "%s/user/posts?unique_id=%s&count=12" % (TIKWM_BASE, quote(handle))
    try:
        d = http_json(url, timeout=15)
    except Exception:
        return []
    vids = (d.get("data") or {}).get("videos") or []
    return [_tiktok_item(v) for v in vids]


def fetch_tiktok_trending():
    url = "%s/feed/list?region=%s&count=20" % (TIKWM_BASE, TIKTOK_REGION)
    try:
        d = http_json(url, timeout=15)
    except Exception:
        return []
    vids = d.get("data") or []
    return [_tiktok_item(v) for v in vids]


def get_tiktok(force: bool):
    path, defaults = ACCOUNT_SOURCES["tiktok"]
    accounts = load_accounts(path, defaults)

    def fetch():
        # 트렌딩(전체 인기) + 구독 계정 최신 영상을 합쳐 중복 제거.
        # tikwm 무료 티어의 레이트리밋을 피하려 동시성을 낮춥니다.
        posts = fetch_tiktok_trending()
        with ThreadPoolExecutor(max_workers=3) as pool:
            for chunk in pool.map(fetch_tiktok_user, accounts):
                posts.extend(chunk)
        seen, unique = set(), []
        for p in posts:
            if p["id"] and p["id"] not in seen:
                seen.add(p["id"])
                unique.append(p)
        return unique
    posts, fetched_at = cached(("tiktok", tuple(accounts)), force, fetch)
    return posts, accounts, fetched_at


# ================================================================ AI 영상 탭
def fetch_news():
    def one(feed):
        label, url = feed
        try:
            _, body = http_get(url, timeout=12)
            root = ET.fromstring(body)
        except Exception:
            return []
        items = []
        for item in root.iter("item"):
            title = item.findtext("title") or ""
            source = item.findtext("source") or ""
            pub = item.findtext("pubDate") or ""
            try:
                ts = email.utils.parsedate_to_datetime(pub).timestamp()
            except (TypeError, ValueError):
                ts = 0
            items.append({"region": label, "title": title, "source": source,
                          "link": item.findtext("link") or "", "ts": ts})
        return items[:25]

    with ThreadPoolExecutor(max_workers=2) as pool:
        results = pool.map(one, NEWS_FEEDS)
    merged = [n for chunk in results for n in chunk]
    merged.sort(key=lambda n: n["ts"], reverse=True)
    return merged[:40]


def fetch_hf_models():
    def one(args):
        pipeline, sort = args
        url = ("https://huggingface.co/api/models?pipeline_tag=%s&sort=%s"
               "&direction=-1&limit=12" % (pipeline, sort))
        try:
            data = http_json(url, timeout=12)
        except Exception:
            return []
        return [{"id": m.get("id", ""), "likes": m.get("likes", 0),
                 "downloads": m.get("downloads", 0), "pipeline": pipeline,
                 "createdAt": m.get("createdAt", "")} for m in data]

    jobs = [(p, s) for p in HF_PIPELINES for s in ("createdAt", "trendingScore")]
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(one, jobs))

    def dedupe(lists):
        seen, out = set(), []
        for chunk in lists:
            for m in chunk:
                if m["id"] not in seen:
                    seen.add(m["id"])
                    out.append(m)
        return out
    latest = dedupe(results[0::2])
    latest.sort(key=lambda m: m["createdAt"], reverse=True)
    trending = dedupe(results[1::2])
    return {"latest": latest[:12], "trending": trending[:12]}


def get_ai_data(force: bool):
    # AI 탭은 '글'(모델·뉴스)만 제공합니다. AI 영상은 유튜브 탭의 'AI' 카테고리로 통합됨.
    def fetch():
        with ThreadPoolExecutor(max_workers=2) as pool:
            news_f = pool.submit(fetch_news)
            models_f = pool.submit(fetch_hf_models)
            return {"news": news_f.result(), "models": models_f.result()}
    return cached(("ai",), force, fetch)


# ================================================================ 기타
def fetch_oembed(url: str):
    """틱톡/유튜브 URL의 oEmbed 메타데이터를 가져옵니다 (CORS 우회용 프록시)."""
    host = urlparse(url).netloc.lower()
    if "tiktok.com" in host:
        endpoint = "https://www.tiktok.com/oembed?url=" + quote(url, safe="")
    elif "youtube.com" in host or "youtu.be" in host:
        endpoint = "https://www.youtube.com/oembed?format=json&url=" + quote(url, safe="")
    else:
        return {"ok": False, "reason": "unsupported"}
    try:
        data = http_json(endpoint, timeout=10)
        return {"ok": True, "title": data.get("title", ""),
                "author": data.get("author_name", ""),
                "thumbnail": data.get("thumbnail_url", "")}
    except Exception:
        return {"ok": False, "reason": "fetch_failed"}


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        print("[%s] %s" % (time.strftime("%H:%M:%S"), fmt % args))

    def _send(self, code, body, content_type="application/json; charset=utf-8"):
        data = body if isinstance(body, bytes) else json.dumps(body, ensure_ascii=False).encode()
        headers = [("Content-Type", content_type),
                   ("Cache-Control", "no-store"),
                   ("X-Content-Type-Options", "nosniff")]
        accepts_gzip = "gzip" in (self.headers.get("Accept-Encoding") or "")
        if accepts_gzip and len(data) > 512 and not content_type.startswith("image/"):
            data = gzip.compress(data, 6)
            headers.append(("Content-Encoding", "gzip"))
        self.send_response(code)
        for k, v in headers:
            self.send_header(k, v)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        try:
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def do_GET(self):
        parsed = urlparse(self.path)
        qs = parse_qs(parsed.query)
        force = qs.get("force", ["0"])[0] == "1"

        if parsed.path in ("/", "/index.html"):
            with open(os.path.join(BASE_DIR, "index.html"), "rb") as f:
                self._send(200, f.read(), "text/html; charset=utf-8")
            return

        if parsed.path == "/api/health":
            self._send(200, {"ok": True, "uptime": int(time.time() - STARTED_AT)})
            return

        if parsed.path == "/api/sessions":
            # 설정 여부(불리언)만 반환 — 쿠키 값은 절대 노출하지 않습니다.
            self._send(200, {"configured": sessions_status(),
                             "adminRequired": bool(ADMIN_TOKEN)})
            return

        if parsed.path == "/api/videos":
            category = qs.get("category", ["전체"])[0]
            period = qs.get("period", ["week"])[0]
            shorts = qs.get("shorts", ["0"])[0] == "1"
            enrich = qs.get("enrich", ["0"])[0] == "1"
            query = qs.get("q", [""])[0].strip()
            if not query and category not in ("전체", "AI") and category not in CATEGORIES:
                self._send(400, {"error": "unknown category"})
                return
            videos, fetched_at = get_videos(category, period, shorts, force, enrich, query)
            self._send(200, {"videos": videos[:60], "fetchedAt": fetched_at})
            return

        if parsed.path == "/api/categories":
            self._send(200, {"categories": ["전체", "AI"] + list(CATEGORIES.keys())})
            return

        if parsed.path == "/api/reels":
            reels, accounts, fetched_at = get_reels(force)
            self._send(200, {"reels": reels[:80], "accounts": accounts, "fetchedAt": fetched_at,
                             "cooldown": in_cooldown("ig") and not session_cookie("instagram"),
                             "authed": bool(session_cookie("instagram"))})
            return

        if parsed.path == "/api/x":
            posts, accounts, fetched_at = get_x_posts(force)
            self._send(200, {"posts": posts, "accounts": accounts, "fetchedAt": fetched_at,
                             "cooldown": in_cooldown("x") and not session_cookie("x"),
                             "authed": bool(session_cookie("x"))})
            return

        if parsed.path == "/api/threads":
            posts, accounts, fetched_at = get_threads_posts(force)
            self._send(200, {"posts": posts, "accounts": accounts, "fetchedAt": fetched_at})
            return

        if parsed.path == "/api/tiktok":
            posts, accounts, fetched_at = get_tiktok(force)
            self._send(200, {"posts": posts[:100], "accounts": accounts, "fetchedAt": fetched_at})
            return

        if parsed.path == "/api/ai":
            data, fetched_at = get_ai_data(force)
            self._send(200, {**data, "fetchedAt": fetched_at})
            return

        if parsed.path == "/api/oembed":
            self._send(200, fetch_oembed(qs.get("url", [""])[0]))
            return

        if parsed.path == "/api/img":
            # 인스타/틱톡 CDN 등 핫링크가 막힌 썸네일을 서버가 대신 받아 전달(메모리 캐시)
            url = qs.get("u", [""])[0]
            host = urlparse(url).netloc.lower()
            if not url.startswith("https://") or not host.endswith(IMG_PROXY_ALLOW):
                self._send(400, {"error": "host not allowed"})
                return
            with _img_lock:
                hit = _img_cache.get(url)
            if hit:
                self._send(200, hit[1], hit[0])
                return
            try:
                ctype, body = http_get(url, timeout=12, retries=0)
                ctype = ctype or "image/jpeg"
                with _img_lock:
                    if len(_img_cache) > IMG_CACHE_MAX:
                        _img_cache.clear()
                    _img_cache[url] = (ctype, body)
                self._send(200, body, ctype)
            except Exception:
                self._send(502, {"error": "fetch failed"})
            return

        self._send(404, {"error": "not found"})

    def _read_json(self):
        length = int(self.headers.get("Content-Length", 0))
        try:
            return json.loads(self.rfile.read(length).decode())
        except (json.JSONDecodeError, ValueError):
            return None

    def do_POST(self):
        parsed = urlparse(self.path)

        # /api/sessions — 로그인 세션 쿠키 저장(값은 응답에 절대 포함하지 않음)
        if parsed.path == "/api/sessions":
            if ADMIN_TOKEN and self.headers.get("X-Admin-Token", "") != ADMIN_TOKEN:
                self._send(403, {"error": "admin token required"})
                return
            req = self._read_json()
            if not isinstance(req, dict):
                self._send(400, {"error": "invalid json"})
                return
            patch = {k: v for k, v in req.items() if k in SESSION_ENV and isinstance(v, str)}
            try:
                save_sessions_file(patch)
            except OSError:
                self._send(500, {"error": "read-only filesystem — 배포 환경에서는 환경변수를 사용하세요"})
                return
            self._send(200, {"configured": sessions_status()})
            return

        # /api/{reels|x|threads|tiktok}/accounts — 구독 계정 추가/삭제
        m = re.match(r"^/api/(reels|x|threads|tiktok)/accounts$", parsed.path)
        if m:
            source = m.group(1)
            path, defaults = ACCOUNT_SOURCES[source]
            length = int(self.headers.get("Content-Length", 0))
            try:
                req = json.loads(self.rfile.read(length).decode())
            except json.JSONDecodeError:
                self._send(400, {"error": "invalid json"})
                return
            action = req.get("action")
            raw = (req.get("username") or "").strip().lstrip("@")
            # X는 대소문자 보존, 인스타/스레드/틱톡은 소문자
            username = raw if source == "x" else raw.lower()
            if action == "add" and not USERNAME_RE.match(username):
                self._send(400, {"error": "invalid username"})
                return
            accounts = load_accounts(path, defaults)
            changed = False
            if action == "add" and username and username not in accounts:
                accounts.append(username)
                changed = True
            elif action == "remove" and username in accounts:
                accounts.remove(username)
                changed = True
            if changed:
                try:
                    save_accounts(path, accounts)
                except OSError:
                    pass  # 읽기 전용 파일시스템(일부 배포 환경)에서도 메모리상 목록은 응답
            self._send(200, {"accounts": accounts})
            return
        self._send(404, {"error": "not found"})


def _background_warmer():
    """빈 캐시(차단으로 수집 실패한 소스)를 10분마다 자동 재수집합니다.
    차단이 풀리면 사용자가 새로고침하지 않아도 탭이 스스로 회복됩니다."""
    while True:
        time.sleep(600)
        for fn in (get_reels, get_x_posts, get_threads_posts):
            try:
                fn(False)  # 캐시가 차 있으면 즉시 반환, 비어 있으면 재수집
            except Exception:
                pass


if __name__ == "__main__":
    load_sessions()
    active = [p for p, on in sessions_status().items() if on]
    if active:
        print("로그인 세션 활성화됨:", ", ".join(active))
    threading.Thread(target=_background_warmer, daemon=True).start()
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    print(f"TrendPulse 서버 실행 중: http://{'localhost' if HOST in ('0.0.0.0', '127.0.0.1') else HOST}:{PORT}")
    server.serve_forever()
