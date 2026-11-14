# -*- coding: utf-8 -*-
"""Kishuto —— TVBox / 影视仓 多源聚合源

  影探聚合(4源) · 稀饭动漫(4源) · 小鸡看看 · FoFo影院 · 小山影视 · 枫奇4K(至臻/蓝光) · 橘汁新网关4K · 四源4K专线(天堂/布布/华谊/苹果)
  分类/搜索按 tag 前缀派发，详情页跨源按标题补线路，播放按 id 派发回原源。
  本文件由 build_kishuto.py 自动生成。
"""

# ==================== 版本（必须放在最前：被聚合代码在模块级引用） ====
CODE_VERSION = '20261108.194545'
UPDATE_URL = 'https://gitee.com/tao060702/tvbox/raw/master/update_kishuto.json'

# ======================================================================
# 模块：yt
# ======================================================================
# -*- coding: utf-8 -*-
"""
影探聚合 —— 四源聚合 TVBox Python 源（单文件）
========================================================================
首页 / 分类 / 筛选 / 搜索：影探4K（cms.lyyytv.cn）
详情页线路顺序：影探4K → 咕噜咕噜 → 橘汁4K → 找剧AI

源说明（2026-11-04 实测）
  影探4K   CMS + fys 解析接口，线路多为联通云/移动云/爱奇艺直链，可播率高
  咕噜咕噜  T3 私有协议（ECDH P-256 + AES-256-GCM + protobuf），线路最多
  橘汁4K   同 host 的另一套 T3 客户端（包名/版本/详情参数不同），目录与 id 空间
           独立，线路与咕噜有互补
  找剧AI   zhaoju4.com，HMAC 签名的 REST，官方 4K/1080P 线路需登录态（自动游客会话）

依赖：纯标准库（无 requests / pycryptodome），自带 AES-128/256-CBC、AES-256-GCM、
     P-256 ECDH、protobuf 裸编解码实现，可直接丢进 TVBox 的 python 目录使用。
========================================================================
"""

import base64
import gzip
import hashlib
import hmac
import json
import os
import re
import secrets
import socket
import ssl
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import zlib

try:
    from base.spider import Spider as _BaseSpider
except Exception:
    _BaseSpider = object

UA_WEB = ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
          '(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36')
UA_ANDROID = ('Mozilla/5.0 (Linux; Android 13; SM-S9080) AppleWebKit/537.36 '
              '(KHTML, like Gecko) Chrome/120.0.0.0 Mobile Safari/537.36')

NL = '\n'
_SEP = '\x1f'


# ============================================================================
# 基础工具
# ============================================================================

def text(value):
    return '' if value is None else str(value).strip()


def as_list(value):
    return value if isinstance(value, list) else []


def as_dict(value):
    return value if isinstance(value, dict) else {}


def loads(value):
    """宽松 JSON 解析：容忍前后缀、非 JSON 内容。"""
    try:
        if not value:
            return {}
        if isinstance(value, (bytes, bytearray)):
            value = value.decode('utf-8', 'replace')
        value = str(value).strip()
        if value[:1] not in ('{', '['):
            m = re.search(r'[\{\[].*[\}\]]', value, re.S)
            if not m:
                return {}
            value = m.group(0)
        return json.loads(value)
    except Exception:
        return {}


def page_of(value):
    m = re.match(r'\s*[+-]?\d+', '' if value is None else str(value))
    n = int(m.group(0)) if m else 0
    return max(1, n) if n else 1


def clean_name(value):
    """线路/标题清洗：去掉 $ # | 以及多余空白，避免破坏 TVBox 分隔符。"""
    s = text(value)
    for ch in ('$', '#', '$$$', '|'):
        s = s.replace(ch, ' ')
    return re.sub(r'\s+', ' ', s).strip()


def norm_title(value):
    s = text(value).lower()
    s = re.sub(r'[\s\-_:：·,，.。!！?？"“”\'’()（）\[\]【】]+', '', s)
    s = re.sub(r'(第[一二三四五六七八九十\d]+季|season\s*\d+|s\d{1,2})$', '', s)
    return s


def sim(a, b):
    """标题相似度（0~1），够用即可：完全一致/包含/字符级 Jaccard。"""
    x, y = norm_title(a), norm_title(b)
    if not x or not y:
        return 0.0
    if x == y:
        return 1.0
    if x in y or y in x:
        return 0.82
    sx, sy = set(x), set(y)
    inter = len(sx & sy)
    if not inter:
        return 0.0
    return inter / float(len(sx | sy))


def best_match(title, items, floor=0.62):
    best, score = None, 0.0
    for it in as_list(items):
        if not isinstance(it, dict):
            continue
        s = sim(title, it.get('vod_name') or it.get('name') or '')
        if s > score:
            best, score = it, s
    return best if score >= floor else None


_SEASON_SIMPLE = re.compile(
    r'(第[一二三四五六七八九十\d]+季|season\s*\d+|s\d{1,2})', re.I)
_QUALITY_NOISE = re.compile(
    r'(4k|8k|2160p?|1080p?|720p?|uhd|hdr\d*|蓝光|高清|超清|'
    r'国语|粤语|中字|字幕|完整版|未删减|合集|正片|bd|hd|dvd|web|remux)', re.I)


def strict_match(title, items):
    """详情页跨源补线路：只认「同一部片」，禁止片名包含式扩展匹配。

    旧 best_match 把「熊出没」⊂「熊出没之雪岭熊风」判成 0.82 分，
    于是剧集《熊出没》详情里挂进了电影版线路。这里要求核心片名完全
    一致，只允许剥掉画质/版本/年份后缀；季数标记不同一律不匹配。
    """
    import difflib

    def core(s):
        t = norm_title(str(s or ''))
        t = re.sub(r'[（(][^）)]*[）)]', '', t)
        t = _QUALITY_NOISE.sub('', t)
        t = re.sub(r'(19|20)\d{2}$', '', t)
        t = re.sub(r'第[一二三四五六七八九十\d]+[季部篇]$', '', t)
        return t.strip()

    want = core(title)
    if not want:
        return None
    wm = _SEASON_SIMPLE.search(str(title or ''))
    wtag = wm.group(0).lower() if wm else ''
    exact, near = [], []
    for it in as_list(items):
        if not isinstance(it, dict):
            continue
        name = str(it.get('vod_name') or it.get('name') or '')
        cm = _SEASON_SIMPLE.search(name)
        ctag = cm.group(0).lower() if cm else ''
        if wtag and ctag and wtag != ctag:
            continue
        got = core(name)
        if not got:
            continue
        if got == want:
            exact.append(it)
        elif (abs(len(got) - len(want)) <= 2
              and difflib.SequenceMatcher(None, got, want).ratio() >= 0.97):
            near.append(it)
    return (exact or near or [None])[0]


# ============================================================================
# 缓存
# ============================================================================

_CACHE = {}
_CACHE_LOCK = threading.Lock()
_TITLE_MEMO = {}          # vod_id -> 片名：个别源详情只回数字 id，补线路要靠它
_DETAIL_MEMO = {}         # 详情 id -> (时间, [(线路名, [(集名, 播放码)])])


def _memo_detail(cid, lines):
    """记住本次详情拼出的全部线路，播放失败时用它同集换源。"""
    if not cid or not lines:
        return
    now = time.time()
    if len(_DETAIL_MEMO) > 200:
        for k in [k for k, v in list(_DETAIL_MEMO.items())
                  if now - v[0] > 1800]:
            _DETAIL_MEMO.pop(k, None)
        if len(_DETAIL_MEMO) > 200:
            _DETAIL_MEMO.clear()
    _DETAIL_MEMO[str(cid)] = (now, lines)


def _unpack_lines(vod):
    """把 _pack 后的 vod_play_from/url 反解成 [(线路名, [(集名, 播放码)])]。"""
    froms = str(vod.get('vod_play_from') or '').split('$$$')
    urls = str(vod.get('vod_play_url') or '').split('$$$')
    out = []
    for i, name in enumerate(froms):
        name = str(name or '').strip()
        if not name:
            continue
        seg = urls[i] if i < len(urls) else ''
        eps = []
        for part in str(seg).split('#'):
            part = part.strip()
            if not part:
                continue
            nm, sep, pid = part.partition('$')
            if not sep:
                nm, pid = '', part
            eps.append((nm, pid))
        if eps:
            out.append((name, eps))
    return out


def _memo_title(code, name):
    """记下列表/搜索里看到的真实片名，供详情缺片名时兜底。"""
    t = str(name or '').strip()
    if not code or len(t) < 2 or t.isdigit():
        return
    if len(_TITLE_MEMO) > 4000:
        _TITLE_MEMO.clear()
    _TITLE_MEMO[str(code)] = t


def cache_get(key):
    with _CACHE_LOCK:
        hit = _CACHE.get(key)
        if not hit:
            return None
        if hit[0] < time.time():
            _CACHE.pop(key, None)
            return None
        return hit[1]


def cache_put(key, value, ttl):
    with _CACHE_LOCK:
        if len(_CACHE) > 800:
            now = time.time()
            dead = [k for k, v in _CACHE.items() if v[0] < now]
            for k in dead[:300]:
                _CACHE.pop(k, None)
            if len(_CACHE) > 1000:
                _CACHE.clear()
        _CACHE[key] = (time.time() + ttl, value)


# ============================================================================
# HTTP（统一层：gzip、连接复用靠 keep-alive 由 urllib 自行管理、瞬时错误重试）
# ============================================================================

_CTX = [None, False]


def ssl_ctx():
    if _CTX[1] is False:
        try:
            c = ssl.create_default_context()
            c.check_hostname = False
            c.verify_mode = ssl.CERT_NONE
            _CTX[0] = c
        except Exception:
            _CTX[0] = None
        _CTX[1] = True
    return _CTX[0]


def http(url, method='GET', headers=None, data=None, timeout=8.0,
         retries=2, backoff=0.35):
    """返回 (status, body_bytes)。网络/瞬时错误自动重试，绝不抛异常。"""
    url = safe_url(url)
    hdr = {'User-Agent': UA_WEB, 'Accept': '*/*', 'Accept-Encoding': 'gzip'}
    if headers:
        hdr.update(headers)
    tries = max(1, int(retries))
    last = (0, b'')
    for i in range(tries):
        if i:
            time.sleep(backoff * i)
        try:
            req = urllib.request.Request(url, data=data, headers=hdr, method=method)
            kw = {'timeout': timeout}
            ctx = ssl_ctx()
            if ctx is not None:
                kw['context'] = ctx
            with urllib.request.urlopen(req, **kw) as rsp:
                body = rsp.read()
                enc = (rsp.headers.get('Content-Encoding') or '').lower()
                if 'gzip' in enc:
                    try:
                        body = gzip.decompress(body)
                    except Exception:
                        pass
                elif 'deflate' in enc:
                    try:
                        body = zlib.decompress(body)
                    except Exception:
                        try:
                            body = zlib.decompress(body, -zlib.MAX_WBITS)
                        except Exception:
                            pass
                status = rsp.getcode()
                if status in (429, 500, 502, 503, 504) and i < tries - 1:
                    last = (status, body)
                    continue
                return (status, body)
        except urllib.error.HTTPError as exc:
            try:
                body = exc.read()
            except Exception:
                body = b''
            last = (exc.code, body)
            if exc.code in (429, 500, 502, 503, 504) and i < tries - 1:
                continue
            return last
        except (socket.timeout, ssl.SSLError, urllib.error.URLError, OSError):
            last = (0, b'')
            continue
        except Exception:
            last = (0, b'')
            continue
    return last


def http_text(url, method='GET', headers=None, data=None, timeout=8.0,
              retries=2, charset='utf-8'):
    st, body = http(url, method, headers, data, timeout, retries)
    if not body:
        return st, ''
    try:
        return st, body.decode(charset, 'replace')
    except Exception:
        return st, body.decode('utf-8', 'replace')


def http_json(url, method='GET', headers=None, data=None, timeout=8.0, retries=2):
    st, txt = http_text(url, method, headers, data, timeout, retries)
    if not txt:
        return {}
    return loads(txt)


def http_cached(key, ttl, fn):
    hit = cache_get(key)
    if hit is not None:
        return hit
    value = fn()
    if value:
        cache_put(key, value, ttl)
    return value


def is_url(value):
    try:
        p = urllib.parse.urlparse(text(value))
        return p.scheme in ('http', 'https') and bool(p.netloc)
    except Exception:
        return False


_URL_SAFE = ":/?#[]@!$&'()*+,;=%~"


def safe_url(value):
    """urllib 不接受 URL 里的非 ASCII（中文文件名很常见）→ 百分号编码掉。"""
    u = text(value).strip()
    try:
        u.encode('ascii')
        return u
    except Exception:
        try:
            return urllib.parse.quote(u, safe=_URL_SAFE)
        except Exception:
            return u


_STREAM_RE = re.compile(r'\.(?:m3u8|mpd)$', re.I)
_MEDIA_RE = re.compile(r'\.(?:mp4|m3u8|mpd|flv|avi|mkv|ts|mov|wmv|webm|m4v)$', re.I)


def is_stream_url(url):
    if not is_url(url):
        return False
    return bool(_STREAM_RE.search(urllib.parse.urlparse(text(url)).path))


def is_media_url(url):
    if not is_url(url):
        return False
    return bool(_MEDIA_RE.search(urllib.parse.urlparse(text(url)).path))


# ============================================================================
# 纯 Python AES（128/256 CBC + 256 GCM）
# ============================================================================

def _xtime(a):
    a <<= 1
    return (a ^ 0x1B) & 0xFF if a & 0x100 else a


def _gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0x1B
        b >>= 1
    return r


_SBOX = None
_INV_SBOX = None


def _aes_tables():
    global _SBOX, _INV_SBOX
    if _SBOX is not None:
        return
    exp = [0] * 256
    log = [0] * 256
    x = 1
    for i in range(255):
        exp[i] = x
        log[x] = i
        x = _gmul(x, 0x03)
    sb = [0] * 256
    ib = [0] * 256
    for i in range(256):
        inv = 0 if i == 0 else exp[(255 - log[i]) % 255]
        t = inv
        s = inv
        for _ in range(4):
            s = ((s << 1) | (s >> 7)) & 0xFF
            t ^= s
        sb[i] = t ^ 0x63
        ib[sb[i]] = i
    _SBOX = bytes(sb)
    _INV_SBOX = bytes(ib)


def _expand_key(key):
    """支持 16(128)/24(192)/32(256) 字节密钥，返回轮密钥列表。"""
    _aes_tables()
    nk = len(key) // 4
    if nk not in (4, 6, 8):
        raise ValueError('bad aes key length')
    total = 4 * (nk + 7)
    w = [list(key[i * 4:i * 4 + 4]) for i in range(nk)]
    rcon = 1
    for i in range(nk, total):
        t = list(w[i - 1])
        if i % nk == 0:
            t = t[1:] + t[:1]
            t = [_SBOX[b] for b in t]
            t[0] ^= rcon
            rcon = _xtime(rcon)
        elif nk > 6 and i % nk == 4:
            t = [_SBOX[b] for b in t]
        w.append([w[i - nk][j] ^ t[j] for j in range(4)])
    return [sum(w[i:i + 4], []) for i in range(0, total, 4)]


def _shift_rows(state, encrypt):
    out = [0] * 16
    for r in range(4):
        for c in range(4):
            out[r + 4 * c] = state[r + 4 * ((c + (r if encrypt else -r)) % 4)]
    return out


def _mix_columns(state):
    out = state[:]
    for c in range(4):
        a = out[0 + 4 * c]
        b = out[1 + 4 * c]
        d = out[2 + 4 * c]
        e = out[3 + 4 * c]
        t = a ^ b ^ d ^ e
        out[0 + 4 * c] = a ^ t ^ _xtime(a ^ b)
        out[1 + 4 * c] = b ^ t ^ _xtime(b ^ d)
        out[2 + 4 * c] = d ^ t ^ _xtime(d ^ e)
        out[3 + 4 * c] = e ^ t ^ _xtime(e ^ a)
    return out


def _mul9(x):
    return _xtime(_xtime(_xtime(x))) ^ x


def _mul11(x):
    return _xtime(_xtime(_xtime(x))) ^ _xtime(x) ^ x


def _mul13(x):
    return _xtime(_xtime(_xtime(x))) ^ _xtime(_xtime(x)) ^ x


def _mul14(x):
    return _xtime(_xtime(_xtime(x))) ^ _xtime(_xtime(x)) ^ _xtime(x)


def _inv_mix_columns(state):
    out = state[:]
    for c in range(4):
        a = out[0 + 4 * c]
        b = out[1 + 4 * c]
        d = out[2 + 4 * c]
        e = out[3 + 4 * c]
        out[0 + 4 * c] = _mul14(a) ^ _mul11(b) ^ _mul13(d) ^ _mul9(e)
        out[1 + 4 * c] = _mul9(a) ^ _mul14(b) ^ _mul11(d) ^ _mul13(e)
        out[2 + 4 * c] = _mul13(a) ^ _mul9(b) ^ _mul14(d) ^ _mul11(e)
        out[3 + 4 * c] = _mul11(a) ^ _mul13(b) ^ _mul9(d) ^ _mul14(e)
    return out


def _enc_block(block, rk):
    nr = len(rk) - 1
    st = [s ^ k for s, k in zip(block, rk[0])]
    for r in range(1, nr):
        st = [_SBOX[b] for b in st]
        st = _shift_rows(st, True)
        st = _mix_columns(st)
        st = [s ^ k for s, k in zip(st, rk[r])]
    st = [_SBOX[b] for b in st]
    st = _shift_rows(st, True)
    return bytes([s ^ k for s, k in zip(st, rk[nr])])


def _dec_block(block, rk):
    nr = len(rk) - 1
    st = [s ^ k for s, k in zip(block, rk[nr])]
    for r in range(nr - 1, 0, -1):
        st = _shift_rows(st, False)
        st = [_INV_SBOX[b] for b in st]
        st = [s ^ k for s, k in zip(st, rk[r])]
        st = _inv_mix_columns(st)
    st = _shift_rows(st, False)
    st = [_INV_SBOX[b] for b in st]
    return bytes([s ^ k for s, k in zip(st, rk[0])])


def cbc_encrypt(key, iv, data, pad=True):
    rk = _expand_key(key)
    if pad:
        n = 16 - len(data) % 16
        data = data + bytes([n]) * n
    out = bytearray()
    prev = iv
    for i in range(0, len(data), 16):
        blk = bytes(a ^ b for a, b in zip(data[i:i + 16], prev))
        prev = _enc_block(blk, rk)
        out += prev
    return bytes(out)


def cbc_decrypt(key, iv, data, unpad=False):
    rk = _expand_key(key)
    out = bytearray()
    prev = iv
    end = len(data) - len(data) % 16
    for i in range(0, end, 16):
        blk = data[i:i + 16]
        out += bytes(a ^ b for a, b in zip(_dec_block(blk, rk), prev))
        prev = blk
    res = bytes(out)
    if unpad and res:
        n = res[-1]
        if 1 <= n <= 16 and res[-n:] == bytes([n]) * n:
            res = res[:-n]
    return res


_GCM_R = 0xE1000000000000000000000000000000


def _ghash_mul(x, y):
    z = 0
    for i in range(128):
        if (x >> (127 - i)) & 1:
            z ^= y
        if y & 1:
            y = (y >> 1) ^ _GCM_R
        else:
            y >>= 1
    return z


def _ghash(h, aad, ciphertext):
    y = 0
    for i in range(0, len(aad), 16):
        blk = int.from_bytes(aad[i:i + 16].ljust(16, b'\x00'), 'big')
        y = _ghash_mul(y ^ blk, h)
    for i in range(0, len(ciphertext), 16):
        blk = int.from_bytes(ciphertext[i:i + 16].ljust(16, b'\x00'), 'big')
        y = _ghash_mul(y ^ blk, h)
    lens = (len(aad) * 8).to_bytes(8, 'big') + (len(ciphertext) * 8).to_bytes(8, 'big')
    return _ghash_mul(y ^ int.from_bytes(lens, 'big'), h)


def gcm_encrypt(key, nonce, data, aad=b''):
    rk = _expand_key(key)
    h = int.from_bytes(_enc_block(b'\x00' * 16, rk), 'big')
    j0 = nonce + b'\x00\x00\x00\x01'
    counter = int.from_bytes(j0, 'big')
    out = bytearray()
    for i in range(0, len(data), 16):
        counter += 1
        ks = _enc_block(counter.to_bytes(16, 'big'), rk)
        chunk = data[i:i + 16]
        out += bytes(b ^ k for b, k in zip(chunk, ks))
    ciphertext = bytes(out)
    s = _ghash(h, aad, ciphertext)
    tag = (s ^ int.from_bytes(_enc_block(j0, rk), 'big')).to_bytes(16, 'big')[:16]
    return ciphertext, tag


def gcm_decrypt(key, nonce, data, tag=None, aad=b''):
    """tag 为 None 时按 data[-16:] 切分（部分客户端不校验 tag）。"""
    rk = _expand_key(key)
    if tag is None:
        tag = data[-16:]
        data = data[:-16]
    j0 = nonce + b'\x00\x00\x00\x01'
    counter = int.from_bytes(j0, 'big')
    out = bytearray()
    for i in range(0, len(data), 16):
        counter += 1
        ks = _enc_block(counter.to_bytes(16, 'big'), rk)
        chunk = data[i:i + 16]
        out += bytes(b ^ k for b, k in zip(chunk, ks))
    return bytes(out)


# ============================================================================
# P-256（secp256r1）ECDH
# ============================================================================

_P256_P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
_P256_A = _P256_P - 3
_P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
_P256_G = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296,
           0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5)


def _p256_double(pt):
    if pt is None:
        return None
    x, y = pt
    if y == 0:
        return None
    lam = (3 * x * x + _P256_A) * pow(2 * y, _P256_P - 2, _P256_P) % _P256_P
    x3 = (lam * lam - 2 * x) % _P256_P
    y3 = (lam * (x - x3) - y) % _P256_P
    return (x3, y3)


def _p256_add(p1, p2):
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2:
        if (y1 + y2) % _P256_P == 0:
            return None
        return _p256_double(p1)
    lam = (y2 - y1) * pow((x2 - x1) % _P256_P, _P256_P - 2, _P256_P) % _P256_P
    x3 = (lam * lam - x1 - x2) % _P256_P
    y3 = (lam * (x1 - x3) - y1) % _P256_P
    return (x3, y3)


def _p256_mul(k, pt):
    res = None
    addend = pt
    while k:
        if k & 1:
            res = _p256_add(res, addend)
        addend = _p256_double(addend)
        k >>= 1
    return res


def ecdh_keypair():
    priv = int.from_bytes(secrets.token_bytes(32), 'big') % (_P256_N - 1) + 1
    pub = _p256_mul(priv, _P256_G)
    raw = b'\x04' + pub[0].to_bytes(32, 'big') + pub[1].to_bytes(32, 'big')
    return priv, raw


def ecdh_shared_x(priv, server_pub):
    raw = bytes(server_pub or b'')
    if len(raw) == 65 and raw[0] == 4:
        pt = (int.from_bytes(raw[1:33], 'big'), int.from_bytes(raw[33:65], 'big'))
    elif len(raw) == 64:
        pt = (int.from_bytes(raw[:32], 'big'), int.from_bytes(raw[32:], 'big'))
    else:
        raise ValueError('bad server public key')
    shared = _p256_mul(priv, pt)
    if shared is None:
        raise ValueError('ecdh infinity')
    return shared[0].to_bytes(32, 'big')


# ============================================================================
# protobuf 裸编解码（T3 协议用）
# ============================================================================

def pb_varint(value):
    if value < 0:
        raise ValueError('negative varint')
    out = bytearray()
    while value >= 0x80:
        out.append((value & 0x7F) | 0x80)
        value >>= 7
    out.append(value)
    return bytes(out)


def pb_bytes(field, value):
    if isinstance(value, str):
        value = value.encode('utf-8')
    return pb_varint((field << 3) | 2) + pb_varint(len(value)) + value


def pb_var(field, value):
    return pb_varint(field << 3) + pb_varint(int(value))


def pb_read_varint(data, pos):
    value = 0
    shift = 0
    while pos < len(data) and shift < 70:
        b = data[pos]
        pos += 1
        value |= (b & 0x7F) << shift
        if b < 0x80:
            return value, pos
        shift += 7
    raise ValueError('bad varint')


def pb_decode(data):
    out = []
    pos = 0
    size = len(data or b'')
    while pos < size:
        key, pos = pb_read_varint(data, pos)
        field, wire = key >> 3, key & 7
        if field == 0:
            raise ValueError('field zero')
        if wire == 0:
            value, pos = pb_read_varint(data, pos)
        elif wire == 1:
            value = data[pos:pos + 8]
            pos += 8
        elif wire == 2:
            length, pos = pb_read_varint(data, pos)
            value = data[pos:pos + length]
            pos += length
        elif wire == 5:
            value = data[pos:pos + 4]
            pos += 4
        else:
            raise ValueError('wire %d' % wire)
        if pos > size:
            raise ValueError('truncated')
        out.append((field, wire, value))
    return out


def pb_field(data, field, wire=None):
    values = [v for f, w, v in pb_decode(data) if f == field and (wire is None or w == wire)]
    return values[-1] if values else None


def pb_fields(data, field, wire=None):
    return [v for f, w, v in pb_decode(data) if f == field and (wire is None or w == wire)]


def pb_str(data, field, default=''):
    value = pb_field(data, field, 2)
    if value is None:
        return default
    try:
        return value.decode('utf-8')
    except Exception:
        return default


def raw_deflate(data, level=6):
    c = zlib.compressobj(level, zlib.DEFLATED, wbits=-15, memLevel=8,
                         strategy=zlib.Z_DEFAULT_STRATEGY)
    return c.compress(data) + c.flush()


def raw_inflate(data):
    return zlib.decompress(data, -15)


def b64url_encode(raw):
    try:
        if isinstance(raw, str):
            raw = raw.encode('utf-8')
        return base64.urlsafe_b64encode(raw).decode('ascii').rstrip('=')
    except Exception:
        return ''


def b64url_decode(txt):
    try:
        s = text(txt)
        s += '=' * ((4 - len(s) % 4) % 4)
        return base64.urlsafe_b64decode(s.encode('ascii'))
    except Exception:
        return b''
# ============================================================================
# 云端自更新（可选，默认不启用）
#
#   原理：脚本 init 时后台拉一份「版本清单」，远端版本比本地新就下载整份
#   .py 覆盖自身文件；下次壳加载这个文件即是新代码（无需改配置、无需手动拷）。
#
#   开启方式：把 UPDATE_URL 填成清单地址（或 extend 里传 update_url）。
#   清单支持两种最省事的形态：
#     ① 纯文本，内容只有一行版本号，例如  20261105.1930
#        → 新脚本地址约定为「清单同目录 + 本文件名」，放同一个目录即可。
#     ② JSON，可指定任意下载地址与校验值：
#        {"version":"20261105.1930",
#         "url":"https://xx.com/tvbox/影探聚合.py",
#         "sha256":"…", "size":91234, "note":"修了找剧 503"}
#
#   安全阀：只接受 2xx、只接受体积 <= UPDATE_MAX_BYTES、只接受含
#   "class Spider" 的 Python 文本、sha256 对不上就放弃；写盘走
#   临时文件 + os.replace 原子替换，失败时旁挂 .new 不破坏旧文件。
# ============================================================================

UPDATE_MAX_BYTES = 4 * 1024 * 1024
SELF_NAME = 'Kishuto.py'

_UPDATE_LAST = {'ok': False, 'updated': False, 'version': CODE_VERSION,
                'msg': '', 'note': '', 'at': 0.0}


def code_version():
    return CODE_VERSION


def _ver_tuple(value):
    return tuple(int(x) for x in re.findall(r'\d+', text(value))[:4]) or (0,)


def version_newer(far, near):
    """far 是否比 near 新。"""
    a, b = _ver_tuple(far), _ver_tuple(near)
    n = max(len(a), len(b))
    return a + (0,) * (n - len(a)) > b + (0,) * (n - len(b))


def self_path():
    try:
        p = os.path.abspath(__file__)
        if os.path.isfile(p):
            return p
    except Exception:
        pass
    return ''


def self_name():
    p = self_path()
    return os.path.basename(p) if p else SELF_NAME


def parse_manifest(body):
    """→ {'version','url','sha256','note'}；纯文本清单只给 version。"""
    if isinstance(body, (bytes, bytearray)):
        try:
            body = bytes(body).decode('utf-8', 'replace')
        except Exception:
            return {}
    raw = text(body).lstrip('\ufeff').strip()
    if not raw:
        return {}
    if raw[:1] == '{':
        try:
            obj = loads(raw)
        except Exception:
            obj = None
        if isinstance(obj, dict):
            return {
                'version': text(obj.get('version') or obj.get('ver')),
                'url': text(obj.get('url') or obj.get('file') or obj.get('py')),
                'sha256': text(obj.get('sha256') or obj.get('hash')).lower(),
                'note': text(obj.get('note') or obj.get('desc')),
            }
    return {'version': raw.splitlines()[0].strip(), 'url': '',
            'sha256': '', 'note': ''}


def _write_self(path, blob):
    """原子替换自身文件。返回 (是否替换成功, 说明)。"""
    folder = os.path.dirname(path) or '.'
    tmp = os.path.join(folder, '.upd_%s.tmp' % uuid.uuid4().hex[:8])
    try:
        with open(tmp, 'wb') as fp:
            fp.write(blob)
            fp.flush()
            try:
                os.fsync(fp.fileno())
            except Exception:
                pass
    except Exception as exc:
        try:
            os.remove(tmp)
        except Exception:
            pass
        return False, 'write failed: %s' % exc
    try:
        bak = path + '.bak'
        try:
            with open(path, 'rb') as src, open(bak, 'wb') as dst:
                dst.write(src.read())
        except Exception:
            pass
        os.replace(tmp, path)
        return True, 'replaced'
    except Exception as exc:
        alt = path + '.new'
        try:
            os.replace(tmp, alt)
            return False, 'replace failed(%s), saved %s' % (exc, os.path.basename(alt))
        except Exception:
            try:
                os.remove(tmp)
            except Exception:
                pass
            return False, 'replace failed: %s' % exc


def _fetch_manifest(url):
    """带时间戳采样两次取版本较大的，都失败再回退原始地址。→ (manifest, status)"""
    sep = '&' if '?' in url else '?'
    got, status = [], 0
    for i in range(2):
        hit = '%s%st=%d' % (url, sep, int(time.time() * 1000) + i * 7)
        status, body = http(hit, timeout=8, retries=1,
                            headers={'Cache-Control': 'no-cache',
                                     'Pragma': 'no-cache'})
        if status == 200 and body:
            got.append(body)
    if not got:
        status, body = http(url, timeout=8, retries=1,
                            headers={'Cache-Control': 'no-cache',
                                     'Pragma': 'no-cache'})
        if status == 200 and body:
            got.append(body)
    best = {}
    for body in got:
        man = parse_manifest(body)
        ver = text(man.get('version'))
        if ver and (not best or version_newer(ver, text(best.get('version')))):
            best = man
    return best, status


def _blob_version(blob):
    m = re.search(rb"^CODE_VERSION = ['\"]([^'\"]*)", blob, re.M)
    return m.group(1).decode('utf-8', 'ignore') if m else ''


def check_update(url=''):
    """拉清单 → 需要就下载覆盖。返回结果 dict（绝不影响主流程）。"""
    url = text(url or UPDATE_URL)
    out = {'ok': False, 'updated': False, 'version': CODE_VERSION,
           'msg': '', 'note': '', 'at': time.time()}
    if not url:
        out['msg'] = 'no update url'
        return out
    try:
        dest = self_path()
        if not dest:
            out['msg'] = 'self path unknown'
            return out

        # 每轮都重新拉清单：CDN 边缘节点之间可能不同步（清单落后一版、
        # 脚本已是新版），死守一份旧清单会永远 sha 对不上。
        last = ''
        for attempt in range(3):
            if attempt:
                time.sleep(1.2 * attempt)
            man, status = _fetch_manifest(url)
            far = text(man.get('version'))
            if not far:
                last = 'manifest http %s' % status
                continue
            out['version'] = far
            out['note'] = man.get('note') or ''
            if not version_newer(far, CODE_VERSION):
                out['ok'] = True
                out['msg'] = 'up to date (%s)' % CODE_VERSION
                return out

            target_url = text(man.get('url'))
            cands = []
            if target_url:
                cands.append(target_url if is_url(target_url)
                             else urllib.parse.urljoin(url, target_url))
            # 清单没写地址 / 拼出来 404 时的兜底：同目录 ASCII 名、再退本地同名
            for name in ('Kishuto.py', self_name()):
                cands.append(urllib.parse.urljoin(url, name))
            digest = text(man.get('sha256')).lower()

            blob = b''
            seen = set()
            for cand in cands:
                if cand in seen:
                    continue
                seen.add(cand)
                sep = '&' if '?' in cand else '?'
                for hit in ('%s%st=%d' % (cand, sep, int(time.time() * 1000)), cand):
                    st2, body = http(hit, timeout=25, retries=1)
                    if st2 == 200 and body and b'class Spider' in body:
                        blob = body
                        break
            if not blob:
                last = 'download failed'
                continue
            if len(blob) > UPDATE_MAX_BYTES:
                out['msg'] = 'too large (%d)' % len(blob)
                return out

            if digest and hashlib.sha256(blob).hexdigest() != digest:
                # 清单落后一版时的兜底：只要脚本自身的版本号确实比本地新、
                # 且不比清单旧，就认可它（版本号是我们自己的单调时间戳）。
                bver = _blob_version(blob)
                if bver and version_newer(bver, CODE_VERSION) and \
                        not version_newer(far, bver):
                    out['version'] = bver
                    out['note'] = (out['note'] + ' / sha 兜底').strip(' /')
                    far = bver
                else:
                    last = 'sha256 mismatch'
                    continue

            done, info = _write_self(dest, blob)
            out['ok'] = True
            out['updated'] = done
            out['msg'] = ('updated %s -> %s, restart to apply'
                          % (CODE_VERSION, far)) if done else info
            return out
        out['msg'] = last or 'update failed'
        return out
    except Exception as exc:
        out['msg'] = 'error: %s' % exc
        return out

# ============================================================================
# 源 1：影探4K（cms.lyyytv.cn）—— 首页 / 分类 / 搜索 的数据来源
# ============================================================================

class YT4K(object):
    """影探4K。原脚本依赖 requests + pycryptodome，这里改为纯标准库实现。"""

    NAME = '影探'
    HOST = 'http://cms.lyyytv.cn'
    CMS_KEY = 'wP5bvxoc3yv7FoBQENFZuAF0EUYr4LTy'
    PARSE_API = 'http://fys.lyyytv.cn/api/index?appid=10001&videoUrl='
    PARSE_ID_WEB = 5      # 网页线路（腾讯/爱奇艺/芒果/优酷/B站…）
    PARSE_ID_4K = 6       # 4K 直链（ym4kjx 等，站点本身 404，需换链）
    HEADERS = {'User-Agent': 'okhttp/4.12.0'}
    PARSE_HEADERS = {'User-Agent': 'okhttp/4.12.0', 'Accept-Encoding': 'identity'}

    DEC_PREFIX = 'https://baidu.con/'
    PAGE_LIMIT = 20
    HOME_TTL = 6 * 3600
    PLAY_TTL = 120

    FILTER_NAMES = {
        'class': '类型', 'area': '地区', 'lang': '语言', 'year': '年份',
        'letter': '字母', 'by': '排序', 'sort': '顺序',
    }

    _B64_RE = re.compile(r'(?:[A-Za-z0-9+/]{4})*(?:[A-Za-z0-9+/]{2}==|[A-Za-z0-9+/]{3}=)?')
    _LDMAX_RE = re.compile(r'^https?://ldmax\.cooom/', re.I)
    _4K_HOST_RE = re.compile(
        r'(?:^|\.)(?:ym4kjx|hd4kjx|sd4kjx|mm4kjx|mv4kjx|vk4kjx)\.lyyytv\.cn$', re.I)

    def __init__(self, timeout=9.0):
        self.timeout = timeout

    # ---------- 基础 ----------
    def cms(self, path, params=None):
        query = urllib.parse.urlencode(params or {})
        url = '%s/api.php/app/%s?%s' % (self.HOST, path, query)
        key = 'yt:cms:%s' % url
        cached = cache_get(key)
        if cached is not None:
            return cached
        data = http_json(url, headers=self.HEADERS, timeout=self.timeout, retries=2)
        if not isinstance(data, dict) or not data:
            return {}
        code = data.get('code')
        if code is not None:
            try:
                ok = int(code) in (1, 200)
            except (TypeError, ValueError):
                ok = False
            if not ok:
                return {}
        cache_put(key, data, 60)
        return data

    # ---------- 解密 ----------
    def _unb64(self, value):
        clean = re.sub(r'\s+', '', text(value))
        if not clean or not self._B64_RE.fullmatch(clean):
            return None
        try:
            return base64.b64decode(clean)
        except Exception:
            return None

    def decrypt_lvdou(self, value):
        """lvdou+ 前缀：前 16 字节 key、后 16 字节 iv 的 AES/CBC/PKCS7（AES-128）。"""
        original = text(value)
        if not original.startswith('lvdou+') or not self.CMS_KEY:
            return original
        try:
            encrypted = self._unb64(original[6:])
            if not encrypted:
                return original
            key = self.CMS_KEY[:16].encode('utf-8')
            iv = self.CMS_KEY[16:32].encode('utf-8') if len(self.CMS_KEY) >= 32 else key
            plain = cbc_decrypt(key, iv, encrypted, unpad=True)
            result = plain.decode('utf-8', 'replace').strip()
            if result.startswith('http'):
                return result
        except Exception:
            pass
        return original

    def decrypt_ldmax(self, value, depth=0):
        """老加密：ldmax.cooom 前缀，key = 路径前 16 位反转。"""
        if depth > 5:
            return ''
        url = text(value)
        decoded = self._unb64(url)
        if decoded:
            url = re.sub(r'\s+', '', decoded.decode('utf-8', 'replace'))
        if not self._LDMAX_RE.match(url):
            return url
        path = self._LDMAX_RE.sub('', url)
        if len(path) <= 16:
            return ''
        try:
            key = path[:16][::-1].encode('utf-8')
            encrypted = self._unb64(path[16:])
            if not encrypted or len(encrypted) % 16:
                return ''
            plain = bytearray(cbc_decrypt(key, key, encrypted))
            pad = plain[-1] if plain else 0
            if 0 < pad <= 16:
                del plain[-pad:]
            result = bytes(plain).decode('utf-8', 'replace').strip()
            return self.decrypt_ldmax(result, depth + 1) \
                if self._LDMAX_RE.match(result) else result
        except Exception:
            return ''

    def resolve_parse(self, body):
        """解析响应：JSON 包裹取 url；baidu.con 前缀走 AES；否则视为明文。"""
        body = text(body)
        if not body:
            return ''
        candidate = body
        if body.startswith('{'):
            parsed = loads(body)
            for key in ('url', 'playUrl', 'link'):
                if isinstance(parsed, dict) and parsed.get(key):
                    candidate = text(parsed[key])
                    break
            else:
                inner = as_dict(as_dict(parsed).get('data'))
                for key in ('url', 'playUrl', 'link'):
                    if inner.get(key):
                        candidate = text(inner[key])
                        break
        if not candidate.startswith(self.DEC_PREFIX):
            return candidate

        rest = candidate[len(self.DEC_PREFIX):]
        if len(rest) <= 16:
            return ''
        key = rest[:16].encode('utf-8')
        cipher_b64 = rest[16:]
        try:
            encrypted = base64.b64decode(cipher_b64, validate=False)
            result = cbc_decrypt(key, key, encrypted, unpad=True).decode('utf-8', 'replace').strip()
            if result.startswith('http'):
                return result
        except Exception:
            pass
        try:
            raw = cipher_b64.encode('latin-1', errors='ignore')
            if raw and len(raw) % 16 == 0:
                result = cbc_decrypt(key, key, raw, unpad=True).decode('utf-8', 'replace').strip()
                if result.startswith('http'):
                    return result
        except Exception:
            pass
        return ''

    def parse_url(self, raw, parse_id):
        if not raw:
            return ''
        target = '%s%s&parsesId=%d' % (
            self.PARSE_API, urllib.parse.quote(raw, safe="!'()*"), parse_id)
        st, txt = http_text(target, headers=self.PARSE_HEADERS, timeout=20, retries=2)
        if st and st < 400 and txt:
            resolved = self.resolve_parse(txt)
            if resolved and resolved.startswith('http'):
                return resolved
        return ''

    # ---------- 类型判断 ----------
    def is_4k_source(self, url):
        if not is_url(url):
            return False
        host = (urllib.parse.urlparse(text(url)).hostname or '').lower()
        if host and self._4K_HOST_RE.search(host):
            return True
        return is_media_url(url) and not is_stream_url(url)

    # ---------- 列表 ----------
    @staticmethod
    def _paginate(data, page):
        lst = as_list(data.get('list'))
        try:
            limit = int(data.get('limit') or 0)
        except (TypeError, ValueError):
            limit = 0
        if limit <= 0:
            limit = YT4K.PAGE_LIMIT
        try:
            pagecount = int(data.get('pagecount') or 0)
        except (TypeError, ValueError):
            pagecount = 0
        if pagecount <= 0:
            pagecount = page + (1 if len(lst) >= limit else 0)
        try:
            total = int(data.get('total'))
        except (TypeError, V