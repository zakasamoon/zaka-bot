#!/usr/bin/env python3
"""
ZakaDesk demo bot - the Night algo and the Volume spike strategy + the demo account, running 24/7 on your own computer.

 * Uses only the Python standard library (no pip packages).
 * Reads public MEXC candles (no API key, nothing is ever sent to MEXC, no real order is placed).
 * Takes every Night-range signal and every Volume-spike trade by itself with fake money (see zaka_bot_config.json; "strategies" chooses which),
   keeps the account in zaka_demo_state.json and shows it at http://127.0.0.1:8766 .
 * ZakaDesk (Position tab > Demo account) also shows this account when the bot is running.

Run:   python zaka_demo_bot.py          (or double-click start_bot.bat)
Cloud: python zaka_demo_bot.py --once   (one check, then exit: used by the GitHub Actions workflow, see CLOUD_SETUP.txt)
Reset: python zaka_demo_bot.py --reset  (deletes the demo account and starts again)
"""
import json, os, sys, time, math, threading, urllib.request, urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HERE = os.path.dirname(os.path.abspath(__file__))
CONF = os.path.join(HERE, 'zaka_bot_config.json')
STATE = os.path.join(HERE, 'zaka_demo_state.json')
PUBLIC = os.path.join(HERE, 'public_state.json')      # what ZakaDesk reads when the bot runs in the cloud
DEFAULT = {
    "symbols": ["BTCUSDT", "ETHUSDT", "SOLUSDT"],   # pairs to follow, MEXC spot names
    "timeframe": "15m",                              # chart timeframe the rules run on: 1m 5m 15m 30m 1h 4h
    "balance": 1000.0,                               # demo start balance (USDT)
    "risk_percent": 1.0,                             # risk per trade, % of the current balance
    "fee_percent": 0.05,                             # fee per side, % of the position
    "night_start_hour": 1,                           # PKT, start of the night window
    "night_end_hour": 5,                             # PKT, end of the window = entries start
    "start_from": "now",                             # "now" = only new signals, "history" = also the signals of the last days
    "history_days": 6,                               # days of candles used for every calculation
    "poll_seconds": 30,
    "port": 8766,
    "line_close_percent": 50,                        # every line-crossing signal needs at least this % of the candle's range beyond the line (0 = off)
    "strategies": ["night", "volspike"],             # which strategies trade the demo account: "night" and/or "volspike"
    "vs": {                                          # the Volume spike strategy (always on 1-minute candles)
        "symbols": [],                               # pairs for it; empty = the same pairs as above
        "timeframe": "1m",
        "multiple": 10,                              # spike = green candle with volume above this many times the biggest 1-minute volume of the look-back days
        "lookback_days": 3,
        "scan_days": 10,                             # how many days back a spike can be found (its lines live until the next spike or until it is older than this)
        "stop_buffer_percent": 10,                   # stop = this % of the spike candle's height beyond the opposite line (below its low for a buy, above its high for a sell)
        "recover_after": 4                           # after more than this many unrecovered losses (in R) the next trade closes when it has won them all back
    }
}
TF = {'1m': 60, '5m': 300, '15m': 900, '30m': 1800, '1h': 3600, '4h': 14400}
IV = {'1m': '1m', '5m': '5m', '15m': '15m', '30m': '30m', '1h': '60m', '4h': '4h'}
LAD = [4, 6, 8, 12, 16, 20, 28, 40, 55]
LADW = [0.4] + [0.075] * 8                          # share of the position closed at each target: 40% at the first, the rest equally
API = 'https://api.mexc.com'

# ---------------------------------------------------------------- the Night algo (night range mode), a port of the ZakaDesk engine
def pkt_day(t):
    return (t + 18000) // 86400 * 86400 - 18000

def sess_of(t, h0, h1):
    D = pkt_day(t); o = t - D
    if o >= h1 * 3600: return D
    if o < h0 * 3600: return D - 86400
    return None

def net_r(g):
    """net result in R of a finished trade (None while it is open)"""
    if g['res'] == 'open': return None
    if not g.get('ladder'): return g['rr'] if g['res'] == 'win' else -1.0
    n = len(g['tps']); hit = n if g['res'] == 'win' else g['hits']
    v = sum(g['mult'][k] * LADW[k] for k in range(hit)); rem = sum(LADW[hit:])
    er = g['mult'][0] if hit >= 3 else (0.0 if hit >= 1 else -1.0)
    return v + rem * er

def line_share(k, line, d):
    """share (0..1) of a candle's full range (high to low) that lies beyond a line"""
    r = k['high'] - k['low']
    if not r > 0: return 1.0
    return max(0.0, (k['high'] - max(k['low'], line)) if d > 0 else (min(k['high'], line) - k['low'])) / r

def build(c, days, h0, h1, lpct=50.0):
    """c: closed candles [{time,open,high,low,close}], days: {PKT midnight: {'vah':high,'val':low}} -> list of sessions with their trades"""
    out = []; cur = None; sess_at = [None] * len(c)
    for i, k in enumerate(c):
        D = sess_of(k['time'], h0, h1)
        if D is None: cur = None; continue
        if cur is None or cur['D'] != D:
            cur = {'D': D, 'i0': i, 'i1': i, 'prof': None, 'setups': [], 'sigs': []}; out.append(cur)
        else: cur['i1'] = i
        sess_at[i] = cur
    for s in out:
        P = days.get(s['D'])
        if not P: continue
        s['prof'] = P
        if P['vah'] > P['val']:
            s['setups'] = [{'n': 3, 'dir': 1, 'lvl': P['vah']}, {'n': 4, 'dir': -1, 'lvl': P['val']}]
    used = set(); N = len(c)

    def cross_kind(st, i):
        if i < 1 or i >= N: return 0
        k = c[i]; pv = c[i - 1]['close']
        if (pv <= st['lvl'] and k['close'] > st['lvl']) if st['dir'] > 0 else (pv >= st['lvl'] and k['close'] < st['lvl']):
            return 1 if line_share(k, st['lvl'], st['dir']) >= lpct / 100.0 - 1e-9 else 0      # a close across the line only counts with enough of the candle beyond it
        pierce = (pv <= st['lvl'] and k['high'] > st['lvl'] and k['close'] <= st['lvl']) if st['dir'] > 0 else (pv >= st['lvl'] and k['low'] < st['lvl'] and k['close'] >= st['lvl'])
        if not pierce or i + 1 >= N: return 0
        b = c[i + 1]
        edge = max(k['open'], k['close']) if st['dir'] > 0 else min(k['open'], k['close'])
        ok = (b['high'] <= k['high'] and b['low'] >= edge) if st['dir'] > 0 else (b['low'] >= k['low'] and b['high'] <= edge)
        return 2 if ok else 0

    def a_range(s, t):
        return range(t - 1, max(s['i0'], t - 60) - 1, -1)

    def cons(st, s, t):
        d = st['dir']
        for a in a_range(s, t):
            if cross_kind(st, a) != 1: continue
            A = c[a]; B = c[a + 1]
            slv = min(st['lvl'], A['low']) if d > 0 else max(st['lvl'], A['high'])
            if (B['close'] > B['open']) if d > 0 else (B['close'] < B['open']): continue
            ok = True; ext = B['high'] if d > 0 else B['low']
            for j in range(a + 1, t + 1):
                q = c[j]
                if (q['close'] <= st['lvl'] or q['low'] <= slv) if d > 0 else (q['close'] >= st['lvl'] or q['high'] >= slv):
                    ok = False; break
                key = 'c|%d|%d' % (st['n'], a)
                if j > a + 1 and ((q['close'] > ext) if d > 0 else (q['close'] < ext)) and j == t and key not in used:
                    return {'a': a, 'slv': slv, 'status': 'enter', 'key': key}
                ext = max(ext, q['high']) if d > 0 else min(ext, q['low'])
            if ok and ('c|%d|%d' % (st['n'], a)) not in used: return {'a': a, 'slv': slv, 'status': 'wait'}
        return None

    def rev(st, s, t):
        d = st['dir']; r = -d
        for a in a_range(s, t):
            if cross_kind(st, a) != 1: continue
            j = -1; ex = c[a]['high'] if d > 0 else c[a]['low']
            for k in range(a + 1, t + 1):
                if ((c[k]['close'] < st['lvl']) if d > 0 else (c[k]['close'] > st['lvl'])) and line_share(c[k], st['lvl'], r) >= lpct / 100.0 - 1e-9: j = k; break      # the candle that closes back must also have enough of its range beyond the line
                ex = max(ex, c[k]['high']) if d > 0 else min(ex, c[k]['low'])
            if j < 0: continue
            slv = c[a]['high'] if d > 0 else c[a]['low']      # stop: beyond the crossing candle's high (sell) / low (buy)
            key = 'r|%d|%d' % (st['n'], a)
            if key in used: return None
            if t == j: return {'a': a, 'slv': slv, 'status': 'wait', 'cons': False}
            B = c[j + 1]
            clean = (B['close'] > B['open'] and B['low'] > st['lvl']) if r > 0 else (B['close'] < B['open'] and B['high'] < st['lvl'])
            if clean:
                if t == j + 1 and ((B['low'] > slv) if r > 0 else (B['high'] < slv)):
                    return {'a': a, 'slv': slv, 'status': 'enter', 'cons': False, 'key': key}
                return None
            ext = B['high'] if r > 0 else B['low']
            for k in range(j + 1, t + 1):
                q = c[k]
                if (q['close'] <= st['lvl'] or q['low'] <= slv) if r > 0 else (q['close'] >= st['lvl'] or q['high'] >= slv): return None
                if k > j + 1 and ((q['close'] > ext) if r > 0 else (q['close'] < ext)) and k == t and k >= j + 3:
                    return {'a': a, 'slv': slv, 'status': 'enter', 'cons': True, 'key': key}
                ext = max(ext, q['high']) if r > 0 else min(ext, q['low'])
            return {'a': a, 'slv': slv, 'status': 'wait', 'cons': True}
        return None

    def rng(st, s, t):
        d = st['dir']
        for a in a_range(s, t):
            if cross_kind(st, a) != 1: continue
            B = c[a + 1]
            if (B['close'] > B['open'] and B['low'] > st['lvl']) if d > 0 else (B['close'] < B['open'] and B['high'] < st['lvl']): continue
            ext = B['high'] if d > 0 else B['low']; ok = True
            for j in range(a + 1, t + 1):
                q = c[j]
                if (q['close'] <= st['lvl']) if d > 0 else (q['close'] >= st['lvl']): ok = False; break
                key = 'g|%d|%d' % (st['n'], a)
                if j > a + 1 and ((q['close'] > ext) if d > 0 else (q['close'] < ext)) and j == t and j >= a + 3 and key not in used:
                    return {'a': a, 'slv': st['lvl'], 'status': 'enter', 'key': key}
                ext = max(ext, q['high']) if d > 0 else min(ext, q['low'])
            if ok and ('g|%d|%d' % (st['n'], a)) not in used: return {'a': a, 'slv': st['lvl'], 'status': 'wait'}
        return None

    def rej_at(s, t):
        """touch rejection (S7/S8): the wick touches a night line without closing beyond it, the next candle has the opposite colour and does not touch the line;
        only taken when the other line (the target) is at least 1:4 away"""
        q = c[t]
        if s['prof'] and t >= 2 and t - 1 >= s['i0']:
            hi = s['prof']['vah']; lo = s['prof']['val']; A = c[t - 1]; pv = c[t - 2]
            for d in (-1, 1):
                line = hi if d < 0 else lo
                if d < 0: ok = A['high'] >= hi and A['close'] <= hi and pv['close'] <= hi and q['close'] < q['open'] and q['high'] < hi and q['close'] > lo
                else: ok = A['low'] <= lo and A['close'] >= lo and pv['close'] >= lo and q['close'] > q['open'] and q['low'] > lo and q['close'] < hi
                if not ok: continue
                slv = A['high'] if d < 0 else A['low']; dist = abs(q['close'] - slv); tp = lo if d < 0 else hi
                if not dist > 0 or abs(tp - q['close']) / dist < 4 - 1e-9: continue
                return {'i': t - 1, 'rej': True, 'st': {'n': 7 if d < 0 else 8, 'dir': d, 'lvl': line}, 'slv': slv, 'dist': dist, 'tp': tp, 'rr': abs(tp - q['close']) / dist}
        return None

    def rev_at(s, t):
        q = c[t]
        for st in s['setups']:
            r = rev(st, s, t)
            if not r or r['status'] != 'enter': continue
            dist = abs(q['close'] - r['slv'])
            if not dist > 0: continue
            return {'i': r['a'], 'rev': True, 'key': r['key'], 'st': {'n': 5 if st['dir'] > 0 else 6, 'dir': -st['dir'], 'lvl': st['lvl']}, 'slv': r['slv'], 'dist': dist}
        return None

    def entry_at(s, t):
        q = c[t]
        for kind in (2, 1):
            i = t - 2 if kind == 2 else t - 1
            if i < s['i0']: continue
            for st in s['setups']:
                if cross_kind(st, i) != kind: continue
                if (q['low'] <= st['lvl']) if st['dir'] > 0 else (q['high'] >= st['lvl']): continue
                if (not q['close'] > q['open']) if st['dir'] > 0 else (not q['close'] < q['open']): continue
                k = c[i]
                slv = min(st['lvl'], k['low']) if st['dir'] > 0 else max(st['lvl'], k['high'])
                dist = abs(q['close'] - slv)
                if not dist > 0: continue
                return {'i': i, 'st': st, 'slv': slv, 'dist': dist, 'wick': kind == 2}
        rj = rej_at(s, t)
        if rj: return rj
        for st in s['setups']:
            r = cons(st, s, t)
            if not r or r['status'] != 'enter': continue
            dist = abs(q['close'] - r['slv'])
            if not dist > 0: continue
            return {'i': r['a'], 'key': r['key'], 'st': st, 'slv': r['slv'], 'dist': dist, 'cons': True}
        for st in s['setups']:
            r = rng(st, s, t)
            if not r or r['status'] != 'enter': continue
            dist = abs(q['close'] - r['slv'])
            if not dist > 0: continue
            return {'i': r['a'], 'key': r['key'], 'st': st, 'slv': r['slv'], 'dist': dist, 'cons': True, 'rng': True}
        rv = rev_at(s, t)
        if rv: return rv
        return None

    def mk_trade(e, z, s, t):
        entry = z['close']; rej = bool(e.get('rej')); rr = e['rr'] if rej else LAD[2]
        T = {'i': t, 'time': z['time'], 'n': e['st']['n'], 'dir': e['st']['dir'], 'entry': entry, 'sl': e['slv'], 'risk': e['dist'],
             'tp': e['tp'] if rej else entry + e['st']['dir'] * rr * e['dist'], 'rr': rr, 'res': 'open', 'end': None, 'D': s['D'], 'rej': rej, 'rev': bool(e.get('rev'))}
        if e['st']['n'] in (3, 4): T['var'] = 'R' if e.get('rng') else 'C' if e.get('cons') else 'W' if e.get('wick') else ''      # S3/S4: '' = the clean entry
        s['sigs'].append(T)
        if e.get('key'): used.add(e['key'])
        if not rej:
            T['ladder'] = True; T['mult'] = LAD; T['tps'] = [entry + e['st']['dir'] * m * e['dist'] for m in LAD]
            T['hits'] = 0; T['cur'] = T['sl']; T['tp'] = T['tps'][2]
        return T

    L = None; last_s = None; carries = []; twins = []
    for t in range(N):
        z = c[t]; s = sess_at[t]
        if s is not None and s is not last_s:
            if L is not None: carries.append(L); L = None
            last_s = s
        ended = []
        for tr in ([L] if L is not None else []) + carries + twins:
            if tr['res'] != 'open' or t <= tr['i']: continue
            stp = tr.get('cur', tr['sl'])
            hs = (z['low'] <= stp) if tr['dir'] > 0 else (z['high'] >= stp)
            if tr.get('ladder'):
                if hs:
                    tr['res'] = 'partial' if tr['hits'] > 0 else 'loss'; tr['end'] = t; ended.append(tr); continue
                while tr['hits'] < len(tr['tps']) and ((z['high'] >= tr['tps'][tr['hits']]) if tr['dir'] > 0 else (z['low'] <= tr['tps'][tr['hits']])): tr['hits'] += 1
                if tr['hits'] >= len(tr['tps']):
                    tr['res'] = 'win'; tr['end'] = t; ended.append(tr); continue
                if tr['hits'] >= 3: tr['cur'] = tr['tps'][0]
                elif tr['hits'] >= 1: tr['cur'] = tr['entry']
                continue
            ht = (z['high'] >= tr['tp']) if tr['dir'] > 0 else (z['low'] <= tr['tp'])
            if hs or ht: tr['res'] = 'loss' if hs else 'win'; tr['end'] = t; ended.append(tr)
        for tr in ended:
            if tr is L: L = None
        carries = [x for x in carries if x['res'] == 'open']; twins = [x for x in twins if x['res'] == 'open']
        if L is None and s is not None and s['prof']:
            e = entry_at(s, t)
            if e: L = mk_trade(e, z, s, t)
        # twin signals: S7/S8 and S5/S6 look alike and often fire together; when one is running the other one is taken as well (same direction)
        if s is not None and s['prof']:
            run = [x for x in ([L] if L is not None else []) + carries + twins if x['res'] == 'open' and (x.get('rej') or x.get('rev')) and x['D'] == s['D']]
            for base in list(run):
                want = 'rev' if base.get('rej') else 'rej'
                if any(x['dir'] == base['dir'] and x.get(want) for x in run): continue
                e2 = rev_at(s, t) if want == 'rev' else rej_at(s, t)
                if e2 and e2['st']['dir'] == base['dir']:
                    T = mk_trade(e2, z, s, t); twins.append(T); run.append(T)
    return out


# ---------------------------------------------------------------- the Volume spike strategy (1-minute candles), a port of the ZakaDesk engine
def vs_spikes(cs, lb_s, mult, first_t=0):
    """indexes of SPIKE candles: green, and volume > mult x the biggest single volume of the previous lb_s seconds"""
    from collections import deque
    dq = deque(); out = []; left = 0
    for i, k in enumerate(cs):
        while left < i and cs[left]['time'] < k['time'] - lb_s: left += 1
        while dq and dq[0] < left: dq.popleft()
        if dq and k['time'] >= first_t and (k['time'] - cs[left]['time']) >= lb_s * 0.9:
            mx = cs[dq[0]]['volume']
            if mx > 0 and k['close'] > k['open'] and k['volume'] > mult * mx: out.append(i)
        while dq and cs[dq[-1]]['volume'] <= k['volume']: dq.pop()
        dq.append(i)
    return out

def vs_build(cs, spikes, buf_pct=10.0, thr=4.0, lpct=50.0):
    """The lines of a spike candle (high = buy line, low = sell line) stay until the next spike. A candle that CLOSES beyond a line opens a trade
    at its close (stop a little beyond the opposite line). Every close opens a new trade (one at a time per line); once more than `thr` R of losses are
    unrecovered, the next trade has ONE target = that many R and closes when the losses are won back; otherwise the 9-target ladder is used.
    A new spike starts everything again (trades still running keep running)."""
    sp = set(spikes); out = []; opn = []; deficit = 0.0; act = None; last = {}
    for j, z in enumerate(cs):
        ended = []
        for tr in opn:
            if tr['i'] >= j: continue
            stp = tr.get('cur', tr['sl'])
            hs = (z['low'] <= stp) if tr['dir'] > 0 else (z['high'] >= stp)
            if tr.get('ladder'):
                if hs:
                    tr['res'] = 'partial' if tr['hits'] > 0 else 'loss'; tr['end'] = j; ended.append(tr); continue
                while tr['hits'] < len(tr['tps']) and ((z['high'] >= tr['tps'][tr['hits']]) if tr['dir'] > 0 else (z['low'] <= tr['tps'][tr['hits']])): tr['hits'] += 1
                if tr['hits'] >= len(tr['tps']):
                    tr['res'] = 'win'; tr['end'] = j; ended.append(tr); continue
                if tr['hits'] >= 3: tr['cur'] = tr['tps'][0]
                elif tr['hits'] >= 1: tr['cur'] = tr['entry']
                continue
            ht = (z['high'] >= tr['tp']) if tr['dir'] > 0 else (z['low'] <= tr['tp'])
            if hs or ht: tr['res'] = 'loss' if hs else 'win'; tr['end'] = j; ended.append(tr)
        for tr in ended:
            opn.remove(tr); deficit = max(0.0, deficit - net_r(tr))
        if j in sp:
            act = {'id': j, 'H': z['high'], 'L': z['low']}; deficit = 0.0; last = {}; continue
        if act is None: continue
        prev = cs[j - 1]; rng = act['H'] - act['L']
        for d in (1, -1):
            line = act['H'] if d > 0 else act['L']
            if not ((z['close'] > line) if d > 0 else (z['close'] < line)): continue
            if line_share(z, line, d) < lpct / 100.0 - 1e-9: continue
            if any(tr['dir'] == d and tr['sig'] == act['id'] for tr in opn): continue
            pb = (prev['close'] > line) if d > 0 else (prev['close'] < line)
            lt = last.get(d)
            if pb and not (lt is not None and lt['res'] == 'loss'): continue
            entry = z['close']; buf = max(buf_pct / 100.0 * rng, entry * 0.0002)
            sl = act['L'] - buf if d > 0 else act['H'] + buf; risk = abs(entry - sl)      # stop just beyond the OPPOSITE line (below the spike low for a buy, above the spike high for a sell)
            if not risk > 0: continue
            T = {'i': j, 'time': z['time'], 'n': 11 if d > 0 else 12, 'dir': d, 'entry': entry, 'sl': sl, 'risk': risk, 'res': 'open', 'end': None,
                 'sig': act['id'], 'line': line, 'D': cs[act['id']]['time']}
            if deficit > thr:
                T.update(rec=True, rr=deficit, tp=entry + d * deficit * risk, need=deficit)
            else:
                T.update(ladder=True, mult=LAD, tps=[entry + d * m * risk for m in LAD], hits=0, cur=sl, rr=LAD[2]); T['tp'] = T['tps'][2]
            opn.append(T); out.append(T); last[d] = T
    return out

# ---------------------------------------------------------------- MEXC public candles
def http_json(url, tries=4):
    err = None
    for k in range(tries):
        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'zaka-demo-bot'})
            with urllib.request.urlopen(req, timeout=20) as r: return json.loads(r.read().decode())
        except Exception as e:
            err = e; time.sleep(0.6 * (k + 1) ** 2)
    raise err

def fetch_range(sym, interval, start_ms, end_ms, step_s):
    W = 500 * step_s * 1000; seen = {}; a = start_ms
    while a <= end_ms:
        b = min(end_ms, a + W - 1)
        j = http_json('%s/api/v3/klines?symbol=%s&interval=%s&startTime=%d&endTime=%d&limit=500' % (API, sym, interval, a, b))
        if isinstance(j, list):
            for k in j:
                if start_ms <= k[0] <= end_ms: seen[k[0]] = k
        a += W
    return [{'time': t // 1000, 'open': float(seen[t][1]), 'high': float(seen[t][2]), 'low': float(seen[t][3]), 'close': float(seen[t][4]), 'volume': float(seen[t][5])} for t in sorted(seen)]

def night_profile(sym, D, h0, h1):
    """high and low of the night window; 5m candles first, then 15m, then 1h if the exchange has no older small candles"""
    for iv, st in (('5m', 300), ('15m', 900), ('60m', 3600)):
        cs = fetch_range(sym, iv, (D + h0 * 3600) * 1000, (D + h1 * 3600) * 1000 - 1, st)
        win = [k for k in cs if D + h0 * 3600 <= k['time'] < D + h1 * 3600]
        if len(win) >= (h1 - h0) * 3600 / st * 0.6 and len(win) >= 3:
            hi = max(k['high'] for k in win); lo = min(k['low'] for k in win)
            if hi > lo: return {'vah': hi, 'val': lo}
    return None

# ---------------------------------------------------------------- the demo account
def load_json(path, default):
    try:
        with open(path, 'r', encoding='utf-8') as f: return json.load(f)
    except Exception: return default

def save_json(path, obj):
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f: json.dump(obj, f, indent=1)
    os.replace(tmp, path)

def calc(D):
    """balance, equity, closed and open trades (same maths as the Demo account in ZakaDesk)"""
    ev = []; bal = D['bal0']; peak = bal; dd = 0.0; wins = 0; eq = [[0, bal]]; closed = []; opened = []
    for r in D['led'].values():
        ev.append((r['t'], 1, r['key']))
        if r['net'] is not None: ev.append(((r['ct'] or r['t']), 0, r['key']))
        else: opened.append(r)
    ev.sort(key=lambda e: (e[0], e[1]))
    for t, kind, key in ev:
        r = D['led'][key]
        if kind == 1: r['amt'] = bal * D['risk'] / 100; continue
        fee_r = 2 * D['fee'] / 100 * r['entry'] / r['risk'] if r['risk'] > 0 else 0
        r['feeR'] = fee_r; r['pnl'] = (r['net'] - fee_r) * r['amt']; bal += r['pnl']
        if r['pnl'] > 0: wins += 1
        peak = max(peak, bal); dd = max(dd, (peak - bal) / peak * 100); eq.append([t, bal]); closed.append(r)
    return {'bal0': D['bal0'], 'balance': bal, 'wins': wins, 'maxDD': dd, 'equity': eq, 'closed': closed, 'open': opened,
            'risk': D['risk'], 'fee': D['fee'], 'start': D['start']}

class Bot:
    def __init__(self, conf):
        self.c = conf; self.lock = threading.Lock(); self.profiles = {}; self.status = 'starting'; self.last_poll = 0; self.vs_cache = {}
        self.D = load_json(STATE, None)
        if not self.D:
            self.D = {'bal0': conf['balance'], 'risk': conf['risk_percent'], 'fee': conf['fee_percent'],
                      'start': 0 if conf['start_from'] == 'history' else int(time.time()), 'led': {}}
            save_json(STATE, self.D)
        self.D['risk'] = conf['risk_percent']; self.D['fee'] = conf['fee_percent']

    def profile(self, sym, D, h0, h1):
        key = (sym, D, h0, h1)
        if key in self.profiles and self.profiles[key] is not None: return self.profiles[key]
        if key in self.profiles and time.time() - self.profiles[key + ('t',)] < 600: return None
        p = night_profile(sym, D, h0, h1); self.profiles[key] = p; self.profiles[key + ('t',)] = time.time()
        return p

    def poll_symbol(self, sym):
        cf = self.c; h0 = cf['night_start_hour']; h1 = cf['night_end_hour']; tf = cf['timeframe']; step = TF[tf]
        now = time.time()
        # the window starts between two sessions (inside the quiet hours of a night), so every session in it is complete
        w0 = pkt_day(now - cf['history_days'] * 86400) + h0 * 3600
        with self.lock:
            olds = [r['t'] for r in self.D['led'].values() if r['sym'] == sym and r['net'] is None]
        if olds: w0 = min(w0, pkt_day(min(olds)) - 86400 + h0 * 3600)      # a trade is still open: keep its whole session in the window
        cs = fetch_range(sym, IV[tf], int(w0 * 1000), int(now * 1000), step)
        cs = [k for k in cs if k['time'] + step <= now]                 # closed candles only
        if len(cs) < 10: return 0
        days = {}
        for D in sorted({sess_of(k['time'], h0, h1) for k in cs} - {None}):
            if now < D + h1 * 3600 + 60: continue
            p = self.profile(sym, D, h0, h1)
            if p: days[D] = p
        sessions = build(cs, days, h0, h1, cf.get('line_close_percent', 50)); changed = 0
        with self.lock:
            for s in sessions:
                for g in s['sigs']:
                    if g['time'] < self.D['start']: continue
                    key = '%s|%d|%d' % (sym, g['time'], g['n']); net = net_r(g)
                    ct = cs[g['end']]['time'] if g['end'] is not None else None
                    r = self.D['led'].get(key)
                    new = {'key': key, 'sym': sym, 'dir': g['dir'], 'n': g['n'], 't': g['time'], 'entry': g['entry'], 'sl': g['sl'], 'risk': g['risk'],
                           'res': g['res'], 'hits': g.get('hits', 0), 'net': net, 'ct': ct, 'var': g.get('var', '')}
                    if r is None or any(r.get(k) != new[k] for k in ('res', 'hits', 'net', 'ct')):
                        if r is not None: new['amt'] = r.get('amt')
                        self.D['led'][key] = new; changed += 1
            if changed: save_json(STATE, self.D)
        return changed


    def vs_symbols(self):
        return [x for x in (self.c['vs'].get('symbols') or self.c['symbols'])]

    def poll_vs(self, sym):
        v = self.c['vs']; tf = v['timeframe']; step = TF[tf]; now = time.time()
        lb = v['lookback_days'] * 86400; scan = v['scan_days'] * 86400; start = now - lb - scan
        cache = self.vs_cache.get(sym) or []
        if cache and cache[0]['time'] <= start + 3 * step and cache[-1]['time'] > now - 3600:
            new = fetch_range(sym, IV[tf], int((cache[-1]['time'] - 3 * step) * 1000), int(now * 1000), step)
            m = {k['time']: k for k in cache}
            for k in new: m[k['time']] = k
            cache = [m[t] for t in sorted(m) if t >= start]
        else:
            cache = fetch_range(sym, IV[tf], int(start * 1000), int(now * 1000), step)
        self.vs_cache[sym] = cache
        cs = [k for k in cache if k['time'] + step <= now]
        if len(cs) < 100: return 0
        trades = vs_build(cs, vs_spikes(cs, lb, v['multiple'], now - scan), v['stop_buffer_percent'], v['recover_after'], self.c.get('line_close_percent', 50)); changed = 0
        with self.lock:
            for g in trades:
                if g['time'] < self.D['start']: continue
                key = '%s|%d|%d' % (sym, g['time'], g['n']); net = net_r(g)
                ct = cs[g['end']]['time'] if g['end'] is not None else None
                r = self.D['led'].get(key)
                new = {'key': key, 'sym': sym, 'dir': g['dir'], 'n': g['n'], 't': g['time'], 'entry': g['entry'], 'sl': g['sl'], 'risk': g['risk'],
                       'res': g['res'], 'hits': g.get('hits', 0), 'net': net, 'ct': ct, 'rec': bool(g.get('rec')), 'sig': g['D']}
                if r is None or any(r.get(k) != new[k] for k in ('res', 'hits', 'net', 'ct')):
                    if r is not None: new['amt'] = r.get('amt')
                    self.D['led'][key] = new; changed += 1
            if changed: save_json(STATE, self.D)
        return changed

    def loop(self):
        while True:
            t0 = time.time(); msgs = self.poll_all()
            if msgs: print(time.strftime('%d/%m %H:%M:%S'), ' | '.join(msgs), flush=True)
            time.sleep(max(1, self.c['poll_seconds'] - (time.time() - t0)))

    def poll_all(self):
        msgs = []; self.errors = {}
        for sym in self.c['symbols']:
            if 'night' in self.c['strategies']:
                try:
                    n = self.poll_symbol(sym)
                    if n: msgs.append('%s: %d change(s)' % (sym, n))
                except Exception as e:
                    msgs.append('%s: %s' % (sym, e)); self.errors[sym] = str(e)[:120]
                time.sleep(0.5)
            if 'volspike' in self.c['strategies'] and sym in self.vs_symbols():
                try:
                    n = self.poll_vs(sym)
                    if n: msgs.append('%s volume spike: %d change(s)' % (sym, n))
                except Exception as e:
                    msgs.append('%s volume spike: %s' % (sym, e)); self.errors[sym + ' vol'] = str(e)[:120]
                time.sleep(0.5)
        self.last_poll = time.time(); self.status = 'ok'
        return msgs

    def write_public(self):
        """public_state.json = the same data as /state. It is only rewritten when something changed, or once an hour, so the repository does not fill with commits."""
        S = self.snapshot(); S['errors'] = getattr(self, 'errors', {})
        old = load_json(PUBLIC, None)
        def core(x): return json.dumps({k: x.get(k) for k in ('balance', 'closed', 'open', 'errors', 'symbols', 'timeframe', 'bal0')}, sort_keys=True)
        if old and core(old) == core(S) and time.time() - old.get('lastPoll', 0) < 3600: return False
        save_json(PUBLIC, S); return True

    def snapshot(self):
        with self.lock:
            S = calc(json.loads(json.dumps(self.D)))
        S['symbols'] = self.c['symbols']; S['strategies'] = self.c['strategies']; S['timeframe'] = self.c['timeframe']; S['lastPoll'] = self.last_poll or time.time()
        return S

PAGE = """<!doctype html><meta charset=utf-8><meta name=viewport content="width=device-width,initial-scale=1"><title>Zaka demo bot</title>
<style>body{font:14px system-ui;background:#0a0e13;color:#d3dde8;margin:16px}table{border-collapse:collapse;width:100%%;max-width:760px}td,th{padding:4px 8px;border-top:1px solid #212c38;text-align:right}th:first-child,td:first-child{text-align:left}
.up{color:#22c3a0}.dn{color:#ef5a6a}h1{font-size:20px}.big{font-size:34px;font-weight:600}</style>
<h1>Zaka demo bot</h1><div id=o>loading...</div>
<script>
const f=v=>(v>=0?'+':'-')+Math.abs(v).toFixed(2), c=v=>v>0?'up':v<0?'dn':'';
function pk(t){const d=new Date((t+18000)*1000),p=n=>String(n).padStart(2,'0');return p(d.getUTCDate())+'/'+p(d.getUTCMonth()+1)+' '+p(d.getUTCHours())+':'+p(d.getUTCMinutes())}
async function go(){try{const S=await (await fetch('/state')).json(),pl=S.balance-S.bal0;
let h='<div class=big><span class='+c(pl)+'>'+S.balance.toFixed(2)+' USDT</span></div><div>'+f(pl)+' USDT from '+S.bal0+' | '+S.closed.length+' closed, '+S.wins+' won | max drawdown '+S.maxDD.toFixed(1)+'% | open '+S.open.length+'</div><div>Pairs: '+S.symbols.join(', ')+' ('+S.timeframe+'). Last check '+new Date(S.lastPoll*1000).toLocaleTimeString()+'</div>';
if(S.open.length)h+='<h3>Open</h3><table><tr><th>Entry (PKT)</th><th>Pair</th><th>Side</th><th>Targets hit</th></tr>'+S.open.map(r=>'<tr><td>'+pk(r.t)+'</td><td>'+r.sym+'</td><td class='+(r.dir>0?'up':'dn')+'>'+(r.dir>0?'BUY':'SELL')+' '+(r.n>=11?'VOL':'S'+r.n+(r.var?'-'+r.var:''))+'</td><td>'+r.hits+'</td></tr>').join('')+'</table>';
h+='<h3>Closed (latest 30)</h3><table><tr><th>Entry (PKT)</th><th>Pair</th><th>Side</th><th>R</th><th>P&amp;L</th></tr>'+S.closed.slice(-30).reverse().map(r=>'<tr><td>'+pk(r.t)+'</td><td>'+r.sym+'</td><td class='+(r.dir>0?'up':'dn')+'>'+(r.dir>0?'BUY':'SELL')+' '+(r.n>=11?'VOL':'S'+r.n+(r.var?'-'+r.var:''))+'</td><td class='+c(r.net-r.feeR)+'>'+(r.net-r.feeR).toFixed(2)+'</td><td class='+c(r.pnl)+'>'+f(r.pnl)+'</td></tr>').join('')+'</table>';
document.getElementById('o').innerHTML=h}catch(e){document.getElementById('o').textContent='bot not answering'}}
go();setInterval(go,10000);
</script>"""

def make_handler(bot):
    class H(BaseHTTPRequestHandler):
        def log_message(self, *a): pass
        def _send(self, code, body, ctype):
            b = body.encode('utf-8') if isinstance(body, str) else body
            self.send_response(code); self.send_header('Content-Type', ctype); self.send_header('Access-Control-Allow-Origin', '*')
            self.send_header('Content-Length', str(len(b))); self.end_headers(); self.wfile.write(b)
        def do_GET(self):
            if self.path.startswith('/state'): self._send(200, json.dumps(bot.snapshot()), 'application/json')
            else: self._send(200, PAGE, 'text/html; charset=utf-8')
    return H

def main():
    if '--reset' in sys.argv:
        for p in (STATE,):
            if os.path.exists(p): os.remove(p)
        print('Demo account deleted. Start the bot again to begin a new one.'); return
    conf = json.loads(json.dumps(DEFAULT)); user = {}
    if os.path.exists(CONF):
        try:
            with open(CONF, encoding='utf-8-sig') as f: user = json.load(f)
        except Exception as e:
            sys.exit('zaka_bot_config.json is not valid JSON, so the bot stops instead of silently using the defaults: %s\nFix it (a comma or a quote is wrong) and run again.' % e)
    else: save_json(CONF, DEFAULT); print('Wrote', CONF, '- edit it to change pairs, balance, risk ...')
    vs = dict(conf['vs']); vs.update(user.pop('vs', {}) or {}); conf.update(user); conf['vs'] = vs
    if isinstance(conf['strategies'], str): conf['strategies'] = [conf['strategies']]
    if vs['timeframe'] not in TF: sys.exit('vs.timeframe must be one of ' + ', '.join(TF))
    if conf['timeframe'] not in TF: sys.exit('timeframe must be one of ' + ', '.join(TF))
    bot = Bot(conf)
    if '--once' in sys.argv:
        for m in bot.poll_all(): print(m)
        print('public_state.json', 'updated' if bot.write_public() else 'unchanged'); return
    threading.Thread(target=bot.loop, daemon=True).start()
    srv = ThreadingHTTPServer(('127.0.0.1', int(conf['port'])), make_handler(bot))
    print('Zaka demo bot is running. Open http://127.0.0.1:%d  (Ctrl+C to stop)' % conf['port'])
    print('Pairs:', ', '.join(conf['symbols']), '| timeframe', conf['timeframe'], '| signals from', 'now' if conf['start_from'] != 'history' else 'the last %d days' % conf['history_days'])
    try: srv.serve_forever()
    except KeyboardInterrupt: print('stopped')

if __name__ == '__main__':
    main()
