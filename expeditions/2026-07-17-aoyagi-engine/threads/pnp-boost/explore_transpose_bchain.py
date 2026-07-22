#!/usr/bin/env python3
"""EXPLORATORY: pin (a) the transpose (partial block = template ROW 0 vs COL 0) via the NON-square
(3,3,2,2) residual, and (b) the load-bearing b-chain fact: u_p | b_i  <=>  i > J_1 (dominant rows
1..J_1 are u_p-FREE; non-dominant rows carry u_p). Mirrors clause3_corner_check.py's recursion."""
import copy, sys
from sympy import symbols, prod, Integer

def fold_emit(M):
    """Run the (S,J) fold; at every interior case1(1)-δ=1 edge (J=0, S<L) emit parent data:
    (S, divisors[with u-symbol,t̃], reused u_p, J1, MS=M(S), MS1=M^(S+1))."""
    L = len(M) - 1
    def Mrun(S): return min(M[:S])
    def tilde(T): return min(T)
    emits = []
    # each divisor: dict u (Symbol), T (list), birthS
    counter = [0]
    def fresh_u():
        counter[0] += 1
        return symbols(f'u_{counter[0]}')
    def step(S, J, divs):
        MS = Mrun(S); MS1 = M[S] if S <= L else None; capJ = min(MS, MS1)
        if J == capJ:
            if S == L: return
            step(S + 1, 0, divs); return
        jumps = sorted({tilde(d['T']) for d in divs if J + 1 <= tilde(d['T']) <= MS - 1})
        if not jumps:                                   # CASE 2 birth
            Tn = [(M[k] if (k + 1) < S else J) for k in range(1, L + 1)]
            nd = divs + [{'u': fresh_u(), 'T': Tn, 'birthS': S}]
            step(S, J + 1, nd); return
        jj = jumps[0]; J1 = jj - J
        cand = [d for d in divs if tilde(d['T']) == jj]
        ustar = min(cand, key=lambda d: tuple(d['T']))
        if J == 0 and S < L:                            # INTERIOR case1(1) δ=1 boost parent
            emits.append(dict(S=S, divs=copy.deepcopy(divs), up=ustar['u'], J1=J1, MS=MS, MS1=MS1))
        # case1(1): boost in place (reset t^(S..L)=J), no J-advance
        d11 = copy.deepcopy(divs)
        u1 = next(d for d in d11 if d['u'] == ustar['u'])
        for k in range(S, L + 1): u1['T'][k - 1] = J
        step(S, J, d11)
        # case1(2): split (birth new inheriting) — advance J (a DIFFERENT branch)
        d12 = copy.deepcopy(divs)
        Tn = [(ustar['T'][k - 1] if k < S else J) for k in range(1, L + 1)]
        d12.append({'u': fresh_u(), 'T': Tn, 'birthS': S})
        step(S, J + 1, d12); return
    step(1, 0, [])
    return emits

def bchain(divs, MS):
    """b_i = prod of u_d over divisors with t̃(d) < i,  i = 1..MS."""
    b = []
    for i in range(1, MS + 1):
        facs = [d['u'] for d in divs if min(d['T']) < i]
        b.append(prod(facs) if facs else Integer(1))
    return b

for M in [(2, 2, 2, 2), (3, 3, 2, 2)]:
    print("="*76)
    print(f"M = {M}")
    for e in fold_emit(M):
        S, divs, up, J1, MS, MS1 = e['S'], e['divs'], e['up'], e['J1'], e['MS'], e['MS1']
        b = bchain(divs, MS)
        print(f"\n  interior case11-δ1 boost parent at (S={S}, J=0):  reuse u_p = {up},  J1={J1}")
        print(f"    M(S)={MS} (template ROWS = running-min axis),  M^(S+1)={MS1} (template COLS = raw axis)")
        print(f"    residual D_0 is  M(S) x M^(S+1) = {MS} x {MS1}  (template);  flat-block is its TRANSPOSE")
        print(f"    b-chain (i=1..{MS}):")
        for i, bi in enumerate(b, 1):
            has_up = (up in bi.free_symbols) if hasattr(bi, 'free_symbols') else False
            print(f"      b_{i} = {bi}      u_p | b_{i}? {has_up}   ({'DOMINANT (i<=J1)' if i<=J1 else 'non-dominant (i>J1)'})")
        # LOAD-BEARING: u_p | b_i  <=>  i > J1
        okfact = all(((up in b[i-1].free_symbols) == (i > J1)) for i in range(1, MS+1))
        print(f"    [b-chain fact] u_p | b_i  <=>  i > J1 : {okfact}")
        # transpose: |partial block| = M^(S+1) (template ROW 0) matches canonCenter flat-col-0 size = #flat rows
        print(f"    |partial block| (canonCenter) = #flat-rows = d_(layer+1) ; template ROW 0 has M^(S+1)={MS1} entries")
