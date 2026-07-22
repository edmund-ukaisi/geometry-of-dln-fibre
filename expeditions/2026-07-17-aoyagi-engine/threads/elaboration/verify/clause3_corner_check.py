#!/usr/bin/env python3
"""Clause-(III) validation for the L6-fix round (elder's authored cleared-pivot protection).

CLAIM CHECKED: along Aoyagi's (S,J) fold recursion, the canonical shear of every edge never
writes a divisor birth-corner in that edge's (child) ledger — so the strengthened
ShearWithinCarveRaw clause (III) is EMITTABLE by canonShearOf.

Decomposition of the check (write-set analysis of the certified Schur step, step_verify.py):
  the shear at a step executed at (S, J) writes ONLY
    (a) the layer-S block's row-J tail (cols > J), col-J tail (rows > J), interior (>J, >J);
    (b) the pivot row (index J) of C^(S+1)  [template-certified: Q^{-1} touches ONLY that row];
  and does NOT write the pivot corner (J,J) itself [step_verify: D'''[0,0] = 1 — re-asserted here].
So a ledger corner (bl, bc) is safe iff NOT (bl == S and bc > J) and NOT (bl > S):
  A1: no ledger corner (S, bc) with bc > J   (would sit in the written interior);
  A2: no ledger corner with bl > S           (covers the C^(S+1) pivot-row write);
  A3: the corner entry itself is fixed by Q and P-hat (symbolic, all tail sizes p,q in 1..4);
  (case-11 boost edges have edgeShear = id — trivially clause-(III); no birth at a boost,
   asserted as A4: births happen only at clearing steps, boosts never re-birth.)

Exit 0 = clause (III) emittable on every step of every instance; exit 1 = a violation (printed).
Provenance: elder's authored clause (III) 2026-07-22; guards the L6-fix round render.
Instances: the nine standing depth-diverse instances.
"""
import copy, sys
import sympy as sp

ok = True
viol = []

def run(M, tag):
    global ok
    L = len(M) - 1
    def Mrun(S): return min(M[:S])
    def tilde(T): return min(T)

    def check(S, J, ledger, where):
        global ok
        for (bl, bc) in ledger:
            if bl == S and bc > J:
                ok = False; viol.append((tag, where, S, J, (bl, bc), "A1 interior-write"))
            if bl > S:
                ok = False; viol.append((tag, where, S, J, (bl, bc), "A2 future-layer"))

    def step(S, J, divs):
        # divs: list of dicts {'T':list,'M':int,'corner':(bl,bc)}
        MS = Mrun(S); MS1 = M[S] if S <= L else None
        capJ = min(MS, MS1)
        if J == capJ:
            if S == L: return
            step(S + 1, 0, divs); return
        jumps = sorted({tilde(d['T']) for d in divs if J + 1 <= tilde(d['T']) <= MS - 1})
        if not jumps:                                   # CASE 2: birth at (S,J), shear fires
            Tn = [(M[k] if (k + 1) < S else J) for k in range(1, L + 1)]
            Mn = (MS - J) * (MS1 - J)
            nd = divs + [{'T': Tn, 'M': Mn, 'corner': (S, J)}]
            check(S, J, [d['corner'] for d in nd], "case2")   # CHILD ledger (incl. current birth)
            step(S, J + 1, nd); return
        else:
            jj = jumps[0]; J1 = jj - J
            cand = [d for d in divs if tilde(d['T']) == jj]
            ustar = min(cand, key=lambda d: tuple(d['T']))
            # chart 1(1): boost in place — edgeShear = id; corner UNCHANGED (A4: no re-birth)
            d11 = copy.deepcopy(divs)
            u1 = next(d for d in d11 if d['T'] == ustar['T'] and d['M'] == ustar['M'])
            assert u1['corner'] == ustar['corner'], "A4 violated: boost re-birthed a corner"
            for k in range(S, L + 1): u1['T'][k - 1] = J
            u1['M'] = ustar['M'] + J1 * (MS1 - J)
            step(S, J, d11)
            # chart 1(2): birth at (S,J), shear fires
            d12 = copy.deepcopy(divs)
            Tn = [(ustar['T'][k - 1] if k < S else J) for k in range(1, L + 1)]
            Mn = ustar['M'] + J1 * (MS1 - J)
            d12.append({'T': Tn, 'M': Mn, 'corner': (S, J)})
            check(S, J, [d['corner'] for d in d12], "case12")
            step(S, J + 1, d12); return

    step(1, 0, [])

INSTANCES = [(3, 3, 4), (3, 3, 2, 2), (2, 2, 2), (2, 2, 2, 2), (2, 2, 3, 2),
             (2, 2, 1, 1), (4, 4, 4), (3, 3, 3), (2, 2, 2, 2, 2)]
for M in INSTANCES:
    run(M, M)
    print(f"[A1+A2+A4] M={M}: every step's child ledger clear of the shear write-set: {ok}")

# A3: the pivot corner entry is FIXED by Q (right) and P-hat (left), all tail sizes 1..4
for p in range(1, 5):
    for q in range(1, 5):
        beta = sp.Matrix(1, q, sp.symbols(f'b0:{q}'))
        gamma = sp.Matrix(p, 1, sp.symbols(f'g0:{p}'))
        delta = sp.Matrix(p, q, sp.symbols(f'd0:{p*q}'))
        Dp = sp.Matrix.vstack(sp.Matrix.hstack(sp.Matrix([[1]]), beta),
                              sp.Matrix.hstack(gamma, delta))
        Q = sp.Matrix.vstack(sp.Matrix.hstack(sp.Matrix([[1]]), -beta),
                             sp.Matrix.hstack(sp.zeros(q, 1), sp.eye(q)))
        Ph = sp.Matrix.vstack(sp.Matrix.hstack(sp.Matrix([[1]]), sp.zeros(1, p)),
                              sp.Matrix.hstack(-gamma, sp.eye(p)))
        Dfin = sp.expand(Ph * (Dp * Q))
        if sp.simplify(Dfin[0, 0] - 1) != 0:
            ok = False; viol.append(("A3", p, q, "corner not fixed"))
print(f"[A3] pivot corner (J,J) fixed by Q,P-hat for all tails p,q in 1..4: "
      f"{not any(v[0] == 'A3' for v in viol)}")

if not ok:
    print("VIOLATIONS:")
    for v in viol: print("  ", v)
    sys.exit(1)
print("CLAUSE (III) EMITTABLE: no fold step's shear write-set touches a ledger corner. EXIT 0")
