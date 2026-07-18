#!/usr/bin/env python3
# guards: resolution-tree
# provenance: threads/08-atlas-probe (pnp08), o4 residual. Reuses the validated simulator via importlib.
"""LiveHeadDom — the invariant that CLOSES the o4 residual sub-lemma (two-way: my in-chain domination
+ Codex's LiveHeadDom, converged).

LiveHeadDom(S,C):  lambda(a) < lambda(b) < M(S)  =>  a^i <= b^i  for all head coords i<S
  (lambda = tilde_t = the level; "live" = level < M(S), i.e. in the b-chain, NOT stranded).

Consequence (STEP1): at a case-1 node, level(y)<=J < ell=level(x) < M(S), so LiveHeadDom gives
x^i>=y^i on the head, and FlatTail gives x^i=ell>J>=y^i on the tail -> x>=y. Hence the case-1 new pivot
f'=setTail(f,S,J) satisfies f'>=every level-J divisor (f>=g via STEP1 => f head>=g head => f'>=g since
tails equal J). So f' is comparable to (indeed the max of) the level-J divisors: the residual PROVED.

The paper's full total-comparability fails ONLY on STRANDED pairs (a level >= M(S)); LiveHeadDom
deliberately says nothing there (the `< M(S)` guard), which is exactly why it survives width-drops.

MAINTENANCE (Codex, verified): case-1 uses chooser MINIMALITY (f=least at level ell => f<=every other
level-ell b => f' head <= b head); case-2 uses WidthBound (c head = M(i+1) >= a head) + the case-2 gap
(no live divisor above J); layer-advance only shrinks the live set (M(S+1)<=M(S)). So minimality IS
consumed here (contra a minimality-free reading) -- the wrong pick breaks LiveHeadDom (checked).
"""
import sys
import importlib.util
import io
import contextlib

_spec = importlib.util.spec_from_file_location("_sim", "nonmono-2232-sim.py")
_m = importlib.util.module_from_spec(_spec)
try:
    with contextlib.redirect_stdout(io.StringIO()):
        _spec.loader.exec_module(_m)
except SystemExit:
    pass
Sim = _m.Sim


def livehead_checker(pick="min"):
    class C(Sim):
        def __init__(self, *a, **k):
            super().__init__(*a, **k)
            self.viol = 0
            self.residual_fail = 0

        def def4_min(self, cands):
            if pick == "max":                              # WRONG pick
                for c in cands:
                    if all(all(x >= y for x, y in zip(c[0], d[0])) for d in cands):
                        return c
                return cands[-1]
            return super().def4_min(cands)

        def _check(self, S, J, divs):
            MS = self.Mrun(S)
            Ts = [d[0] for d in divs]
            for a in Ts:
                for b in Ts:
                    if min(a) < min(b) < MS and any(a[i] > b[i] for i in range(S - 1)):
                        self.viol += 1

        def _proc(self, S, J, divs):
            # residual check at case-1 nodes: f' = setTail(f,S,J) comparable to every level-J divisor
            if S <= self.L:
                MS = self.Mrun(S); MSp1 = min(MS, self.Mw(S + 1))
                if J < MSp1:
                    occ = [x for x in sorted({min(d[0]) for d in divs}) if J + 1 <= x <= MS - 1]
                    if occ:
                        f = self.def4_min([d for d in divs if min(d[0]) == occ[0]])
                        fT = self.set_tail(f[0], S, J)
                        for g in [d[0] for d in divs if min(d[0]) == J]:
                            comp = all(p <= q for p, q in zip(fT, g)) or all(p >= q for p, q in zip(fT, g))
                            if not comp:
                                self.residual_fail += 1
            super()._proc(S, J, divs)
    return C


tests = [(2, 2, 2), (3, 3, 4), (2, 2, 2, 2), (2, 2, 3, 2), (2, 2, 3, 3, 2), (3, 2, 4, 2),
         (2, 2, 1, 1), (3, 3, 1, 1), (3, 3, 2, 2), (4, 4, 2, 2), (4, 4, 3, 2),
         (3, 3, 2, 1), (2, 2, 1, 2), (2, 2, 2, 1, 1)]
ok = True
for M in tests:
    s = livehead_checker("min")(M, headreset="runmin", check_inv=True).run()
    ok &= (s.viol == 0 and s.residual_fail == 0)
    print(f"  M={str(M):14s} LiveHeadDom_viol={s.viol}  residual(case-1 f' vs level-J)_fail={s.residual_fail}")
print("LiveHeadDom holds + residual holds (correct min pick), all 14:", ok)

# minimality is load-bearing: the WRONG (max) pick breaks LiveHeadDom
sw = livehead_checker("max")((2, 2, 2, 2), headreset="runmin", check_inv=True).run()
print(f"  (2,2,2,2) LiveHeadDom_viol under WRONG (max) pick = {sw.viol}  (>0 => minimality maintains LiveHeadDom)")
ok &= (sw.viol > 0)

sys.exit(0 if ok else 1)
