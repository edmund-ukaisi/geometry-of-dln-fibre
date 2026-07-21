#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Probes the edge-indexed L4 hypothesis `SupportedOn`
# (DLN.Aoyagi.MonumentAtlas.Case1Preservation) for the δ=1 child divisibility. EXACT algebra.
"""
FINDING (surfaced for the pending rev-leaves review): `SupportedOn resid spec.center V` is TOO WEAK
for the δ=1 (spec.δ=true, J=0) child divisibility that `BlockChild` demands. `SupportedOn` says
"resid depends only on center coordinates"; the child needs `resid_j ∘ (blockBlowupMap center p)`
DIVISIBLE by the pivot `u_p`, which additionally requires resid_j to VANISH at the center-origin AND
be ANALYTIC (polynomial). The SupportedOn docstring's claim ("each center coordinate gains the pivot
factor, so residⱼ ∘ blockBlowupMap is divisible by u_p") is FALSE for a general SupportedOn residual.

Checks (sympy, exact):
  (G1) FAITHFUL residual (a center COORDINATE) ⟹ pullback divisible by u_p (seat-L4 BlockDivision — OK).
  (G2) SupportedOn but NON-VANISHING residual (1 + center coord) ⟹ pullback NOT divisible (const term
       survives at u_p=0). SupportedOn ⇏ divisibility.
  (G3) THE δ=1 CHILD BREAK: b = center monomial, resid = 1 + center coord ⟹ (F∘g∘σ)/b' is NON-
       polynomial (order deficit u_p^1 numerator vs u_p^2 denominator). StepInv + SupportedOn + S3 all
       hold; the δ=1 child divisibility FAILS. => the leaf's hypothesis set is unsound as stated.
  (G4) THE FIX: pin resid to center-coordinate combinations (analytic + vanish at 0) ⟹ divisibility
       restored (this is exactly seat-L4's BlockDivision assumption; SupportedOn should be strengthened).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

def block_blowup(w, S, p):
    return [w[p] if j == p else (w[p] * w[j] if j in S else w[j]) for j in range(len(w))]

# center = {0,1} (card 2, the coupled minimum), pivot p=0, ambient D=2 (no spectators).
D, S, p = 2, {0, 1}, 0
w = sp.symbols('w0 w1')
sig = block_blowup(list(w), S, p)                      # blockBlowupMap {0,1} 0

# (G1) faithful: resid = center coordinate u_1  ->  pullback = w0*w1, divisible by w0 (EXACT)
resid_faithful = w[1]
pb1 = resid_faithful.subs({w[j]: sig[j] for j in range(D)}, simultaneous=True)
check("(G1) faithful resid=u1: pullback w0*w1 divisible by w0 (quotient w1, EXACT)",
      sp.cancel(pb1 / w[0]).is_polynomial(*w))

# (G2) SupportedOn but non-vanishing: resid = 1 + u1  ->  pullback = 1 + w0*w1, value at w0=0 is 1 != 0
resid_bad = 1 + w[1]
pb2 = sp.expand(resid_bad.subs({w[j]: sig[j] for j in range(D)}, simultaneous=True))
check("(G2) resid=1+u1 (SupportedOn, non-vanishing): pullback = 1 + w0*w1",
      sp.simplify(pb2 - (1 + w[0] * w[1])) == 0)
check("(G2) pullback does NOT vanish at w0=0 (=1) ==> NOT divisible by w0  [SupportedOn ⇏ divisible]",
      pb2.subs(w[0], 0) != 0)

# (G3) the δ=1 child break. b = u0 (center monomial, b(0)=0), resid_0 = 1+u0, resid_1 = u1, q=(1,0).
b = w[0]
F0 = sp.expand(1 * (b * (1 + w[0])) + 0 * (b * w[1]))    # F0 = u0 + u0^2  (StepInv factorization)
check("(G3) StepInv S3: (F0∘g)(0) = 0", F0.subs({w[0]: 0, w[1]: 0}) == 0)
# δ=1 child (g=id, any shear cannot fix an order deficit; take sh=id): σ = blockBlowup, b' = u0*(b∘σ)
b_sig = b.subs({w[j]: sig[j] for j in range(D)}, simultaneous=True)   # b∘σ = w0
bprime = sp.expand(w[0] * b_sig)                                      # b' = u0^2
F0_sig = sp.expand(F0.subs({w[j]: sig[j] for j in range(D)}, simultaneous=True))  # (F0∘g∘σ) = u0+u0^2
quot = sp.cancel(F0_sig / bprime)                                    # (F0∘g∘σ)/b' = (1+u0)/u0
check("(G3) b' = u0^2, (F0∘g∘σ) = u0 + u0^2  (u_p-order 1 numerator vs order 2 denominator)",
      sp.simplify(bprime - w[0]**2) == 0 and sp.simplify(F0_sig - (w[0] + w[0]**2)) == 0)
check("(G3) (F0∘g∘σ)/b' is NON-polynomial ==> NO continuous child quotient ==> δ=1 BlockChild FAILS",
      not quot.is_polynomial(*w))

# (G4) THE FIX: resid a center-coordinate combination (vanishes at 0, analytic). resid_0 = u0, resid_1=u1.
F0_fix = sp.expand(1 * (b * w[0]))                                    # F0 = u0^2 (resid_0 = u0)
F0fix_sig = sp.expand(F0_fix.subs({w[j]: sig[j] for j in range(D)}, simultaneous=True))  # = u0^2
quot_fix = sp.cancel(F0fix_sig / bprime)                             # = 1, polynomial
check("(G4) FIX resid=center coords: (F0∘g∘σ)/b' polynomial (child divisibility restored)",
      quot_fix.is_polynomial(*w))

print("\nCONCLUSION: SupportedOn is necessary but INSUFFICIENT for δ=1 divisibility; the residual must")
print("also VANISH at the center-origin and be ANALYTIC (== a center-coordinate combination, seat-L4")
print("BlockDivision's assumption). The rendered L3/L4 hypothesis `SupportedOn` should be strengthened.")
print(f"\nL4 SupportedOn-gap probe: {'PASS (gap confirmed)' if ok else 'FAIL'}")
sys.exit(0 if ok else 1)
