#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Determine the EXACT hshear_schur predicate on ed.shearφ
# that closes conjunct-B (DeeperMultilinear self-propagation) — arch-C's blocking re-render input.
"""
Goal: the WEAKEST-that-INDUCTS shear pin s.t. child = foldResid_p(quot ∘ shear) is DeeperMultilinear on
the CHILD support, given the parent is DeeperMultilinear on the PARENT support. Requirements:
(1) stated against edge fields (shearφ + the generic pins); (2) every construction edge satisfies it;
(3) kills the conjunct-B breaker classes (u_i↦u_i+u_p FRAME; u_i↦u_i+support² general); (4) render-ready.

3-layer model (layers S=carve, S+1=child support, S+2=deeper). At δ=1: parent support = layer S;
child support = layer S+1; pivot p ∈ layer S. Parent residual (DeeperMultilinear on layer S, coeffs over
Sᶜ = {S+1,S+2}): resid = ∑_{i∈S} u_i · c_i,  c_i = ∑_{d∈Sᶜ} u_d·h_d.  We take the honest multilinear
fibre form: one factor per layer.  Child = resid(quot∘shear), quot: p↦1, else (shear u)_·.
Test which shear pins make the child DeeperMultilinear on layer S+1 (= degree-1 in {S+1} coords, coeffs
reading (S+1)ᶜ, vanishing at S+1 = 0).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

# layer coords: carve S = {p (pivot), g (γ=col), b (β=row), dl (δ=sub-block)}; child support S1 = {s1};
# deeper S2 = {e}.  (One representative coord per role.)
p, g, b, dl = sp.symbols('p g b dl')      # layer S (carve)
s1 = sp.Symbol('s1')                      # layer S+1 (child support)
e = sp.Symbol('e')                        # layer S+2 (deeper)
S = [p, g, b, dl]; S1 = [s1]; S2 = [e]

# parent residual: multilinear, one factor per layer. A representative slot whose S-factor is dl:
# resid = dl · s1 · e   (deg-1 on S via dl, deg-1 on S+1 via s1, deg-1 on S+2 via e).
# (The slot whose S-factor is the pivot p: resid_p = p · s1 · e — exercises the clear.)
def child_of(shear, resid):
    """quot (p↦1) ∘ shear, then substitute into resid. shear: dict coord↦displacement (blockShear=id+φ)."""
    sh = {c: c + shear.get(c, 0) for c in S + S1 + S2}     # (shear u)_c = u_c + φ_c
    quot = dict(sh); quot[p] = sp.Integer(1)               # blockBlowupCoordQuot pivot: p-slot ↦ 1
    return sp.expand(resid.subs(quot, simultaneous=True))

def is_deg1_on(expr, T):
    ex = sp.expand(expr)
    if ex == 0: return True
    pol = sp.Poly(ex, *T) if T else sp.Poly(ex, sp.Symbol('_z'))
    return ({sum(m[:len(T)]) for m in pol.monoms()} if T else {0}) == {1}

resid_dl = dl * s1 * e      # slot with S-factor = dl (an un-cleared carve coord)
resid_p  = p  * s1 * e      # slot with S-factor = pivot p (the cleared slot)

# ---- the construction's Schur-fold shear: dl ↦ dl − g·b (Schur, within carve), pivot-independent ----
schur = {dl: -g * b}
c_dl = child_of(schur, resid_dl); c_p = child_of(schur, resid_p)
check("Schur fold, slot-dl: child deg-1 on child support {s1}",  is_deg1_on(c_dl, S1))
check("Schur fold, slot-p (cleared): child deg-1 on child support {s1} (p↦1, keeps s1)", is_deg1_on(c_p, S1))

# ---- BREAKER 1 (FRAME axis): a pivot-READING shear s1 ↦ s1 + p (writes child-support coord using pivot) ----
frame = {s1: p}
bf_dl = child_of(frame, resid_dl)
check("BREAKER frame (s1↦s1+p) MUST violate the pin (child not deg-1 on {s1}: c·p term, p∈cofactor)",
      not is_deg1_on(bf_dl, S1))

# ---- BREAKER 2 (general support-injection): dl ↦ dl + s1·s1 (injects child-support² into a carve coord) ----
gen = {dl: s1 * s1}
bg_dl = child_of(gen, resid_dl)
check("BREAKER general (dl↦dl+s1²) MUST violate the pin (child deg-2 on {s1})",
      not is_deg1_on(bg_dl, S1))

# ============ CANDIDATE PINS — which distinguishes Schur (PASS) from BOTH breakers (must reject)? ============
# Pin A: pivot-INDEPENDENT (φ reads no p). schur: reads g,b (not p) ✓; frame: reads p ✗; gen: reads s1 (not p) ✓.
def reads(disp): return set().union(*[sp.expand(v).free_symbols for v in disp.values()]) if disp else set()
pinA = lambda disp: p not in reads(disp)
check("Pin A (pivot-independent): Schur ✓, frame ✗ — but gen ✓ (INSUFFICIENT: admits the general breaker)",
      pinA(schur) and (not pinA(frame)) and pinA(gen))

# Pin B: displacement of each coord is DEEPER-MULTILINEAR over that coord's-layer-COMPLEMENT-downward, i.e.
# φ_c reads ONLY coords in layers STRICTLY SHALLOWER-OR-EQUAL to c AND never the child support S1 as a
# WRITTEN-into-support factor... too fiddly. Try the CLEAN form actually matching the Schur:
# Pin C (CARVE-COFACTOR FORM): φ writes ONLY carve coords (layer S), and each φ_c reads ONLY carve coords
# EXCLUDING the pivot (⊆ S∖{p}). schur: writes dl∈S, reads g,b∈S∖{p} ✓. frame: writes s1∉S ✗. gen: writes
# dl∈S but reads s1∉S ✗.  Kills BOTH breakers, admits Schur.
carve_nonpivot = {g, b, dl}
def pinC(disp):
    writes_ok = all(c in S for c in disp.keys())
    reads_ok = reads(disp) <= carve_nonpivot
    return writes_ok and reads_ok
check("Pin C (writes ⊆ carve S, reads ⊆ carve∖pivot): Schur ✓, frame ✗, gen ✗ — KILLS BOTH breakers",
      pinC(schur) and (not pinC(frame)) and (not pinC(gen)))

print(f"\nhshear_schur pin determination: {'PASS' if ok else 'FAIL'}")
print("FINDING: Pin A (pivot-independence) is NECESSARY but NOT sufficient (admits the general support-")
print("  injection breaker dl↦dl+s1²). Pin C — φ WRITES only carve-block coords (⊆ blockCoords(carve layer),")
print("  available via hcenter) and READS only carve-block coords EXCLUDING the pivot — kills BOTH breakers")
print("  and admits the Schur fold. CAVEAT to verify vs the Q2⁻¹-into-next-layer transfer (below).")
sys.exit(0 if ok else 1)
