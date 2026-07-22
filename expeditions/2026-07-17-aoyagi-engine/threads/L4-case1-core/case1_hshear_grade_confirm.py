#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). Confirm the exact hshear_grade predicate SUPPLIES conjunct-B
# (arch-C's blocking question): does clause (a) [S'-image deg-1 on S'] suffice, or is clause (b)
# [S'ᶜ-image S'-free] needed? + the parent-structure dependency.
"""
child = foldResid_p(qm), qm_k = blockBlowupCoordQuot pivot k (blockShear φ u) = (1 if k=pivot else (Bφ u)_k).
Parent Deg1 on S_p = layer S, DeeperMultilinear coeffs over S_pᶜ. Child support S' = layer S+1 (descend).
Conjunct-B needs: child Deg1 on S' with DeeperMultilinear coeffs over S'ᶜ.

Model layers: S_p={p(pivot),ga,be,de} (carve); S'={s1,s2} (child support); deeper={e}.
Parent (multilinear fibre form, one factor per layer): resid slot = (S_p factor)·(S' factor)·(deeper).
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok; ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

p, ga, be, de = sp.symbols('p ga be de')     # S_p = carve (layer S)
s1, s2 = sp.symbols('s1 s2')                  # S' = child support (layer S+1)
e = sp.symbols('e')                           # deeper
Sp = [p, ga, be, de]; Sprime = [s1, s2]; deep = [e]

def is_deg1_on(expr, T):
    ex = sp.expand(expr)
    if ex == 0: return True
    pol = sp.Poly(ex, *T) if T else sp.Poly(ex, sp.Symbol('_z'))
    return ({sum(m[:len(T)]) for m in pol.monoms()} if T else {0}) == {1}

def child(shear_disp, resid):
    """apply qm = (p↦1) ∘ blockShear φ to resid. shear_disp: coord↦φ displacement."""
    B = {c: c + shear_disp.get(c, 0) for c in Sp + Sprime + deep}   # blockShear = id + φ
    qm = dict(B); qm[p] = sp.Integer(1)
    return sp.expand(resid.subs(qm, simultaneous=True))

# parent slots (multilinear: S_p factor × S' factor × deeper). Two representative slots:
resid_de = de * s1 * e     # S_p factor = de (uncleared carve); S' factor = s1
resid_p  = p  * s1 * e     # S_p factor = pivot p (cleared slot)

# ---- Schur (S'-images identity; S'ᶜ-image de↦de−ga·be reads carve⊆S'ᶜ) : satisfies (a)+(b) ----
schur = {de: -ga * be}
check("Schur: child(slot de) deg-1 on S'={s1,s2}", is_deg1_on(child(schur, resid_de), Sprime))
check("Schur: child(slot p, cleared) deg-1 on S'", is_deg1_on(child(schur, resid_p), Sprime))

# ---- Q2⁻¹-form (S'-image s1↦s1−ga·s2 : deg-1 on S', reads carve×S'; S'ᶜ untouched) : satisfies (a)+(b) ----
q2 = {s1: -ga * s2}
check("Q2⁻¹: child(slot de) deg-1 on S'", is_deg1_on(child(q2, resid_de), Sprime))

# ---- BREAKER satisfying (a) VACUOUSLY but violating (b): de↦de+s1² (S'ᶜ-coord image reads S') ----
brk = {de: s1 * s1}
check("BREAKER de↦de+s1² (violates (b), (a) vacuous on S'ᶜ): child deg-2 on S' ⟹ (a)-ALONE INSUFFICIENT",
      not is_deg1_on(child(brk, resid_de), Sprime))

# ---- FRAME breaker on an S' coord: s1↦s1+p (violates (a): p is S'-free term). ----
frame = {s1: p}
check("FRAME s1↦s1+p (violates clause (a): image not deg-1 on S'): child not deg-1 on S' ⟹ (a) kills it",
      not is_deg1_on(child(frame, resid_de), Sprime))

# ---- clause (b) as IgnoresCoords S' for S'ᶜ-coord images: verify construction shears satisfy it ----
def ignoresS_prime(disp, i):
    """(blockShear φ)_i ignores S' ? (displacement of coord i reads no S')."""
    d = disp.get(i, 0)
    return not (set(Sprime) & sp.expand(d).free_symbols)
check("(b) Schur: every S'ᶜ-coord image ignores S' (de↦−ga·be reads carve only)",
      all(ignoresS_prime(schur, i) for i in Sp + deep))
check("(b) Q2⁻¹: every S'ᶜ-coord image ignores S' (S'ᶜ untouched)",
      all(ignoresS_prime(q2, i) for i in Sp + deep))
check("(b) BREAKER de↦de+s1²: S'ᶜ-coord image de READS S' ⟹ violates (b) (correctly excluded)",
      not ignoresS_prime(brk, de))

# ---- PARENT-STRUCTURE DEPENDENCY: if the parent's DeeperMultilinear coeff h READS S' (allowed by the
# bare def over S_pᶜ ⊇ S'), the child can be deg-2 on S' EVEN with a perfect (a)+(b) shear. ----
resid_h_reads_Sp = de * s1 * s2      # a "parent" whose coeff (of de) reads S' twice (s1·s2) — deg-2 on S'
check("PARENT DEPENDENCY: parent slot with coeff reading S' (de·s1·s2) → child deg-2 on S' even under Schur",
      not is_deg1_on(child(schur, resid_h_reads_Sp), Sprime))

print(f"\nhshear_grade confirmation: {'PASS' if ok else 'FAIL'}")
print("ANSWER TO arch-C:")
print("  (1) clause (a) ALONE is INSUFFICIENT — need clause (b): ∀ i∈S'ᶜ, the shear image ignores S'")
print("      (S'ᶜ-coord images stay S'-free). The general breaker de↦de+s1² satisfies (a) vacuously but")
print("      violates (b) and makes the child deg-2 on S'. (a)+(b) is the right pair; the S'→S'")
print("      'preservation form' is the wrong shape (conjunct-B is a DESCEND S_p→S', not S'→S').")
print("  (2) pivot-independence is IMPLIED, not extra: (a) kills u_i↦u_i+u_p on S' coords (u_p is S'-free,")
print("      breaks deg-1-on-S'); (b) kills S'ᶜ-coord breakers. pivot∈S_p⊆S'ᶜ; reading it within S'ᶜ is fine.")
print("  (3) TRUE-UNDER-BOTH confirmed WITH (b): Schur (S'-image=id ✓a; S'ᶜ-image=de−ga·be ignores S' ✓b);")
print("      Q2⁻¹ (S'-image=s1−ga·s2 deg-1 ✓a; S'ᶜ untouched ✓b).")
print("  DEPENDENCY FLAG: conjunct-B ALSO needs the parent's DeeperMultilinear coeff h to NOT read S'")
print("      (deeper-than-S' only) — the construction's MULTILINEAR residual gives this; the bare")
print("      DeeperMultilinear-over-S_pᶜ def technically allows h to read S' (→ child deg-2 on S'). This is")
print("      an INVARIANT-strength question separate from the shear predicate — flag for the elder.")
sys.exit(0 if ok else 1)
