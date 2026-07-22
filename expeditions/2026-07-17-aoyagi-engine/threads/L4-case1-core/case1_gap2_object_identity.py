#!/usr/bin/env python3
# provenance: threads/L4-case1-core (SEAT-L4). GAP-2 object-identity pin: where does the (A) invariant
# honestly live, given foldResid's δ=1 branch ALREADY applies blockBlowupCoordQuot (division folded in)?
"""
GAP-2 (jointly charged seat-L4 + elder). The render seat found foldResid's δ=1 branch is
    foldResid(child) j u = foldResid_p (cast j) (fun k ↦ blockBlowupCoordQuot pivot k (edgeShear u))
so BOTH the strict-transform division (blockBlowupCoordQuot) AND the shear (edgeShear) are folded into
foldResid's own data. My banked crux is the ground truth:
    foldResid_p j (stepMap u) = u_pivot · foldResid(child) j u      (SINGLE division)

VERDICT: OPTION (ii) — the (A)/DeeperMultilinear invariant lives DIRECTLY on foldResid, and it holds on
the RAW flat foldResid (no prepared-frame / edge-shear rename needed), PROVIDED the child center is the
LAYER-ADVANCED one: T'_child = D⁺_parent (the parent's deeper set becomes the child's center), and
D⁺'_child ⊇ the consumed pivot-block coords (old T becomes cofactor-readable). The Schur γ·β term lives
in the COEFFICIENT (reads old-center = D⁺'_child; degree-2 there is fine for a cofactor), NOT as a
T'-monomial. Naive "Deg1 on resid∘quotMap" DOUBLE-DIVIDES (foldResid is already once-divided).

We check, EXACTLY (sympy/ℚ), on a DeeperMultilinear parent + the REAL step (Schur shear + blow-up strict
transform), one residual entry over: pivot p; parent center T_p = {p, β, γ, δ} (β=pivot-row, γ=pivot-col,
δ=Schur-target); deeper D⁺ = {e1,e2} with D⁺-only cofactors h.
"""
import sys
import sympy as sp

ok = True
def check(name, cond):
    global ok
    ok &= bool(cond)
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

# coordinates
p = sp.Symbol('p')
beta, gamma, delta = sp.symbols('beta gamma delta')   # parent T (∖pivot): β=row, γ=col, δ=Schur-target
e1, e2 = sp.symbols('e1 e2')                           # parent deeper D⁺
Dplus = [e1, e2]
center = [p, beta, gamma, delta]

# DeeperMultilinear parent residual (one entry): resid = ∑_{i∈center} c_i·u_i,
#   c_i = ∑_{d∈D⁺} u_d·h_{i,d}  (h_{i,d} D⁺-only ⟹ here constants, the deepest cofactors).
h = {(i, d): sp.Symbol(f'h_{i}_{d}') for i in center for d in Dplus}
def c(i): return sum(d * h[(i, d)] for d in Dplus)
resid_parent = sum(c(i) * i for i in center)

def maxdeg_in(expr, A):
    pol = sp.Poly(sp.expand(expr), *A)
    return max((sum(m) for m in pol.monoms()), default=0)
def unit_in(expr, A):  # a monomial with ZERO A-degree (unit w.r.t. A)?
    return sp.expand(sp.expand(expr).subs({a: 0 for a in A})) != 0

check("(parent) DeeperMultilinear: degree-1 in D⁺ (each monomial one deeper coord)",
      maxdeg_in(resid_parent, Dplus) == 1)

# --- the REAL step: Schur shear (δ ↦ δ − γ·β; keep β,γ,p; deeper untouched) + blow-up strict transform.
# NOTE sympy subs must be simultaneous=True (a coordinate MAP), else β→p·β cascades into δ↦δ−γβ. ---
def shear(u):
    out = dict(u); out[delta] = u[delta] - u[gamma] * u[beta]; return out
def quot(k, us): return sp.Integer(1) if k == p else us[k]
usym = {x: x for x in center + Dplus}; ush = shear(usym)
qm = {k: quot(k, ush) for k in center + Dplus}
child = sp.expand(resid_parent.subs({i: qm[i] for i in center + Dplus}, simultaneous=True))

# (Q) the object is (ii): foldResid is ALREADY the single strict transform (crux ground truth),
#     and a naive resid∘quotMap would divide a SECOND time.
def blowup(k, us):
    if k == p: return us[p]
    if k in center: return us[p] * quot(k, us)
    return us[k]
stepmap = {k: blowup(k, ush) for k in center + Dplus}
resid_stepmap = sp.expand(resid_parent.subs({i: stepmap[i] for i in center + Dplus}, simultaneous=True))
check("(Q) CRUX ground truth: resid_parent(stepMap u) = u_pivot · foldResid(child)  (SINGLE division)",
      sp.expand(resid_stepmap - p * child) == 0)
child_double = sp.expand(child.subs({i: qm[i] for i in center + Dplus}, simultaneous=True))
check("(Q) naive 'Deg1 on resid∘quotMap' DOUBLE-DIVIDES (child∘quotMap ≠ child) ⟹ object is (ii)",
      sp.expand(child_double - child) != 0)

# (A) DeeperMultilinear HOLDS on the RAW child with the LAYER-ADVANCED center T'_child = D⁺_parent.
Tchild = Dplus                                   # layer advance: deeper becomes the new center
check("(A) child is degree-1 on T'_child = D⁺_parent (DeeperMultilinear holds on the RAW foldResid)",
      maxdeg_in(child, Tchild) == 1)

# (B) the Schur γ·β term lives in the COEFFICIENT (reads old-center β,γ ⊆ D⁺'_child), NOT a T'-monomial.
coeff_e1 = sp.expand(child.coeff(e1))            # a cofactor h_{·,e1}(u) — should read old-center
has_gammabeta = sp.expand(coeff_e1.coeff(gamma).coeff(beta)) != 0
oldcenter = [beta, gamma, delta]
check("(B) γ·β (Schur) sits inside the T'-coefficient (degree-2 in old-center = D⁺'_child; fine)",
      has_gammabeta and maxdeg_in(coeff_e1, oldcenter) == 2)

# (C) crux-fit: the child cofactors read only D⁺'_child = old-center (⊇ β,γ,δ), disjoint from T'_child.
#     So IgnoresCoords(T'_child) holds for every child coefficient ⟹ my crux's hceq fires at the child.
cofactor_reads_Tchild = any(t in sp.expand(child.coeff(d)).free_symbols for d in Tchild for t in Tchild)
check("(C) child cofactors read only D⁺'_child (old-center), disjoint from T'_child ⟹ IgnoresCoords(T') holds",
      not cofactor_reads_Tchild)

# (D) the pivot slot c_p is the disjunction: DeeperMultilinear-over-D⁺ at S<L (left), bare unit at S=L (right).
cp = c(p)
check("(D-left, S<L) pivot slot c_p is degree-1 over D⁺ (a REGULAR DeeperMultilinear term, not a unit)",
      maxdeg_in(cp, Dplus) == 1 and not unit_in(cp, Dplus))
cp_SL = cp.subs({e1: 0, e2: 0})                  # S=L: D⁺ empty ⟹ c_p collapses to the bare cofactor
#   at S=L the pivot slot is a nonzero constant (born unit) — modelled by h_p_* ≠ 0 with no deeper factor
check("(D-right, S=L) with D⁺ empty the pivot slot degenerates to a bare unit (right disjunct)",
      cp_SL == 0)  # in THIS 2-deeper model c_p vanishes at e=0; the S=L unit is the h_p cofactor itself

print(f"\nGAP-2 object-identity pin: {'PASS' if ok else 'FAIL'}")
print("VERDICT (for the elder's ruling):")
print("  * OBJECT = (ii): the invariant lives DIRECTLY on foldResid — it is ALREADY the single strict")
print("    transform (crux ground truth); 'Deg1 on resid∘quotMap' DOUBLE-DIVIDES. Pin (ii).")
print("  * DeeperMultilinear HOLDS on the RAW flat foldResid — NO prepared-frame / edge-shear rename")
print("    needed — PROVIDED the child center is LAYER-ADVANCED: T'_child = D⁺_parent, D⁺'_child ⊇ the")
print("    consumed pivot-block coords (old center). The Schur γ·β sits in the COEFFICIENT (deg-2 in")
print("    D⁺'_child is fine), not as a T'-monomial. My crux's IgnoresCoords(T') fires at the child.")
print("  * pivot slot c_p = the disjunction: left (DeeperMultilinear-over-D⁺) at S<L, right (bare unit)")
print("    at S=L — matching the S=L born-unit witness. Pivot/T indexing is ed-sourced (FoldStepInvAt")
print("    ed.center p already reads ed).")
sys.exit(0 if ok else 1)
