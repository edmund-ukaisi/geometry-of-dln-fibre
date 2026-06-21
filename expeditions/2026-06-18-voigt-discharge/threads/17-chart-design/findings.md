# Thread 17 — pivot-chart design + (2,2,2) certificate (pen-and-paper, 2026-06-19)

## L3 route decision (so far): EXPLICIT CHART over SMOOTH-DESCENT
Smooth-descent (B fppf over A, B smooth/k ⟹ A smooth/k) is **absent** in Mathlib v4.29: only base-change
*stability* (`FormallySmooth.isStableUnderBaseChange`) + faithfully-flat **codescent of elementary properties**
(`FaithfullyFlat.codescendsAlong_{inj,surj,bij}`); fpqc `FlatDescent` covers surj/iso/open-immersion, NOT
smoothness. No torsor/faithfully-flat-of-orbit-map machinery. ⟹ smooth-descent = absent sub-library. Decorrelated
Codex convergent.
**OPEN (this thread did NOT settle): chart-GENERAL vs HOMOGENEITY for general M** — see thread 18.

## (2,2,2) pivot-chart certificate (exact, Gröbner-verified)
`M` = (1,1)-orbit normal form `L=[(0,0),(0,1),(1,2),(2,2)]`: `M_1=M_2=[[0,1],[0,0]]`. Ambient `C¹=k⁸`:
`A_0=[[a,b],[c,d]]`, `A_1=[[e,f],[g,h]]`; `M` at `(0,1,0,0,0,1,0,0)`.
- Local eqns of `Ō_M=Z_M`: `det A_0`, `det A_1`, `A_1A_0=0` (4 eqns); Jacobian rank 3 = codim (l.c.i.).
- Pivot `f := A_1[0,1]` (unit at `M`). On `D(f)`: **r=5 free** `(a,b,e,f,h)`; 3 determined `c=−ae/f, d=−be/f, g=eh/f`.
  The 3 residual generators vanish identically — **lex-Gröbner: localized closure ideal = graph ideal**.
- **AlgEquiv (L3.0):** `R_f̄ ≅_{k-alg} Localization.Away f (MvPolynomial (Fin 5) k)` (5 vars ↦ `(a,b,e,f,h)`,
  inverse = graph substitution). `Away` preserves `FormallySmooth` ⟹ `IsSmoothAt k m_M`; `κ(m_M)=k` from
  `m_M=ker(eval_M)`. `r=5=8−orbitLinearCodim(3)=finrank(range δ⁰)` ✓. A SINGLE pivot closes the chart.
- **L2:** `T_M Ō_M = ker(J_M) = range δ⁰` (both 5-dim, verified). Formaliser proves
  `CotangentSpace(AtPrime m_M) ≃ₗ[k] Dual k (range δ⁰)` ⟹ `finrank = finrank(range δ⁰)`. Bridge: `dμ_M` at `1`
  has image `range δ⁰`.
- Hardest sub-step (if chart route): the explicit Laurent **cofactor witnesses** (3 residual gens ∈ graph ideal
  over `k[a,b,e,f,h][1/f]`). Short at 2×2 scale.
- **Conditional on L6** (`vanishingIdeal(O_M)=vanishingIdeal(Z_M)`): the chart certifies the CLOSURE; L4★ needs
  closure = Z_M. Carried as the L3 caveat.

## General-pattern note
Determined entries are Laurent monomials in the free entries; denominator = product of the normal form's
structural-pivot entries. Suggests a uniform construction exists — but its Lean SCALE for arbitrary
interval-module sums is unsized (thread 18 resolves chart-general vs homogeneity).

Codex artefacts: `threads/17-chart-design/codex/l3-route-{prompt,answer}.md`.
