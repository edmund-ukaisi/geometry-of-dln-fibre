# Codex consult — constructing the C2(a) iso `e`, and which orbit it uses

You are a Lean4/Mathlib + algebraic-geometry design reviewer. DESIGN/SOUNDNESS consult before a
~1000-line build. Do NOT write Lean; give a route + adjudicate one structural truth-value.

## Setup (DLN multiplication fibre, type-A quiver)
- `d : Fin (N+2) → ℕ` (fibre dim vector); `r` the target rank; `δ = r·(d_last + d_0 − r) ≥ 1` for r≥1.
- `sweepFibreRing = O(F)`, `F = mult⁻¹(E_r)` the fibre over the rank-`r` normal form. Reduced, fp.
- `O(Σ̄^r)` = coordinate ring of the rank-`≤r` product locus, ambient `RepCoord d` (SAME as fibre).
- Chart keystone (BUILT, Lean): `Away dsig ≃ₐ[k] SchurLoc ⊗_k sweepFibreRing`, where `dsig` localizes
  `O(Σ^r)` (rank-exactly-r locus) and `SchurLoc = Localization.Away detSchurS` is a localized
  polynomial ring in δ variables (the C-part / Schur factor; regular of dim δ).
- BUILT (unconditional, Lean): every top-dim component `q` of `O(Σ̄^r)` satisfies
  `O(Σ̄^r)⧸q ≃ₐ[k] orbitRing (realizerD m)` for a corner-`r` Kostant `m`, where `realizerD m` is a
  Tuple over **`d`** (the FULL fibre dim vector, NOT shifted). Call this object (B).

## The THREE objects (worked at (2,2,2), r=1; δ=3)
- (A) fibre top component `sweepFibreRing⧸I`: **dim 4**.
- (B) sigma top component `orbitRing (realizerD m)` over `d=(2,2,2)`: **dim 7 = 4 + δ**.
- (C) shifted/residual orbit `orbitRing M` over `d−r=(1,1,1)` at corner 0: **dim 1 = 4 − δ**.

The chart product structure `Away dsig ≃ SchurLoc ⊗ sweepFibreRing` localizes (B) and exhibits it as
`(δ-dim localized poly) ⊗ (fibre)` → strongly suggests **(B) ≅ (A) × A^δ**, i.e.
`orbitRing (realizerD m) ≃ₐ[k] MvPolynomial η (sweepFibreRing⧸I)`, |η|=δ.

The smoothness CONSUMER I already built (`isSmoothAt_sweepFibre_of_component_orbitPolyEquiv`) wants the
OTHER factorization: `sweepFibreRing⧸I ≃ₐ[k] MvPolynomial η (orbitRing M)` — i.e. **(A) ≅ (C) × A^δ**,
using the SHIFTED orbit (C), dim 1.

## The questions (adjudicate sharply)

1. **Is (A) ≅ (C) × A^δ actually TRUE?** I.e. is the fibre top component, as a reduced variety,
   isomorphic to (shifted orbit closure over d−r) × A^δ? Dimensionally it checks (1+3=4). But the
   chart naturally gives (B) ≅ (A) × A^δ, NOT (A) ≅ (C) × A^δ. Are (B) and (C) related by
   `orbitRing (realizerD m over d) ≅ MvPolynomial ζ (orbitRing M over d−r)` for some ζ — i.e. is the
   full-d orbit closure itself a polynomial extension of the shifted-(d−r) orbit closure? (This is the
   rank-shift on orbit closures: `Ō` over d with corner r vs `Ō` over d−r with corner 0. Is the
   former ≅ the latter × affine? By how many vars?) If (B)≅(A)×A^δ and (B)≅(C)×A^ε, then
   (A)×A^δ ≅ (C)×A^ε; does that give (A)≅(C)×A^{ε−δ}? Only if cancellation holds (NOT automatic for
   rings — `R[x]≅S[y]` does NOT give `R≅S[y−x]`). FLAG cancellation hazards hard.

2. **Given the hazard in Q1, should the smoothness consumer instead target (B)** — i.e. should I
   re-correct the interface to `MvPolynomial η (sweepFibreRing⧸I) ≃ orbitRing (realizerD m)` (the
   factorization the chart NATURALLY produces), and prove smoothness of `sweepFibreRing⧸I` from THAT?
   Problem: that iso has `sweepFibreRing⧸I` on BOTH sides (it's `(fibre comp) × A^δ ≅ orbit`), so it
   does not directly give "fibre comp is smooth" unless I can deduce smoothness of a factor from
   smoothness of `factor × A^δ`. IS THERE a clean CA lemma "if `MvPolynomial η R` is smooth at a point
   then `R` is smooth at the corresponding point" (smoothness descends through a polynomial/affine
   factor)? If yes, route via (B) entirely — `orbitRing (realizerD m)` is smooth at normal form
   (BUILT), so `(fibre comp) × A^δ` is smooth there, so fibre comp is smooth. This SIDESTEPS the
   shifted orbit (C) and the cancellation hazard. Adjudicate: does smoothness descend through a free
   polynomial factor (Mathlib `Algebra.Smooth`/`FormallySmooth` — formal smoothness of `A` from
   `MvPolynomial ι A`)? Name the mechanism.

3. **Recommended cleanest route to FULLY-UNCONDITIONAL smoothness of the fibre top component**, given
   (B) is BUILT (unconditional) and the chart product `Away dsig ≃ SchurLoc ⊗ sweepFibreRing` is BUILT.
   Specifically: can I get `IsSmoothAt k I` of `sweepFibreRing` DIRECTLY from (B) + a
   smoothness-descends-through-affine-factor lemma, WITHOUT ever constructing the shifted-orbit iso (A)≅(C)×A^δ?
   The localized chart `Away dsig ≃ SchurLoc ⊗ sweepFibreRing` says the LOCALIZED sigma ring is
   `(smooth δ-factor) ⊗ fibre`; `sweepFibreRing` is smooth at I iff `SchurLoc ⊗ sweepFibreRing` is
   smooth at the corresponding point (smooth base change by the regular SchurLoc) iff `Away dsig`
   (= localized O(Σ^r)) is smooth there iff `O(Σ̄^r)` is smooth at the sigma component q iff
   `orbitRing (realizerD m)` is smooth at its generic pt (BUILT via OrbitSmooth + the sigma iso (B)).
   Is THIS chain (smoothness transport, no variety iso `e` needed) the actually-correct route to
   unconditional fibre smoothness? It seems to make the consumer's `e` UNNECESSARY. Pressure-test:
   does the C3 module already do part of this (it transports `sweepFibreRing` smoothness FROM the
   chart — is that circular, or is the missing direction exactly "smoothness of sigma component ⟹
   smoothness of fibre component via the chart product")?

Be skeptical and concrete. The KEY deliverable: tell me whether the cleanest path to unconditional
fibre smoothness is (i) build the variety iso `e` (and which orbit), or (ii) a pure SMOOTHNESS-TRANSPORT
chain through the chart that needs no `e` at all. If (ii), give the exact rung sequence and name the
Mathlib smoothness-descent lemma.
