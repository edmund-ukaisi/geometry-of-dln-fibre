<task>
Lean 4 + Mathlib v4.29 formalisation. I need to adjudicate whether a MEASURABLE strong-eigenprojection
selector `Z ↦ U_s(Z)` exists and is Mathlib-adjacent, and whether it is even NEEDED for a specific
a.e.-integration argument.

SETUP (all matrices real; `ᵀ` transpose; `PosSemidef`, `det`, `rank` are Mathlib.Matrix notions):
- `Z : Matrix (Fin M₂) (Fin n) ℝ` is an OUTER integration variable (it varies; we integrate a
  nonnegative `ℝ≥0∞`-valued integrand over `Z` in a set).
- Fix `ε > 0`, `r : ℕ`. A "count shell" `S_j := { Z | min (weakEigCount ε Z) r = j }`, where
  `weakEigCount ε Z := #{ i | eigenvalue_i(Z Zᵀ) < ε² }` (number of eigenvalues of the Gram `Z Zᵀ`
  below ε²). On shell `S_j` there are exactly `min(·,r)=j` "weak" eigenvalues and `m := M₂ − j`
  "strong" ones (≥ ε²).
- The "strong eigenprojection" `U_s : Matrix (Fin M₂) (Fin m) ℝ` has ORTHONORMAL columns
  (`U_sᵀ * U_s = 1`) spanning the sum of eigenspaces of `Z Zᵀ` with eigenvalue ≥ ε². The associated
  PSD (Loewner) inequality on the shell is `(Z Zᵀ − ε² • (U_s * U_sᵀ)).PosSemidef`.

WHAT I HAVE (banked, sorry-free) — a per-FIXED-(Z,U_s) bound:
  `shell_corankOffSector_le`: given fixed `Z`, fixed `U_s` with `U_sᵀ*U_s=1`, `b≤m≤M₂`, `m≤Z.rank`,
  `ε>0`, and the shell PSD hypothesis `(Z Zᵀ − ε²•(U_s U_sᵀ)).PosSemidef`, plus convergence
  `a < m − b + 1` and `ab/2 < c'`:
    ∃ C₁<⊤, ∀ w>0,  ∫_{A_cor∈box(b×M₂)} ∫_{Γ∈sΓ} (w + frobSq(Ccross + Γ·(A_cor·Z)))^(−c')
                       ≤ C₁ · w^(−(c'−ab/2)).
  Here `C₁ = ofReal(Cresid(ab,c')) · Wenn(Z,U_s)`, `Wenn(Z,U_s) = ∫_{A_cor∈box} det((A_cor·Z)(A_cor·Z)ᵀ)^(−a/2)`,
  and finiteness of `Wenn` is proved from `U_s`+PSD-hypothesis by PSD-monotone weak-direction elimination.
  NOTE C₁ depends on Z (and U_s) but the bound is uniform in `w`.

WHAT I NEED — to bound an OUTER integral over the shell:
    ∫_{Z ∈ S_j} [ ∫_{A_cor} ∫_{Γ} (w(Z) + frobSq(Ccross(Z) + Γ·(A_cor·Z)))^(−c') ] dZ.
  To apply `shell_corankOffSector_le` pointwise for each Z ∈ S_j and then integrate the resulting bound,
  I need, for each Z ∈ S_j, a choice of `U_s(Z)` satisfying `U_s(Z)ᵀ U_s(Z)=1` and the PSD hypothesis,
  AND — because the resulting per-Z bound `C₁(Z)·w(Z)^(−…)` must be integrated in Z — the map
  `Z ↦ (the per-Z bound)` must be a.e.-MEASURABLE, which (naively) needs `Z ↦ U_s(Z)` measurable.

SUB-QUESTIONS (answer each; Mathlib v4.29 pin — confirm names exist or say "not in v4.29"):
Q1. Does Mathlib v4.29 provide the ingredients to CONSTRUCT a measurable `Z ↦ U_s(Z)` (the rank-m
    strong eigenprojection)? Consider: `Matrix.IsHermitian.eigenvectorUnitary` / `.eigenvalues` /
    `.eigenvalues₀` (sorted); continuous-functional-calculus spectral projection `1_{[ε²,∞)}(Z Zᵀ)`;
    `MeasurableSpace`/`Measurable` instances on matrices; measurability of eigenvalues/eigenvectors in
    the matrix entries. Is eigenVECTOR selection continuous/measurable where eigenvalues cross? Where
    is the obstruction (eigenvalue crossings / eigenvector sign/basis ambiguity)?
Q2. Is a GLOBAL measurable selector actually necessary, or can the argument avoid selection? Options to
    evaluate: (a) use the SPECTRAL PROJECTION `P_s(Z) = 1_{[ε²,∞)}(Z Zᵀ)` (a projection MATRIX, not an
    eigenbasis) which is a continuous function of `Z Zᵀ` off the crossing locus {det(Z Zᵀ − ε²I)=0} and
    only needs the PROJECTION to be measurable (Borel functional calculus / a matrix polynomial /
    resolvent contour integral), NOT an orthonormal eigenbasis `U_s`; can the bound be re-stated with a
    PSD projection `P` (`P²=P=Pᵀ`, `rank P = m`) instead of `U_s`? (b) restrict to the a.e. set where
    the crossing locus is avoided (`{det(Z Zᵀ − ε²I) ≠ 0}` is co-null, a real-analytic non-vanishing
    condition) so any local measurable selection suffices; (c) avoid the pointwise-in-Z bound entirely
    and dominate the whole shell integral by a single Z-uniform majorant.
Q3. If the cleanest route is a PSD spectral PROJECTION `P` rather than an orthonormal `U_s`: is the
    downstream algebra (PSD-monotone determinant elimination `det((A_cor·Z)(A_cor·Z)ᵀ) ≥ ε^{2b}·det(...)`
    using `Z Zᵀ ⪰ ε²·P`) sound with `U_s U_sᵀ` replaced by a projection `P` of rank `m`? Note the
    downstream needs `det((A_cor·U_s)(A_cor·U_s)ᵀ)` to be integrated; with a projection `P = U_s U_sᵀ`
    one has `A_cor·P·A_corᵀ = (A_cor U_s)(A_cor U_s)ᵀ` only via a factorization `P = U_s U_sᵀ`. Does
    Mathlib give a measurable `Z ↦ U_s(Z)` from a measurable `Z ↦ P(Z)` (e.g. via a fixed reference
    factorization, Gram–Schmidt on P's columns, or `PosSemidef.sqrt`/`sqrt`-based)?
Q4. Bottom line: is the measurable-selector obligation "labour" (a bounded, banked-adjacent lemma) or a
    genuine Mathlib GAP requiring new measure-theory-of-spectra development? If a gap, what is the
    smallest native workaround (name the concrete lemma the formaliser must prove, with its Lean-shape
    signature)?
</task>

<output_contract>
Answer Q1–Q4 in order, each ≤ 8 sentences. For each, explicitly tag [FACT: Mathlib v4.29 has/lacks X]
vs [INFERENCE]. End with a 3-line VERDICT: (a) selector exists & is labour / is a gap; (b) the single
cheapest route (global selector vs projection vs a.e.-crossing-avoidance vs Z-uniform majorant);
(c) the one concrete Lean lemma signature the formaliser should target.
</output_contract>

<grounding_rules>
You may NOT assume a Mathlib lemma exists without naming it; if unsure whether a name is in v4.29, say
"[uncertain — verify]". Distinguish continuity/measurability facts you KNOW (Borel functional calculus,
continuity of spectral projections off crossings, matrix-entry continuity) from what you INFER about
this specific formalisation. Do not write Lean proofs; give signatures only. Flag any place where the
naive selector approach hides a real obstruction (eigenvalue crossings, eigenvector discontinuity).
</grounding_rules>
