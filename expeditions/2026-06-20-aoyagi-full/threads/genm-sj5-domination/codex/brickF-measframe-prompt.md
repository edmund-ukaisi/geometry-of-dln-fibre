<task>
Adjudicate a sharp truth-value in measure theory / real algebraic geometry. I need a decorrelated
independent read; do NOT try to guess which answer I want — argue whichever direction is correct.

SETTING. Fix an integer N ≥ 1 (think N = M₂, small: 2, 3, 4). Let (X, 𝓑) be a standard Borel /
measurable space. Let A : X → Sym_N(ℝ) be a BOREL-MEASURABLE family of real symmetric N×N matrices
(equivalently, each of the N(N+1)/2 entries is a Borel function of z ∈ X). Write the eigenvalues,
sorted DESCENDING with multiplicity, as λ₁(z) ≥ λ₂(z) ≥ … ≥ λ_N(z).

THE PRIMITIVE TO ADJUDICATE. Does there provably exist:
  (i)  a Borel-measurable map z ↦ (λ₁(z),…,λ_N(z)) [the sorted eigenvalue vector], AND
  (ii) a BOREL-MEASURABLE map U : X → O(N) (orthogonal matrices) such that for every z,
         A(z) = U(z) · diag(λ₁(z),…,λ_N(z)) · U(z)ᵀ,
       i.e. the columns of U(z) are orthonormal eigenvectors of A(z) in the sorted order?
And can (ii)'s U be written as a CONCRETE Borel FORMULA in the entries of A — i.e. built by explicit
operations (polynomial/rational arithmetic in entries and eigenvalues, matrix inverse off a null set,
Gram–Schmidt, finite case-splits on Borel conditions) — WITHOUT invoking an abstract measurable-selection
theorem (Kuratowski–Ryll-Nardzewski / von Neumann / Jankov–von Neumann selection)?

WHY THIS IS DELICATE (the crux the reader must engage, not dodge):
- Part (i) is expected easy: eigenvalues are continuous (Weyl/Lidskii) in A, hence Borel. Confirm or
  refute, but it is not the hard part.
- Part (ii) is the crux. At points z₀ where an eigenvalue has multiplicity k > 1 (a DEGENERATE
  eigenspace), the choice of an orthonormal basis of that k-dim eigenspace is a whole O(k)'s worth of
  non-unique choices. Around such points there may be NO CONTINUOUS choice of eigenvectors at all — e.g.
  the 2×2 family A(x,y) = [[x, y],[y, −x]] on X = ℝ² has a "diabolical point"/conical intersection at
  (0,0) (eigenvalues ±√(x²+y²)); its eigenvectors carry a Berry phase and cannot be chosen continuously
  on any neighbourhood of 0. The question is whether a MEASURABLE (Borel) choice — not continuous —
  nonetheless exists as an explicit formula, and whether the O(k) ambiguity on degenerate blocks forces a
  genuine measurable-selection theorem.

CANDIDATE CONSTRUCTIONS ON THE TABLE (evaluate each; propose better if you see one):
  (a) Riesz/resolvent spectral projection P = (2πi)⁻¹ ∮_Γ (ζI − A)⁻¹ dζ around a group of eigenvalues,
      built entrywise on the (continuous, off-spectrum) resolvent; then Gram–Schmidt the columns of P.
  (b) The algebraic Lagrange/Sylvester eigenprojection onto the eigenspace of a distinct eigenvalue μ:
      P_μ = ∏_{other distinct eigenvalues ν} (A − νI)/(μ − ν); then Gram–Schmidt the columns of P_μ.
  (c) Stratify X by the eigenvalue MULTIPLICITY PATTERN (a composition of N recording which sorted
      eigenvalues coincide). Each stratum is cut out by polynomial (in)equalities in the entries (the
      characteristic-polynomial discriminant and subresultants). On each stratum the distinct eigenvalues
      are separated and vary continuously; build P_μ by (b) there; select an m-subset of the standard
      basis whose Gram determinant under P_μ is nonzero (a finite deterministic pivot), Gram–Schmidt it.

CONTEXT (Lean/Mathlib formalisation target; affects what "concrete" must mean).
- Mathlib has: spectral theorem, eigenvalues₀ (sorted, choice-built, NO measurability rider), Gram–Schmidt,
  continuity of matrix ×/det/adjugate/inv-off-spectrum, PosSemidef API.
- Mathlib LACKS: any measurable functional calculus, sorted-eigenvalue continuity lemma, and ANY
  Kuratowski–Ryll-Nardzewski / measurable-selection theorem (none exists in the library).
- So a "WALL" answer = the construction provably requires a measurable-selection theorem (⇒ a major new
  Mathlib contribution, research-level). A "LABOUR" answer = there is an explicit Borel formula reducible
  to (continuity of eigenvalues) + (finite Borel stratification) + (Gram–Schmidt), no selection theorem.

<output_contract>
Respond in these sections, terse and exact:
1. PART (i) VERDICT — one line: does the sorted-eigenvalue map exist Borel, and what is the minimal fact
   it rests on. Mark [FACT]/[STANDARD]/[UNSURE].
2. PART (ii) VERDICT — LABOUR or WALL, decisively. State it plainly.
3. THE DEGENERATE-BLOCK ARGUMENT — the heart. Exactly how (or whether) the O(k) within-eigenspace
   ambiguity is resolved without a measurable-selection theorem. If it IS resolved, give the explicit
   formula and prove its measurability (name where continuity/Borel-ness of each ingredient comes from,
   and how the multiplicity-pattern jumps are handled). If it is NOT, prove that KRN/selection is
   unavoidable (exhibit the obstruction).
4. THE DIABOLICAL POINT — work A(x,y)=[[x,y],[y,−x]] on ℝ² explicitly: give the eigenvector formula your
   construction produces, its exact discontinuity locus, and confirm it is Borel (or show it fails).
5. WHICH CANDIDATE — rank (a)/(b)/(c) for a finite-dimensional Lean formalisation; flag any that hides a
   selection theorem or an unavailable analytic primitive (e.g. a genuine contour integral of a
   matrix-valued function).
6. CHEAPEST KILL — the single sharpest test or counterexample that would flip your verdict.
Distinguish [FACT] (provable now) from [BELIEF] (plausible, unproven) throughout.
</output_contract>

<grounding_rules>
- Finite dimension N only. Do not drift to infinite-dim operators / von Neumann algebras (where measurable
  diagonalization genuinely needs selection) unless you argue the finite-dim case inherits that difficulty.
- "Measurable" = Borel. "Concrete formula" = no oracle, no arbitrary choice from a continuum; finite
  deterministic case-splits on Borel sets are allowed.
- Be exact about WHERE Gram–Schmidt can be discontinuous and whether that breaks measurability (it should
  not, but say why precisely).
- Cite the standard name of any theorem you use (Weyl inequalities, continuity of roots, semialgebraic
  triviality, etc.).
</grounding_rules>
