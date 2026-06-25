<task>
I am formalising in Lean 4 + Mathlib. I have a clean math route (iterated fibre integration) for a
finiteness integral and want the CLEANEST LEAN formulation of the core "fibre lemma" — minimising
case-splits and parameter-dependent change-of-variables bookkeeping.

WHAT I HAVE PROVEN (reusable Lean bricks):
  - sumSqND_box_lt_top: ∫⁻_{[−T,T]^p} (Σ_{i<p} x_i²)^{−c'} dx < ∞ for c' < p/2.  (p-dim Morse leaf.)
  - radial_morse_dominates_lt_top: ∫⁻_{z-box} ∫⁻_{P-box} (Σ_{i<p} P_i² + W(z))^{−c'} ≤ Kbound·vol(z-box),
    for c' < p/2, W ≥ 0 measurable. (Tonelli + W≥0 domination.)
  - measurePreserving_shearAt {n} (i : Fin (n+1)) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g):
    the single-coordinate shear x ↦ update x i (x i + g(x_{others})) is volume-preserving on Fin(n+1)→ℝ.
  - lintegral_image_eq_lintegral_abs_det_fderiv_mul (change of variables), Tonelli (lintegral_prod,
    setLIntegral_prod), volume_measurePreserving_piCongrLeft (reindex).

THE FIBRE LEMMA (math, VERIFIED numerically):
  For X ∈ ℝ^{p×n} (free, box (−1,1)^{pn}), FIXED Y ∈ ℝ^{n×q} with Y ≠ 0:
     ∫_{X∈(−1,1)^{pn}} ‖X·Y‖_F^{−2c'} dX ≤ K(Y,c') < ∞   for c' < p/2,
  with K(Y,c') = (something)·‖Y‖^{−2c'}. The argument: pick max-abs entry Y_{ℓj}; per-row det-1 shear
  u_i := (XY)_{ij}/Y_{ℓj}; then ‖XY‖² ≥ Y_{ℓj}²·Σ_i u_i² ≥ (‖Y‖²/(nq))·Σ_i u_i², and the box maps into
  |u_i|<n, spectators |v|<1, so ∫ ≤ (‖Y‖²/nq)^{−c'}·∫_{(−n,n)^p}(Σu²)^{−c'}·(spectator vol).

THE PROBLEM: the "max-abs entry of Y" selection is a parameter-dependent case split (which (ℓ,j) is
maximal varies over Y's domain). In the OUTER assembly Y is itself integrated (Y = A1·A2, then A2), so
Y is NOT actually fixed — I Tonelli the X-fibre first with Y as a parameter, so I need the bound to hold
for a.e. Y with a measurable constant K(Y).

QUESTION — rank these Lean formulations of the fibre lemma by LEAST bookkeeping, and give the cleanest:
  (F1) Fix a SINGLE column j and a SINGLE row-coordinate index ℓ, REQUIRE Y_{ℓj} ≠ 0 as a hypothesis,
       do the per-row shear dividing by Y_{ℓj}. Bound: ∫_X ‖XY‖^{−2c'} ≤ |Y_{ℓj}|^{−2c'}·C_{p,n,c'}.
       Then in the assembly, split Y-space by which entry is nonzero/maximal. Is the per-row shear here a
       clean product of p independent `measurePreserving_shearAt`s (one per row, on disjoint coords)?
  (F2) Avoid the shear entirely: lower-bound ‖XY‖² ≥ Σ_i (XY)_{ij}² and substitute the LINEAR map
       L : X_row_i ↦ (XY)_{ij} directly via a measure-preserving linear reindex per row, using that the
       map ℝ^n → ℝ^n sending X_i ↦ (⟨X_i,Y_{·j}⟩, X_{i,2..n}) has |det| = |Y_{ℓj}| (one nonzero pivot).
       Is there a Mathlib lemma for "∫ f(L x) = |det L|^{-1} ∫ f" for a fixed invertible linear L that is
       cleaner than building the shear by hand? (e.g. via `MeasureTheory.lintegral_comp_mul` analogues,
       or `Real.map_linearMap_volume_pi_eq_smul_volume`, or addHaar smul.)
  (F3) Keep the integral over the WHOLE Y but note: do I even need the max-entry? Since I only need
       FINITENESS (not the sharp constant), can I fix ONCE AND FOR ALL the column j=0 and row-coord ℓ=0,
       restrict to the region {|Y_{00}| ≥ |Y_{kj}| for all k,j} by a finite union over (ℓ,j) of such
       regions (covering Y≠0 up to null), and on each region use F1? How many pieces, and is the union
       bookkeeping worth it vs. just proving F1 and instantiating per-region in the assembly?

For the ACTUAL assembly I need (the (4,4,2,2) case): the outer integral is over A2∈(−1,1)^4 (4 coords),
then A1∈(−1,1)^8, then A0∈(−1,1)^16, of ‖A0·A1·A2‖^{−2c'}, c'<2. I plan:
  Tonelli A0 inner (Y0:=A1·A2): fibre-lemma ⟹ ≤ C0·‖A1·A2‖^{−2c'};   [p=4,n=4,q=2]
  Tonelli A1 (Y1:=A2):          fibre-lemma ⟹ ≤ C0·C1·‖A2‖^{−2c'};    [p=4,n=2,q=2]
  ∫_{A2}(−1,1)^4 ‖A2‖^{−2c'} < ∞ by radial_ball_iff (c'<2).
But ‖A1A2‖ and ‖A2‖ as the "Y" are themselves integrated — so the fibre bound's constant C must be a
fixed number, NOT depending on Y. RE-READ my fibre lemma: the bound is C0·‖Y‖^{−2c'}, and then I integrate
‖Y‖^{−2c'} over Y. So the constant is fixed (C0 = (nq)^{c'}·∫(Σu²)^{−c'}·2^{p(n-1)}) and ‖Y‖^{−2c'} is the
next-level integrand. GOOD. Confirm this telescoping is right and the constants are Y-independent.

OUTPUT what I should build.
</task>

<output_contract>
  Three sections:
  1. Rank F1/F2/F3 by least Lean bookkeeping; pick ONE and justify in 2 lines. State the EXACT Lean
     statement (signature) of the chosen fibre lemma, including hypotheses, in Mathlib-style.
  2. The shear/linear-map mechanics for the chosen route: which Mathlib lemma does the per-row
     change-of-variables, and how the determinant |Y_{ℓj}| (or |det|) enters. Flag if a hand-built shear
     via p copies of measurePreserving_shearAt is cleaner than a linear-map det lemma, or vice versa.
  3. Confirm (or correct) the telescoping assembly: are the constants C0,C1 Y-independent fixed reals,
     so that ∫_Y ‖Y‖^{−2c'} is the next integrand? Give the exact chain of three inequalities with the
     constants named, and the final radial_ball_iff instantiation.
</output_contract>

<grounding_rules>
  If a Mathlib lemma name is uncertain, say "verify name" rather than asserting it exists. Distinguish
  proven-mechanics from "should work". If F1's region-split in the assembly is actually heavier than I
  think (because Y is integrated and the regions interact with Tonelli), flag it.
</grounding_rules>
