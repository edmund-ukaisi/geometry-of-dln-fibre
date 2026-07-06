<task>
Lean 4 + Mathlib (v4.29) formalisation. I must prove ONE theorem (the "crux") for the L=2 DLN
learning-coefficient (Aoyagi/Watanabe RLCT). Everything ELSE is already wired + green (axiom-clean).
I want your DIAGNOSIS of the MINIMAL, LOWEST-RISK decomposition — not code.

SETTING. `Params H := ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ` (L=2, so H : Fin 3 → ℕ).
`prod H A = A₀·A₁` (matrix chain). `dlnLoss H B A = ‖prod H A − B‖²_F` (sum of squares). `rlctAt`/`rlctAtOn`
= the local real-log-canonical-threshold (a sSup over admissible exponents with a finite-integral condition;
lower c is smaller RLCT). Optimal set = fibre {A | prod H A = B}, rank B = r, all widths > r.

THE CRUX (statement, already stated + accepted, currently `sorry`):
  d1ge_L2_hAtV_explicit (H : Fin 3 → ℕ) (r) (B) (v : Params H) (hopt : prod H v = B) (hB : B.rank = r) :
    ∃ P : Params (H−r),
      (nRegL2 H r : ℝ≥0∞)/2 + rlctAtOn (fun A => dlnLoss (H−r) 0 A) P  ≤  rlctAt H (dlnLoss H B) v
  where nRegL2 H r = r*(H0 + H2 − r), and (H−r) s = H s − r (reduced widths).

WHY this shape closes the leg (already proven, green): banked bridge `deepest_le_of_optimal_via_L2_ge`
+ my just-proven `core_zero_le_of_params` (Aoyagi Thm 4 on the EXPLICIT core: rlctAtOn(dlnLoss(H−r)0) 0 ≤
rlctAtOn(dlnLoss(H−r)0) P, ANY P — via degree-2L homogeneity + the ray-scaling/lsc lemmas, clean-three)
+ the deepest value (#44 + banked R1). So the crux only needs SOME reduced-core point P with the ≥.

WHAT IS ALREADY BANKED / GREEN and reusable:
1. `rlctAt_ge_nReg_add_slice_of_residual` : GIVEN a C¹ residual `q : (Fin m→ℝ)×Y → EuclideanSpace ℝ (Fin n)`
   and a chart transfer `hchart : rlctAt H (dlnLoss H B) v = rlctAtOn (fun p => (∑ p.1 i²)+(∑ q p i²)) (0,t0)`
   plus slice a.e.-nonzero, PRODUCES `(m:ℝ≥0∞)/2 + rlctAtOn (fun t => ∑ q(0,t) i²) t0 ≤ rlctAt v`.
2. `dln_hchart_residual` : PRODUCES such a `q`,t0,hchart at m=nRegL2 — BUT its residual `q` is defined
   through an EXISTENCE-ONLY IFT inverse `Ψsymm` (from `rlctAtOn_eq_of_contDiff_chart_rinv`): q(p) =
   (prod H (gmapAt v (Ψsymm(split⁻¹ p))) − B) at non-selected entries. Ψsymm has NO closed form / retains
   NO algebraic tie to dlnLoss. VERDICT of two prior tides + Codex: `rlctAtOn(slice-of-q) t0` is
   germ-unpinned — CANNOT be identified with (or lower-bounded by) rlctAtOn(dlnLoss(H−r)0)(any point).
   (Counterexample level: x²+u⁴ peels to slice u⁴, rlctAtOn=1/4, invisible to any finite-jet data.)
3. `rlct_additive_smooth_block` : rlctAtOn(∑xᵢ² + G²)(0,y0) = n/2 + rlctAtOn(G²) y0 (G measurable + a.e.≠0 nbhd).
4. `rlctAtOn_comp_homeomorph` : rlctAtOn(F∘e) w0 = rlctAtOn F (e w0) for e a measure-preserving homeomorph
   + measurable-embedding.
5. `rlctAtOn_unit_invariant_aux` : rlctAtOn(u·F) w* = rlctAtOn F w* for u a bounded-above-and-below
   POSITIVE unit near w* (measurable).
6. `block_elimination` : ∃ invertible P,Q with P·B·Q = diag(E_r,0) (explicit normal form).
7. The DEEPEST-POINT analogue `deepest_regular_core_reduces_frontPivot` : rlctAt(deepestPoint) =
   nReg/2 + rlctAtOn(dlnLoss(H−r)0) 0 — proven via an explicit gauge-slice chart `DeepestGaugeChart`
   (a multi-file build). It lands the residual EXACTLY on dlnLoss(H−r)0 at the ORIGIN (deepest = rank-r-exact
   layers). The general-v obstruction: v's layers can be HIGHER rank, so the deepest gauge chart
   (which rides rank-r-exact pivot structure) does not directly transfer.

COORDINATOR + a decorrelated exact-algebra witness (modelidwit) established (for the SECOND-peel form):
- The reduction UNIT U is BOUNDED + NON-VANISHING (Gram-sandwich; = the selected extra×extra minor ≠0 at
  basepoint). Clean, no order-4 pathology.
- The identification map φ is a SUBMERSION, NOT a diffeomorphism: there IS a dimension gap. After peeling
  the nReg regular block, the slice residual depends on exactly dimParams(reduced core) essential coords;
  the remaining coords are FLAT (e.g. flatDim−nReg−dimParams(H−r) = r(2H1−r) = 7 for (4,4,4)/r=1).
  Correct shape: R(z) = U(z)·(dlnLoss(reducedcore) 0)(φ(z)), U bounded±, φ submersion, R independent of
  the flat coords. Then rlctAtOn R = rlctAtOn(reducedcore-loss)(essential pt) via a FLAT-DIRECTION FUBINI
  RLCT lemma `rlctAtOn (g∘proj) w = rlctAtOn g (proj w)` + peeling U + the linear/IFT part.

MY QUESTION. I am on ROUTE A (land on dlnLoss(H−r)0 at a general point P, dominated by Thm 4 which I
already have), NOT the degraded-core Route B (dlnLoss(M') 0, needs R1@M'). For Route A the crux reduces to:
produce an EXPLICIT first peel whose slice residual R satisfies rlctAtOn R t0 = rlctAtOn(dlnLoss(H−r)0)(some P),
via: bounded-U peel (5) + flat-direction Fubini (new brick) + a linear reindex (4). The abstract `dln_hchart_residual`
residual (2) is unusable. So I must build a NEW explicit residual q with q(p) EXPLICITLY = (up to bounded U +
flat projection + linear reindex) the reduced-core loss composed with an EXPLICIT (polynomial/rational,
unit-Jacobian) corner-elimination map — NO Ψsymm.
</task>

<output_contract>
Answer in <=900 words, these sections:
1. VERDICT: Is Route A (first-peel-only, land on dlnLoss(H−r)0 at a general P, dominate by Thm 4) actually
   SOUND and STRICTLY SIMPLER than the two-peel degraded route? Any hidden obstruction? (esp: is the FIRST
   corner-elimination peel enough to land on dlnLoss(H−r)0, or does the "higher-rank layers at v" force a
   second reduction even in Route A?)
2. THE EXPLICIT FIRST PEEL: the cheapest concrete construction of the explicit residual q (no Ψsymm) for
   L=2. What is the explicit coordinate change (corner elimination at v's chosen invertible r-minor)? What
   is φ, U, and the flat projection concretely (matrix-block terms)? Does q need the IFT AT ALL, or is it a
   purely algebraic (polynomial-in-entries + rational-in-the-minor-det) global map on the chart open set?
3. THE FLAT-DIRECTION FUBINI RLCT LEMMA: precise statement to build in Lean, and the cleanest proof route
   from a sSup/finite-integral RLCT def (is it a genuine Fubini/Tonelli argument, or does it follow from
   `rlctAtOn_comp_homeomorph` composed with a product-projection trick? beware: a projection is NOT a
   homeomorph). Rank it: is this the single load-bearing new brick, or are there others?
4. DECOMPOSITION + RISK: ordered list of the sub-lemmas for the crux, each tagged
   [reuse-banked | new-clean | new-risky], with the ONE most likely to be a hidden wall flagged.
5. If you think Route A secretly re-collapses to needing the degraded R1@M' or a second peel, SAY SO
   plainly and say why.
</output_contract>

<grounding_rules>
Distinguish what you can DERIVE (matrix algebra of the corner elimination — do this concretely) from what
you INFER about Lean feasibility. Flag any step where you are guessing about Mathlib API availability.
The RLCT is genuinely germ-sensitive: do not hand-wave any step that silently discards higher-order data.
</grounding_rules>
