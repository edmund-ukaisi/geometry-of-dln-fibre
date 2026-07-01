<task>
Lean4/Mathlib. Final piece of a DLN box-divergence det: prove |det DB| = 1 where DB is the fderiv of a
SYMBOLIC-dimension boundary factor at deepRank=0. Need the CLEANEST Lean route (least lines, robust to
opaque M0,M1,M2). All below is banked/proved except this |det DB|=1.

CONTEXT:
- M : Fin 3 → ℕ. deepRank=0 means Text M (tach M) 2 = 0 (call it hdr0). minAdm = M0*M1.
- BchartE ha y := paramsEquivFlat M (BparamsE ha y), where
  BparamsE ha y := chartParamsGen 1 M (tach M) (genBlkFlatLive M (tach M) ha 0 y) hle.
  I.e. the radial-1 chart reading the E-block DIRECTLY via readE (plain live decoder, leaf rfin=0).
- I have proved BchartE_differentiableAt (BchartE is differentiable everywhere).
- I need: |LinearMap.det (fderiv ℝ (BchartE ha) z).toLinearMap| = 1  for z = pivotBlowupOn ... u.
- At deepRank=0, K/X/N blocks at boundary 1 are all 0-dimensional (Text 2 = 0): K:0x0, X:M0x0, N:0xM1.
  So the Schur frame schurFrameProd 1 K X N (readE) DEGENERATES: bottom-right block = X*K*N + 1*E, and
  X*K*N=0 (inner dim Fin 0), so A0 = the E-block read directly; A1 = the W-block/chainA structure.
  So BparamsE is LINEAR in y (no K/X/N products); chartParamsGen 1 is affine-linear in y.

TWO CANDIDATE ROUTES (both precedented in the codebase; which is cheaper for SYMBOLIC M?):

ROUTE A — coordinate-pack (RouteM4422 template): show BchartE = paramsEquivFlatCLE ∘ packCLM where
packCLM : (Fin N → ℝ) →L[ℝ] Params M is a coordinate PERMUTATION (each Params entry = one input coord),
then |det(paramsEquivFlatCLE ∘ packCLM)| = 1 because paramsEquivFlat is measure-preserving
(measurePreserving_paramsEquivFlat is banked) and packCLM is a coordinate permutation (|det|=1).
PROBLEM: RouteM4422 hardcodes explicit Fin 28 slot tables (decide). For symbolic M0,M1,M2 I cannot write
explicit tables. Is there a SYMBOLIC way to express packCLM as a permutation and get |det|=1 without
enumerating slots? (e.g. via an Equiv (Fin N) FlatIdx built abstractly, LinearMap.det of a permutation
matrix = ±1.) How hard is the symbolic permutation-det in Lean v4.29?

ROUTE B — reuse the banked Dtot machinery. There is a banked lemma for the LEAF chart (BchartLeaf, a
DIFFERENT leaf reader):
  BchartLeaf_abs_det_free : |det (fderiv (BchartLeaf ha) y₀)| = |det (readK y₀ 0)|^{r+c}  (given hreg).
It routes through Bchart_abs_det_eq_Dtot + Dtot_abs_det_free (an eihd/Dtot reindex). If an analogous
BchartE_abs_det lemma held, then at deepRank=0 readK y₀ 0 is a 0x0 matrix so |det (0x0)| = 1 and
1^{r+c} = 1, giving |det DB|=1 immediately. QUESTION: is the Dtot machinery keyed to BchartLeaf's specific
leaf reader, or is it generic to "radial-1 chart of a live decoder"? i.e. could BchartE reuse
Bchart_abs_det_eq_Dtot / Dtot_abs_det_free with minimal change, OR is deriving a BchartE-analog as heavy
as Route A?

ROUTE C — is there something even simpler I am missing? e.g.:
- Since BchartE is affine-linear (deepRank=0, no nonlinearity), fderiv(BchartE) z is a CONSTANT linear map
  L = paramsEquivFlatCLE ∘ (linear part of BparamsE). Maybe |det L| = 1 follows from
  |det paramsEquivFlatCLE| = 1 (measure-preserving ⟹ |det|=1 — is this banked or 1-line derivable?)
  times |det (linear part of BparamsE)| = 1. The linear part of BparamsE: is it a coordinate permutation
  composed with the reindex, hence |det|=1? Could I prove |det (fderiv BparamsE z)| = 1 by showing
  fderiv(BparamsE) as a Params-valued linear map is measure-preserving / a relabeling?
- OR: evaluate the WHOLE chart det at a chosen point via radialComp_abs_det_at BACKWARDS: I already have
  |det Dφ(u)| = |u_p|^{minAdm-1}·|det DB|. If I ALSO compute |det Dφ(u)| by a DIFFERENT decomposition
  (e.g. φ is itself affine at deepRank=0 up to the radial, so its det is directly |u_p|^{minAdm-1}), I
  could conclude |det DB|=1. Is φ = eDeepRank0Phi expressible as (a fixed linear reshape) ∘ pivotBlowupOn
  with the reshape |det|=1, computed WITHOUT going through B? (This is basically Route A applied to φ not B.)

QUESTIONS:
1. Rank the routes A/B/C by expected Lean effort for SYMBOLIC M0,M1,M2 (opaque). Which is cheapest?
2. For the chosen route, give the KEY lemma chain (3-6 named steps) and the single hardest sub-lemma.
3. Is |det paramsEquivFlatCLE M| = 1 banked or cheap to derive from measurePreserving_paramsEquivFlat?
   (A measure-preserving continuous linear equiv on Fin n → ℝ has |det| = 1 — what Mathlib lemma?)
4. The biggest risk / most likely Lean wall for the chosen route.
</task>

<output_contract>
Q1: rank A/B/C with 1-line rationale each. Q2: the lemma chain for the winner + hardest sub-lemma.
Q3: yes/no + the Mathlib lemma name for measure-preserving-linear ⟹ |det|=1. Q4: the wall.
End VERDICT (2 lines): the ONE route to build + the ONE lemma to prove first.
</output_contract>

<grounding_rules>
Distinguish banked-fact from inference. If you name a Mathlib lemma, flag if you are unsure it exists at
v4.29 (I will verify with scripts/lean-search). The goal is minimal robust Lean, not elegance.
