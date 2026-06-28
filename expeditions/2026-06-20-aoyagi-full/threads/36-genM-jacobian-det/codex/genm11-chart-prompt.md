<task>
Lean 4 + Mathlib v4.29, DLNFibre harness. I am building the ∀M-(1,1)-smeared Option-A CHART (the rate
leg of an RLCT lower bound). I have LANDED two substrates; I need the cleanest architecture to combine
them, and a verdict on the single biggest risk.

SUBSTRATE A — the CLEAN radial chart (`RouteMBoundaryCleanRate.lean`), a GENERIC flat→flat map:
- `cleanPhi M hL hne := pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL hne)` — a pure radial
  blow-up keyed on the deepest layer's flat coords; pivot coord `p := deepestPivot`.
- `cleanParams M hL hne u := (paramsEquivFlat M).symm (cleanPhi … u)` — the Params tuple.
- KEY LANDED rate: `routeMCore_cleanPhi : routeMCore M (cleanPhi … u) = (u p)^2 * dlnLoss M 0 (unblownParams … u)`.
  (Mechanism: `cleanParams = scaleLayer u_p (deepLayer) (unblownParams)`; the deepest layer is u_p-scaled,
  earlier layers untouched; `prod_scaleLayer` + `dlnLoss_homogeneous_layer` pull u_p^2 out.)
- `routeMCore M x := dlnLoss M 0 ((paramsEquivFlat M).symm x)`.

SUBSTRATE B — the LANDED front fact (`RouteMFrontBottleneck.lean`), for the (1,1)-smeared family
(minAdm=1, r=1, m1=M_{L-1}≥2):
- `prodAux_frontScalarShear_cancel`: for the front product P = prodAux M A (L-1) with a width-1 layer
  at p* (M⟨p*⟩=1), off the pole ‖col0‖²≠0, the pivot column P₁=P[:,0:1] and any residual block P₂
  (columns of P selected by σ) satisfy P₁·((P₁ᵀP₁)⁻¹P₁ᵀP₂) = P₂.

THE SMEARED CHART adds, vs CLEAN, a SCALAR SHEAR at the deepest-pivot coord that reads the FRONT coords:
the deepest layer A^{L-1} (m1×1, since M_{L-1}=m1, Text(L)=r=1, deepest column-count c=1) gets its
"routing" entries shifted by Λ₀ = (P₁ᵀP₁)⁻¹P₁ᵀP₂ (front coords). The validate-small (1,2,1) does this
per-M: A1 = [z − (b/a)·sb ; sb], i.e. the pivot row is z minus the shear (b/a)·(residual), the residual
rows are free. The rate then telescopes: P·A^{L-1} = u_p·(P₁·H̄), so F = u_p²·‖P₁H̄‖² = u_p²·U, OFF the
pole. The front fact P₁·Λ₀=P₂ is exactly what cancels the shear.

GOAL: define a GENERIC sheared flat→flat chart `phiSm M hL hne u` and prove
  `routeMCore M (phiSm … u) = (u p)^2 * U(u)`  (off the pole),  U(u) ≥ 0 measurable,
then it is measure-preserving (the shear has det 1; the radial part is trivial since minAdm=1 ⟹ no
radial), so I can feed `routeMCore_box_diverges_of_MPChart` (a LANDED generic-M assembly taking a
source sub-box certificate).

What I have considered (two architectures):
(A) "shear ∘ cleanPhi": phiSm := cleanPhi ∘ shear, where `shear` is a measure-preserving flat self-map
    that injects the Λ₀-shear into the deepest-layer pivot coords (reading the front coords). Then
    routeMCore(phiSm u) = routeMCore(cleanPhi (shear u)) = (shear u) p ^2 · dlnLoss(unblown(shear u)),
    and the shear must be designed so this collapses to (u p)²·U via the front fact. This is the
    validate-small's `phi121sm = Q121 ∘ shear121` route.
(B) define the sheared Params tuple directly (deepest layer = pivot-scaled MINUS Λ₀·residual; earlier
    layers free), flatten via paramsEquivFlat, and prove the rate by a direct dlnLoss computation
    reusing prodAux_frontScalarShear_cancel — NOT routing through cleanPhi's scaleLayer machinery.
</task>

<output_contract>
1. RECOMMEND (A shear∘cleanPhi, B direct sheared Params, or C hybrid). Decisive criterion: which
   minimizes NEW infrastructure given I already have routeMCore_cleanPhi (substrate A) and the front
   fact (substrate B), AND keeps the measure-preserving proof cheapest (det-1 shear).
2. For the recommended route: the exact sequence of lemmas to state (signatures sketch), in dependency
   order. Identify which can reuse cleanParams_eq_scaleLayer / prod_scaleLayer / dlnLoss_homogeneous_layer
   vs which are genuinely new. Flag where prodAux_frontScalarShear_cancel plugs in.
3. The measure-preserving leg: how to define the generic det-1 shear over `Fin (routeMAmbient M) → ℝ`
   so `measurePreserving_shearAt`-style (single-coordinate polynomial shear, MP via skew_product) gives
   MP at arbitrary pivot p. Is a SINGLE shearAt enough, or do I need a finite product of shears (one per
   residual coordinate the routing reads)?
4. The SINGLE biggest risk / wall on the recommended route — be concrete (a cast, a measurability, the
   pole handling, the abstract front product P = prodAux M A (L-1) degree-(L-1) expansion). Is there a
   design subtlety the (1,2,1) validate-small does NOT cover that I should surface rather than grind?
</output_contract>

<grounding_rules>
Mark Mathlib lemmas you are unsure exist at v4.29 as "verify". Distinguish "exists" (fact) from "should
exist" (inference). Prefer routes reusing the LANDED substrates A+B over routes needing fresh analysis
API. The rate is needed OFF the pole only ({‖col0‖²=0} is Lebesgue-null; the cov/leaf_integrand see it
a.e.) — do NOT propose proving an ∀u rate (the validate-small's pole witness shows it fails on the pole).
</grounding_rules>
