<task>
Confirm the right Lean 4 + Mathlib architecture for the ∀M family-parametric lift of the
boundary-SMEARED achiever box-divergence atom for the (r,c)=(1,1) family (34 deep-linear-network
dimension vectors M), and identify the biggest risk. This is an architecture decision BEFORE a
multi-hundred-line build — I must not pick the wrong substrate.
</task>

<context>
SETTING. A node M=(M_0,...,M_L). The "(1,1) smeared family" (34 cases, L∈{2,3,4}) has r:=deepRank=1,
c:=M_L=1, s:=m1−r where m1:=M_{L−1}, minAdm=r·c=1. The achiever loss F=‖P·A^{L−1}‖² factors as
F=z²·U with U=‖P_1·H̄‖², where P=A^0···A^{L−2} is the FRONT PRODUCT (M_0×m1), P_1=P[:,:1] (its first
column, full rank 1), Λ_0=(P_1ᵀP_1)⁻¹P_1ᵀP_2 (1×s, SCALAR Gram), and the deepest factor
A^{L−1}=[z·H̄−Λ_0·S_bot ; S_bot]. minAdm=1 ⟹ NO radial (weight 1); the chart is just the scalar shear.

I have THREE completed concrete-width validate-smalls (all sorry-free, S2-free):
- (1,2,1) [L=2]: the (1,1)-family template, via `routeMCore_box_diverges_of_MPChart` (weight-1 route):
  φ = Q∘shear, Q∘shear measure-preserving + measurable embedding. CRITICALLY it uses a PER-M explicit
  reshape: `pack121 : (Fin 4 → ℝ) → Params M121` (a hand-coded Fin-4 → matrix-slot map) +
  `fin4EquivFlatIdx121` (an explicit Fin 4 ≃ FlatIdx M121 `match`). The shear MP uses an explicit
  Fin-4 `split121` peel.
- (2,3,1), (1,3,2): same per-M `pack`/`finNEquivFlatIdx`/`splitN` explicit-reshape architecture at Fin 9.

THE PROBLEM with generalizing the (1,2,1) template to ∀ (1,1)-family M:
- L varies (2 cases L=2, 8 L=3, 24 L=4). For L≥3 the front P=A^0·A^1·... is a MATRIX PRODUCT (not a
  single matrix), so P_1 (its first column) is a degree-(L−1) polynomial in the front coords.
- The pivot location varies (the bottleneck front layer M_k=1 is at k∈{0,1,2}).
- flatDim M varies (4..15+). The per-M `pack`/`finNEquivFlatIdx`/`splitN` explicit reshapes do NOT
  generalize over varying L/flatDim — they are hand-coded per fixed width.

THE PRECEDENT — the BOUNDARY-CLEAN ∀M lift (already done, sorry-free). It does NOT use a per-M reshape.
"Option A" (in `RouteMBoundaryCleanRate.lean`): the chart is the GENERIC flat→flat radial blow-up
`cleanPhi := pivotBlowupOn (deepestCoords M hL) (deepestPivot M hL)` — NO outer reshape. det/cov are
the generic `pivotBlowupOn` lemmas. The RATE is decoded ONCE generically via:
  * `paramsEquivFlat_symm_decode` (`=rfl`): reads the (s,i,j) Params slot of `(paramsEquivFlat M).symm x`
    off the flat coord `flatCoordOf q`;
  * `flatCoordOf_mem_deepestCoords_iff`: membership is the only coordinate fact;
  * then "the deepest layer of the decoded Params is `u_p •` its pivot-stripped form, earlier layers
    untouched, so prod = u_p • (prefix·M̄)" ⟹ rate = (u_p)²·‖prefix·M̄‖². The front product
    `prefix·M̄` is NEVER built explicitly — `u_p` factors out of the LAST factor and `LossHomogeneity`
    handles the rest. (CLEAN has r=m1 so NO shear — pure radial.)

MY READ: the ∀M SMEARED (1,1) lift should adopt the CLEAN Option-A flat-coordinate architecture
(generic `deepestCoords`/`deepestPivot`/`paramsEquivFlat_symm_decode` + `LossHomogeneity`), NOT the
per-M `pack`-reshape of my validate-smalls — because only the flat-coordinate generic route survives
varying L/flatDim. The genuinely-new piece vs CLEAN: a GENERIC flat SCALAR-SHEAR (the Λ_0-shear keyed
on the smeared structure) inserted before the (here trivial, minAdm=1) radial, and a generic rate
showing the scalar shear cancels (P_1·Λ_0=P_2) so prod = u_p·(prefix·[1]) — reusing the CLEAN decode
machinery for everything except the shear-cancellation step.

QUESTIONS:
1. Is my read correct that the per-M `pack`-reshape architecture of the validate-smalls CANNOT
   generalize over varying L, and the ∀M lift MUST adopt the flat-coordinate Option-A architecture?
   Or is there a way to make the per-M reshape itself parametric in L (a `pack`/`finNEquivFlatIdx`
   defined generically by recursion on L) that I'm underrating?
2. For the SMEARED rate in flat coordinates: the CLEAN rate factors u_p out of the deepest factor and
   leaves `prefix·M̄` abstract. The SMEARED rate additionally needs the shear-cancellation P_1·Λ_0=P_2
   to telescope the deepest product. At r=1 (scalar Gram, Λ_0=P_1⁻¹P_2 elementwise) — can this
   cancellation be stated/proven GENERICALLY in flat coords (reusing `paramsEquivFlat_symm_decode`),
   or does it require the explicit front-product P_1 (degree-(L−1) polynomial) which defeats the
   generic route?
3. The shear MP: the CLEAN chart is a pure `pivotBlowupOn` (measure-preserving by the generic lemma,
   no shear). The SMEARED needs the flat scalar-shear to be measure-preserving. Generically (varying
   flatDim), is the flat shear `x ↦ x + (shift reading the front coords)·(at the deepest-pivot coord)`
   measure-preserving by a GENERIC argument (it's a triangular/transvection shift), or does each M
   need an explicit `splitN`/`coreShear` peel (which doesn't generalize)?
4. Biggest risk to flag for the controller, and a recommended FIRST sub-target (the smallest generic
   lemma to build that proves the architecture is viable before the full lift).

Be concrete about which existing generic infrastructure (deepestCoords/deepestPivot/Text/minAdm/
paramsEquivFlat_symm_decode/LossHomogeneity/S1G5Charts pivotBlowupOn) the smeared lift reuses, and
what is genuinely NEW. Mathlib v4.29.
