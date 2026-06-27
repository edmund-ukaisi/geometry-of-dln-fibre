<task>
Lean/Mathlib RLCT proof. A SEAM INCONSISTENCY between two teammates' pieces that I need adjudicated
before I tell them the interface is broken — I may be missing how it composes.

THE STRUCTURE (DeepestGaugeChart, the producer must instantiate):
- `split : (Fin N → ℝ) ≃ₜ DeepestSplit` (MEASURE-PRESERVING `split_mp`), `split (flatDeepest) = 0`.
  DeepestSplit = (Fin nReg → ℝ) × ((Fin nM → ℝ) × (Fin nGauge → ℝ)) = (reg) × (core × spec).
- `coreAbsorb : DeepestSplit ≃ₜ DeepestSplit`, fixing reg (`(coreAbsorb q).1 = q.1`) and spec.
- `coreAbsorb_rlct`: rlctAtOn(∑reg² + coreF (coreAbsorb q).2.1) 0 = rlctAtOn(∑reg² + coreF q.2.1) 0.
- `loss_squeeze`: ∃ c₁,c₂>0, ∀ w near flatDeepest:
    c₁·Φ(w) ≤ dlnLoss(flatSymm w) ≤ c₂·Φ(w),   Φ(w) = ∑ᵢ (split w).1 i² + coreF (coreAbsorb (split w)).2.1.
  [NOTE: the regular sum is over (split w).1 — the PRE-coreAbsorb reg slot. coreF = dlnLoss_M ∘ flatSymm_M.]

TEAMMATE A (split, just landed): builds `split` MP + basepoint via an ARBITRARY finite-index partition
`Fintype.equivOfCardEq` (Fin N ≃ Fin nReg ⊕ (Fin nM ⊕ Fin nG)) + translation + relabel + unpack. The
partition is arbitrary (cardinality-matching only); its docstring says "the slot semantics (reg = pivots,
core = raw T_s, spec = rest) are NOT pinned by split — they're pinned by loss_squeeze (the other teammate)."

ME (loss_squeeze + coreAbsorb): the loss decomposes (near the deepest point) as
dlnLoss = ∑E² + ‖P11‖², where E = the product's regular RESIDUAL blocks (a NONLINEAR function of the
flat params — the gauge slice / block_elimination residuals) and P11 = the (1,1) block; the core is the
Schur complement of P11. My core_comparability_squeeze gives the c₁,c₂ bound.

THE PROBLEM I SEE: loss_squeeze's Φ uses (split w).1 (the arbitrary reg slot) as "∑E²". But split is an
ARBITRARY MP relabel — (split w).1 is just some flat coords, NOT the nonlinear regular residuals E. So
∑(split w).1² is unrelated to ∑E², and loss_squeeze (c₁·Φ ≤ loss) is FALSE. The regular residuals E are
NONLINEAR in flat coords, so NO MP relabel split can have (split w).1 = E. And coreAbsorb fixes reg
((coreAbsorb q).1 = q.1) so it can't fix it either. The gauge slice (which produces E) is non-MP, but
split must be MP — so where does E come from?
</task>

<output_contract>
Terse, decisive:
1. Is this a GENUINE interface inconsistency (loss_squeeze FALSE with an arbitrary-MP split), or am I
   missing how it composes? yes/no + one sentence.
2. If genuine: the regular residuals E are nonlinear in flat coords; the structure's Φ uses (split w).1
   (the MP-split reg slot) as the regular block. Can an MP split EVER have (split w).1 = E (nonlinear)?
   (A MeasurePreserving homeomorph can be nonlinear — is the obstruction that E is not a coordinate
   PROJECTION, or something deeper?) If an MP split CAN deliver E in its reg slot, how (what nonlinear MP
   map)? If not, why.
3. THE FIX: who must change what? Options: (a) split is NOT MP (carries the gauge slice) → breaks sub-6's
   comp_homeomorph which needs split_mp; (b) loss_squeeze's reg-sum moves to (coreAbsorb(split w)).1 and
   coreAbsorb produces E (drops coreAbsorb_regular); (c) the structure's Φ is wrong and should compare
   loss to ∑E²+core where E is a SEPARATE function (not a split slot); (d) split is a nonlinear MP map
   that genuinely puts E in its reg slot. Which is correct + minimal?
4. The cleanest consistent interface for {split MP, coreAbsorb, loss_squeeze} that makes loss_squeeze TRUE
   AND keeps sub-6 (which needs split MP) working. State it.
5. Most likely way I'm wrong (e.g. E IS expressible as an MP-split slot via some change I'm not seeing).
</output_contract>

<grounding_rules>
The loss decomposition dlnLoss = ∑E² + ‖P11‖² with E nonlinear (gauge residuals) is TRUSTED. The
question is whether the {MP split + coreAbsorb-fixes-reg + loss_squeeze-over-(split w).1} interface is
CONSISTENT, and if not, the minimal fix. Distinguish "MP forbids it" (measure obstruction) from
"projection forbids it" (E isn't a coordinate) from "it composes and I'm wrong". A nonlinear
volume-preserving homeomorph is allowed for split — factor that in.
