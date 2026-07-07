<task>
Lean 4 + Mathlib v4.29 formalisation. I must RE-SCOPE a flawed contract for a boundary "peel"
in an RLCT box-finiteness induction. I need you to adjudicate ONE design decision: the exact shape
of the per-chart peeled integral `gammaPeelIntegral`, so its two named-sorry uses are TRUE statements
(a sorry under a false statement is worse than useless).

BACKGROUND (matrix multiplication fibre / DLN RLCT):
- `M : Fin (L+3) → ℕ` a width vector; `Params M` = tuple of layer matrices; `prod M A` = their product.
- `frobSq X = ∑ᵢⱼ Xᵢⱼ²`; `matBox p n 1 = [-1,1]^{p×n}`; `paramsBoxM M 1` = all-entries-in-[-1,1] box.
- Target: `routeMLayerBoxIntegral M c' 1 := ∫_{A∈paramsBoxM M 1} frobSq(prod M A)^{-c'}  <  ⊤`
  for `c' < ½·minAdm M`, proven by strong induction on the chain length L.
- CLOSED plumbing already banked:
  * `routeMLayerBoxIntegral_front_split`: peels leftmost layer A₀ (M₀×M₁), giving the tail-outer form
      `∫_{A'∈box(tailChain M)} ∫_{A₀∈matBox M₀ M₁ 1} frobSq(rmatMul A₀ (prod (tailChain M) A'))^{-c'}`.
  * `pivotChartCover_lintegral_le_sum {m n} (t) (f)`:
      `∫_{A₀ ∈ {A | t ≤ A.rank}} f A₀  ≤  ∑_{ρ:Fin t↪Fin m} ∑_{κ:Fin t↪Fin n} ∫_{A₀ ∈ pivotChart ρ κ} f A₀`
      where `pivotChart ρ κ = {A₀ | IsUnit (A₀.submatrix ρ κ)}` (the t×t (ρ,κ)-minor is a unit).
  * `frobSq_schur_block_split (A B C D) [Invertible A] (Q)`:  (EXACT pointwise, no measure theory)
      `frobSq (fromBlocks A B C D * Q)
        = frobSq (A * Q̃_p) + frobSq (C * Q̃_p + Γ * Q_b)`,
      `Q̃_p := Q_p + A⁻¹ B Q_b`, `Q_b := Q.submatrix Sum.inr id`, `Q_p := Q.submatrix Sum.inl id`,
      `Γ := schurCompl A B C D = D − C A⁻¹ B`.
  * `measurePreserving_shearSub {α β} (hK : Measurable K)`:
      `(x, D) ↦ (x, D − K x)` is measure-preserving on `α × β` (β an additive group w/ right-inv volume).
      Concrete `Fin`-space instance `measurePreserving_coreShear` also banked.
  * complement equiv: from `ρ : Fin t ↪ Fin M₀`, Mathlib gives `Fin t ⊕ ↥(Set.range ρ)ᶜ ≃ Fin M₀`
    via `ρ.toEquivRange` + `Equiv.Set.sumCompl (Set.range ρ)`.

THE FLAW (triple-confirmed by reviewer + 2 decorrelated Codex passes) in the OLD def:
  OLD `gammaPeelIntegral M t c' := ∫_{A'∈box(tail)} ∫_{Γ∈matBox (M₀−t)(M₁−t) 1}
         (frobSqTopRows t Q + frobSq (Γ · Q_b))^{-c'}`,  Q = prod(tailChain M) A', sum over t∈range(min+1).
  Three defects:
   (1) t=0 CIRCULARITY: at t=0 the pivot is 0×0, so this integral degenerates to the WHOLE box integral,
       i.e. the finiteness sorry `sjJointResolution M _ 0 c'` IS the induction goal → circular. Fix: sum
       range must be t = 1..min(M₀,M₁), and the {rank=0} point A₀=0 is null so {rank≥1}=box a.e.
   (2) Only indexed by t, but a chart genuinely selects an arbitrary (ρ,κ) column/row subset → different
       integral. Fix: index the per-step object by (t,ρ,κ), fold finite chart count into constant C.
   (3) UNFAITHFUL integrand: it (a) DROPPED the cross-term `C·Q̃_p` (bottom block is really
       `C·Q̃_p + Γ·Q_b`, not `Γ·Q_b`), (b) replaced the top block by `frobSqTopRows t Q` (= `‖Q_p‖²`)
       instead of the true `‖A·Q̃_p‖²` (A the near-singular pivot block), (c) used a CLEAN box for Γ
       instead of the shear-image domain `{Γ | Γ + C·A⁻¹·B ∈ D-box}`.

THE REQUIRED FIX (per the controller): make `gammaPeelIntegral` FAITHFUL — carry the true cross-coupled
integrand `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{-c'}` with Γ over the shear-image domain, per-(t,ρ,κ), sum
t=1..min. Then:
  sjBoundaryPeel:  routeMLayerBoxIntegral M c' 1 ≤ ∑_{t=1..min} ∑_{ρ} ∑_{κ} C · gammaPeelIntegral M t ρ κ c'
  sjJointResolution (GIVEN box-finiteness IH for all shorter chains): gammaPeelIntegral M t ρ κ c' < ⊤.
sjBoundaryPeel is acknowledged a multi-hundred-line measure-plumbing WALL (likely a sorry this tide);
sjJointResolution is deferred (needs a Gram/corank atom not on this branch). BOTH will be sorries — so
what matters THIS tide is that the DEFINITION makes both statements TRUE, and the recursion spine
(sjResolutionStep_proof composing them; strong-induction wrapper) is sorry-free.

THE DESIGN FORK I need you to adjudicate — two candidate definitions of `gammaPeelIntegral M t ρ κ c'`:

CANDIDATE A ("sheared block-coordinate", matches the controller's literal instruction):
  Integrate over the tail A' AND the block variables A (t×t), B (t×(M₁−t)), C ((M₀−t)×t), Γ ((M₀−t)×(M₁−t)),
  with Γ over the shear-image domain `{Γ | Γ + C·A⁻¹·B ∈ [-1,1]^{(M₀−t)×(M₁−t)}}`, A/B/C over their sub-boxes,
  integrand `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{-c'}` with Q_p/Q_b the (ρ,κ)-reindexed row-split of Q.
  Requires: subtype complement types `↥(range ρ)ᶜ` (NOT `Fin (M₀−t)` syntactically), a 4-fold block integral
  with a nontrivial (A,B,C-dependent) Γ-domain. sjBoundaryPeel then needs a reindex-of-matBox-through-(ρ,κ)
  measure-preserving + the shearSub instantiation (the "wall").

CANDIDATE B ("raw chart contribution", provably-equal to A but tractable):
  `gammaPeelIntegral M t ρ κ c' := ∫_{A'∈box(tail)} ∫_{A₀ ∈ matBox M₀ M₁ 1 ∩ pivotChart ρ κ}
       frobSq (rmatMul A₀ (prod (tailChain M) A'))^{-c'}`.
  This is LITERALLY the (t,ρ,κ)-chart's contribution to the box integral — no dropped term, no clean box,
  exact frobSq(A₀·Q). By `frobSq_schur_block_split` (on the chart, where the pivot block is invertible) it
  EQUALS the cross-coupled `(‖A·Q̃_p‖²+‖C·Q̃_p+Γ·Q_b‖²)^{-c'}` form; the shear/Γ-free-variable/shear-image
  reformulation becomes a downstream lemma consumed by sjJointResolution. sjBoundaryPeel is then just
  `routeMLayerBoxIntegral_front_split` + `pivotChartCover_lintegral_le_sum` (t≥1, {rank=0} null) — CLOSABLE
  this tide (the finite-sum reindex over t and (ρ,κ) charts). t=0 still excluded (chart=whole box → circular).
</task>

<output_contract>
1. VERDICT (1 line): pick A or B for the DEFINITION this tide, given the goal is a faithful def + a
   sorry-free recursion spine + closing sjBoundaryPeel if reachable.
2. FAITHFULNESS CHECK (≤6 lines): is Candidate B a genuinely FAITHFUL/TRUE object for sjBoundaryPeel
   (`box ≤ ∑ C·gammaPeelIntegral`) and sjJointResolution (`< ⊤`)? Is the C constant needed for B, or is B
   an equality (C=1) with the box integral over {rank≥1}? Flag any way B's statement could be FALSE.
3. WELL-FOUNDEDNESS (≤4 lines): confirm/deny that with B and t=1..min, sjJointResolution at t≥1 is NOT
   circular (does the chart integral for t≥1 genuinely reduce to shorter chains, unlike t=0=whole box?).
   Is there any t≥1 chart that still equals the whole box (would re-introduce circularity)?
4. RISK on A (≤4 lines): the single biggest Lean-definability or truth risk if I follow A literally.
5. If B: the precise statement of the downstream lemma (B = sheared cross-coupled form) that
   sjJointResolution will consume, so I can pin it as an `example`/named sorry now. (≤5 lines)
Keep total under ~35 lines. Mark any claim that is inference vs. a fact you're confident of.
</output_contract>

<grounding_rules>
This is a design adjudication, not a proof. You may reason from the stated lemma signatures (treat them as
accurate). Where you INFER truth of a statement vs. KNOW a Mathlib fact, say which. Do not invent Mathlib
lemma names; if you reference one, mark it "verify". The decisive criterion is: which definition makes
sjBoundaryPeel + sjJointResolution TRUE statements (honest sorries) with the least risk of a false skeleton.
</grounding_rules>
