<task>
Lean 4 / Mathlib v4.29 formalisation. I must discharge two named hypotheses of a banked headline
theorem GENERICALLY over opaque widths at depth L=2. I want a decorrelated review of my ARCHITECTURE
choice for the dominant cast-heavy piece (the "DECODE") before I spend multi-day compute.

SETUP (all banked, sorry-free):
- `M : Fin 3 → ℕ` are opaque layer widths; `r s : ℕ` with `hrs : r + s = M 1`.
- `Params M := ∀ s : Fin 2, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ` (2 layer matrices, L=2).
- `routeMAmbient M = flatDim M = Σ_s (M s.castSucc)*(M s.succ)`, the total flat dim.
- `paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ)` is a measure-preserving MeasurableEquiv.
- BANKED RATE CORE: `routeMCore_phiL2 M hrs A0 z Hbar Sbot Λ₀ P₁ P₂ hP₁ hP₂ hcancel :
   routeMCore M (phiL2 M hrs A0 z Hbar Sbot Λ₀) = z^2 * ∑ i, ∑ j, ((P₁ * Hbar) i j)^2`,
  where `phiL2 M hrs A0 z Hbar Sbot Λ₀ := paramsEquivFlat M (chartL2Params M hrs A0 z Hbar Sbot Λ₀)`,
  and `chartL2Params` builds `Params M` as `Fin.cons A0 (Fin.cons (chartL2Deep …) elim0)` with the deepest
  factor row-split (top r rows = z·Hbar − Λ₀·Sbot, bottom s rows = Sbot), all via `deepWidthEquiv hrs :
  Fin r ⊕ Fin s ≃ Fin (M 1)`. hP₁/hP₂ say P₁,P₂ are column-blocks of A0 (selected by deepWidthEquiv);
  hcancel : P₁ * Λ₀ = P₂ is the shear cancellation (supplied by banked `frontShear_cancel_general`).

THE HEADLINE (banked) `routeMCore_box_diverges_smearedL2` reduces the box-divergence to per-family
chart facts on a CONDITIONED box `condBox (hN ▸ p) (fun k => box (hN ▸ k)) δ`. Two genuinely-new
hypotheses over opaque widths:
 (1) THE PEELED RATE: provide concrete flat maps `ψ R : (Fin (routeMAmbient M)→ℝ)→(Fin(routeMAmbient M)→ℝ)`
     and prove `routeMCore M (ψ (R (hN ▸ (Fin.insertNth p z y)))) = z^2 * Uy y` on the conditioned box,
     plus ψ measure-preserving + measurable-embedding, R = a radial blow-up `pivotBlowupOn` (banked
     det/injOn/fderiv), Uy measurable+positive.
 (2) FIELD A: containment `condBox ⊆ (ψ∘R)⁻¹(cubeBox ε)` + a generic conditioned Λ₀-bound (analytic).

THE WORKED PRECEDENT is `(2,3,1)` (r=2,s=1,c=1, all `Fin 9`, `!![...]`, 1126 lines), fully concrete:
`ψ := paramsEquivFlat ∘ pack231 ∘ shear231`, `R := pivotBlowupOn {6,7} 6`. The KEY decode lemma is
`chartParams231_eq_pack_shear_R : chartParams231 u = pack231 (shear231 (R231 u))` (funext s; fin_cases s
over the 2 LAYERS; inside each layer reduce pack/shear/R coordinatewise).

THE GAP-1 FINDING (sympy-verified): the contract's R=pivotBlowupOn sends the rc deepest flat coords
(z,h₁,…) ↦ (z, z·h₁, …); reshaped, the deepest top block is z·H̄_unit (pivot entry fixed=1). So the DECODE
target is `(paramsEquivFlat M).symm (ψ(R u)) = chartL2Params M hrs A0 z H̄_unit Sbot Λ₀` (Hbar := H̄_unit),
i.e. equivalently `ψ(R u) = phiL2 M hrs A0 z H̄_unit Sbot Λ₀`. Then routeMCore_phiL2 gives the rate.

THE DOMINANT COST (flagged by the prior tide): there is NO banked coordinate-level form of `shearM` —
only its measure-preserving form `measurePreserving_shearM coreSet shift hshift` (built as
`splitOfCoreSet.symm ∘ coreShear[shift] ∘ splitOfCoreSet`). I have banked `splitOfCoreSet_core`/`_spec`
(coordinate readback: Core block reads u at `coreSet.equivFin.symm j`, Spec reads at `coreSetᶜ.equivFin.symm k`),
and `splitOfPartition_symm_apply`. The opaque-width `packM` reshape is `(flatEquivOf M e).symm` for a slot
bijection `e : Fin N ≃ FlatIdx M`, with `flatEquivOf_symm_coord : ((flatEquivOf M e).symm x) q.1.1 q.1.2 q.2
= x (e.symm q)` (rfl), and `measurePreserving_paramsPack_of_flatIdxEquiv`.

MY PROPOSED ARCHITECTURE: avoid defining shearM's coordinate form entirely. Instead define
`ψ := paramsEquivFlat ∘ packM ∘ shearM` where shearM is the BANKED MP map (whose coordinate action I
characterize ONLY via splitOfCoreSet_core/_spec), and prove the DECODE `ψ(R u) = phiL2 M hrs A0 z H̄_unit
Sbot Λ₀` by:
  (a) computing `(paramsEquivFlat M).symm (ψ(R u)) = packM (shearM (R u))` (symm_apply_apply),
  (b) then `packM (shearM (R u)) = chartL2Params M hrs A0 z H̄_unit Sbot Λ₀` LAYERWISE: `funext layer;
      fin_cases layer` (only Fin 2 layers), and inside each layer relate `packM (shearM (R u)) layer i j`
      to the chart entry via flatEquivOf_symm_coord (gives `shearM (R u) (e.symm ⟨⟨layer,i⟩,j⟩)`), then
      splitOfCoreSet_core/_spec to read shearM coordinatewise, then pivotBlowupOn's defn for R.
</task>

<output_contract>
Three sections, terse:
1. VERDICT on my architecture (a)+(b): is routing the shearM coordinate action through
   splitOfCoreSet_core/_spec (never defining shearM's per-coord `if`-form) the lower-cast path, OR is the
   prior tide right that I must ALSO define an explicit per-coord shearM and bridge it to the MP form?
   Which minimizes dependent-Fin cast pain at opaque width? Be concrete about WHY.
2. THE SINGLE BIGGEST RISK in step (b) — the cast/defeq trap most likely to stall me (name it precisely:
   e.g. the slot bijection e's interaction with coreSet.equivFin ordering, or insertNth/succAbove vs the
   flat-index q, or the deepWidthEquiv row-split alignment), and the cheapest way to de-risk it FIRST
   (a 1-lemma probe I can build before the full decode).
3. SCOPING: given ≤4 cast-attempts per [HIGH] piece and a hard "report the reachable ceiling" discipline,
   what is the minimal SLICE of this that is worth banking first if the full opaque-width decode proves
   too cast-heavy? (e.g. fix c := M 2 = 1 but keep r,s,M0,M1 opaque? carry the decode as a named hypothesis
   and discharge only field A + the box facts generically?)
</output_contract>

<grounding_rules>
You are reviewing an architecture, not a built proof. Flag clearly which of your claims are general
Lean/Mathlib-mechanism facts vs inferences about THIS specific (banked) API that you cannot verify from
the description. Do not invent Mathlib lemma names; if you need a lemma that may not exist, say so.
</grounding_rules>
