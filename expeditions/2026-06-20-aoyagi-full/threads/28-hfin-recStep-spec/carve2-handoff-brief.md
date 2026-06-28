# Handoff brief — `schurRatioResidGen_mid` carve assembly (the SOLE remaining R1-UPPER sorry)

**Branch:** `genm-carve2` (based on `origin/genm-firing` ebb007be; HEAD pushed). **File:**
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean`. Build green, exactly ONE sorry
(`schurRatioResidGen_mid`). Build via `lean/scripts/lb DLNFibre.DLN.RLCT.Validate.RouteMSchurFiring`;
force `#print axioms` (delete olean → rebuild → `lake env lean` a scratch importing the module) before
trusting any axiom-clean claim.

## What this tide BANKED (all green + axiom-clean `[propext, Classical.choice, Quot.sound]`, S2-free)

These are the analytic landing pads + the pivot spine. The carve assembly chains ONTO them.

- **Pivot-normalization spine** (Brick A): `RmatGnorm r N hN p z` (the (0,0)-pivot reorder of the angular
  matrix); `RmatGnorm_pivot` (=1 at (0,0)); `RmatGnorm_offpivot_le` (|·|≤1 off (0,0) on the ratio box);
  `innerSGen_eq_norm` (`innerSGen r c' T p ((piRatioG…).symm(0,z)) = ∫_S frobSq(RmatGnorm·S)^{−c'}`).
- **Slot readback** (#135 foundation): `RmatGnorm_eq_zslot` — for `(i,j)≠(0,0)`, `∃ jj, RmatGnorm … i j = z jj`
  (EXISTENTIAL — the carve needs a CONCRETE `slotG : RatioIdx → Fin N` bijection; see "remaining" below).
- **Generic a.e.-positivity** (#134): `frobSqG_ne_zero_ae (m n q)(hm hn hq) : ∀ᵐ (Δ,S), 0 < frobSq(Δ·S)`
  via the single-(0,0)-entry `entryPolyG` (nonzero, E00 witness) + the new general flatten
  `matToFlatAB`/`combineMNQ`/`genFlatPair` (MP) + read-backs `genFlatPair_idxΔ/_idxS`. Imports Core
  `PolynomialZeroSet`. Plus `frobSqShiftG_ne_zero_ae` (shifted, MP-reduced to unshifted).
- **The JOINT peel brick** (#136) — THE LANDING PAD: `resolvedShiftRG_le (r)(hr:3≤r)(Sh)(B)(hB:|Sh|≤B)(K)(hK)(c')(hc2:2<c') :`
  `∫_{Δ∈matBox(r-1)(r-1)K}∫_{S∈matBox(r-1)4 K}∫_{T∈morseBox 4 K} (∑ᵢTᵢ²+frobSq((Δ−Sh)·S))^{−c'}`
  `≤ ofReal(Cresid 4 c')·coreSchurGenVal r (c'−2)(K+B)`. Δ=free M22, T=Morse spectator, S=S_bot. Peel-after-carve
  (a.e.-positivity over the FREE joint). `coreSchurGenVal_lt_top` gives `<⊤` for `0<c'−2<λ_{r−1}` (abstract IH).
- (Pre-banked by genm-firing, reused) `schur_minorPivot_split` (N2b j=1 two-sided), `schurSplit_lintegral_le`
  (the inverse-power flip), `core_T_peel_le_ae_G`, `schurResidG_translate_le`, the full `piRatioG`/`RmatG` API.

## The remaining assembly (the sole sorry, ~150-200 lines, ORDER from genm-firing's Codex assembly-answer)

CLEAN ORDER (Codex Q4, decorrelated, CONFIRMED): `pivot WLOG → z split (Δ=M22, rest) → pointwise N2b/split
→ top-row shear → Tonelli → a.e. Morse peel over (Δ,S_bot) → resolvedShiftRG_le per fixed rest → bounded
rest volume`. HARDEST (Codex Q5) = the generic ratio-index split/readback proving `Sc = M22 − Sh(rest)`.

1. **The carve carrier (THE HARD PIECE, build standalone FIRST per Codex Q5).** Index ratios by
   `RatioIdxG r := {ij : Fin r × Fin r // ¬(ij = (0,0))}`. `CoreIdxG := Fin(r-1)×Fin(r-1)` via
   `(a,b)↦(a.succ, b.succ)` (using `r = (r-1)+1` from hN/hr); `RestIdxG := Fin(r-1) ⊕ Fin(r-1)` (M21 col-0
   rows 1.., M12 row-0 cols 1..). Build `cellG : CoreIdxG ⊕ RestIdxG ≃ RatioIdxG`
   (inl(a,b)↦⟨(a.succ,b.succ),_⟩, inr inl a↦⟨(a.succ,0),_⟩, inr inr b↦⟨(0,b.succ),_⟩; injective + surjective
   by the `Fin.eq_zero_or_eq_succ` case split). Then a CONCRETE `slotG : RatioIdxG r → Fin N` (promote
   `RmatGnorm_eq_zslot`'s existential to a function — e.g. via `Classical.choose`, or better the explicit
   `(finSuccEquiv' (finCongr hN p))`-decode of `finCongr hN (eG r (σr ij.1, σc ij.2))`, which is `some jj`
   since the index ≠ p; `finSuccEquiv'_symm_some` is the clean decode). Prove `slotG` bijective (it's the
   off-pivot decoder, a bijection `RatioIdxG ≃ Fin N`). Compose `zσG := (cellG.trans slotG-equiv).symm :
   Fin N ≃ CoreIdxG ⊕ RestIdxG`, then `zEG := piCongrLeft ∘ sumPiEquivProdPi` (MP, mirror corank-3 `zE`).
   READBACK (the crux): `RmatGnorm … i j` at a CoreIdxG cell = `(zEG z).1 (the M22 coord)`; at RestIdxG =
   `(zEG z).2` — and `Sc(z) = M22(z) − M21(z)·M12(z)` with `M22 = matOf((zEG z).1)`, `Sh(rest) i j =
   (zEG z).2 (inl i)·(zEG z).2 (inr j)`, `|Sh|≤1`. (Confirmed Mathlib: `MeasurableEquiv.piCongrLeft`,
   `MeasurableEquiv.sumPiEquivProdPi`, `volume_measurePreserving_piCongrLeft`,
   `volume_measurePreserving_sumPiEquivProdPi`. Mirror corank-3 `zσ`/`zE`/`Δof_eq_zE` in
   `RouteM334Ratiofin.lean` 466-690, generic.)

2. **The generic top-row shear** (analog of `RouteM334Ratiofin.step3a`/`step3a_inner`, lines 356-455).
   Split `S = (S0:top row ⊕ S_bot)` via `MeasurableEquiv.piFinSuccAbove (fun _:Fin r => Fin 4→ℝ) ⟨0,_⟩` (MP),
   translate `S0 jj ↦ T jj = S0 jj + ∑_{k:Fin(r-1)} R'(0,k.succ)·S_bot k jj` (so `frobSq((R'·S)_top)=∑_jj T_jj²`
   since R'(0,0)=1), box-enlarge S0 radius T→ `K=max 1 T` or `(r·T)` (|shift|≤(r-1)·T). Atoms: `lintegral_translate`
   (the corank-3 `lintegral_translate_le`), `prod_reorder`, `setLIntegral_prod`, `lintegral_mono_set`.

3. **The per-z N2b dominate.** `schur_minorPivot_split 1` at `R' = RmatGnorm` (cell hyps: |R'|≤1 ✓
   `RmatGnorm_offpivot_le`+pivot=1; 1×1 max-minor = pivot |R'(0,0)|=1 ✓; det M11 = R'(0,0)=1≠0 ✓). Then
   `schurSplit_lintegral_le` (the inverse-power flip, two-sided) → `∫_S frobSq(R'·S)^{−c'} ≤ ofReal(c₀^{−c'})·
   ∫_S (frobSq((R'·S)_top)+frobSq(Sc·S_bot))^{−c'}`. At j=1, `Sc = M22 − M21·M11⁻¹·M12 = M22 − M21·M12`
   (M11⁻¹=[1] since R'(0,0)=1) — prove this `Sc = M22 − Sh` readback (the j=1 simplification of
   `schur_minorPivot_split`'s structural `Sc`).

4. **The assembly** `schurRatioResidGen_mid`: `rw [innerSGen_eq_norm]`; carve z via `zEG` (CoV, MP); Tonelli
   to rest-outer; per rest fix `Sh`, chain (3)+(2) to the `resolvedShiftRG_le` integrand; apply
   `resolvedShiftRG_le` (uniform in rest) + `coreSchurGenVal_lt_top`; outer rest-box `[−1,1]^{2(r-1)}` finite
   volume × the uniform finite bound. Mirror corank-3 `ginnerZ_lt_top` (`RouteM334Ratiofin.lean` 848-896) +
   `schurInner3_ratiofin_mid`, generic.

## Closure
Closing `schurRatioResidGen_mid` → `schurRatioResidGen` (subcritical fold, ALREADY wired) →
`schur_matBoxG_chart_lt_top` → `schurCoreGen_firing` → `schurRecStep_four` all sorry-free →
`RouteMSchurGeneral.schurGen_lt_top_modulo_recStep` CLOSES R1-UPPER. Then AUDIT: force `#print axioms`
clean-three; statement-card → `reviewed` (reviewer fidelity check).

## Highest-risk sub-step (per genm-firing Codex Q5)
The generic ratio-index split/readback proving `Sc = M22 − Sh(rest)` at opaque `Fin(r-1)` widths (step 1).
Mitigation: build `zEG` + ALL readback lemmas (M22/M21/M12/Sh, |Sh|≤1) standalone BEFORE touching integrals;
use the opaque-width `have`+`exact` recipe (`lean/CLAUDE.md`); `⟨0, by omega⟩` / `Fin.succ` for the cells.
