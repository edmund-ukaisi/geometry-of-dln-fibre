Notation: `[TC]` = scratch-elaborated on v4.29. `[UNVERIFIED/local✓]` = outside your confirmed list, but locally `#check`ed.

### 1. Integrable-level transport

Yes—cleaner than `∫⁻`. Crucially, use `hmp.symm e`, matching the supplied `e.symm`-preimage lemma.

```lean
let H := fun z => Fsub z.1 * Gsub z.2
have hprod : IntegrableOn H (boxZ ×ˢ boxC) ((Measure.pi fun _ => volume).prod
    (Measure.pi fun _ => volume)) := by
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact hF.mul_prod hG
have hmodel : IntegrableOn (H ∘ e) box volume := by
  refine ((hmp.symm e).integrableOn_comp_preimage e.symm.measurableEmbedding).1 ?_
  rw [hpre]
  have hc : (H ∘ e) ∘ e.symm = H := by funext z; exact congrArg H (e.apply_symm_apply z)
  rw [hc]; exact hprod
exact hmodel.congr hfactor_ae.symm.restrict
```

`[TC]`. If `hfactor_ae` already uses `volume.restrict box`, omit `.restrict`. Do not transport the a.e. equality through `e`.

### 2. Missing question

No Question 2 was supplied.

### 3. Sum-of-squares block

Reindexing to `Fin Z.card`, then using `ofLp`, is cheaper. A Fintype-general ball theorem hides those same transports.

```lean
let n := Z.card
have hn : 0 < n := Finset.card_pos.mpr hZne -- [UNVERIFIED/local✓]
have hrad := RLCT.integrableOn_ball_norm_rpow_iff
    (m := n - 1) hρ (by linarith : -2 * cc < 0)
rw [Nat.sub_add_cancel hn] at hrad                 -- [UNVERIFIED/local✓]
have hrad' := hrad.2 (by dsimp [n]; linarith [hsos])
refine ((PiLp.volume_preserving_ofLp (Fin n)).integrableOn_comp_preimage
  (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding).1 ?_
rw [hcomp_ofLp]
exact hrad'.mono_set hbox_preimage_subset_ball
```

For `cc = 0`, use `prodRpow_boxSymm_lt_top hR (fun _ ↦ 0) (by simp)` and simplify both functions to `1`.

### 4. `piCongrLeft` reindexing

Avoid integral equality unless needed. For integrability use `integrableOn_comp_preimage`; for equality, use:

```lean
let φ : Fin n ≃ I := ...
let eI := MeasurableEquiv.piCongrLeft (fun _ : I ↦ ℝ) φ
have hcomp : Gsub ∘ eI = GFin := by
  funext v; simp only [Function.comp_apply]
  rw [← φ.prod_comp (fun i : I ↦ |eI v i| ^ exponent i)] -- [UNVERIFIED/local✓]
  simp only [eI, MeasurableEquiv.piCongrLeft_apply_apply]
have ht := hmpI.setLIntegral_comp_preimage_emb eI.measurableEmbedding
  (fun w ↦ ENNReal.ofReal (Gsub w)) boxI
rw [hpre] at ht
simpa only [congrFun hcomp] using ht.symm
```

For `hpre`, `[UNVERIFIED/local✓] Equiv.piCongrLeft_preimage_univ_pi` is one line. Confirmed-only fallback: `ext v`; unfold `Set.mem_pi`; use `piCongrLeft_apply_apply` in both directions and `φ.surjective`.

### 5. Landmines

- Put `classical` first; this resolves both membership predicates.
- Sigma-finite/S-finite instances for finite Pi spaces over `ℝ` are automatic.
- Pi-space `Measure.pi (fun _ ↦ volume)` reduces to `volume` here; keep the product measure explicit until transport.
- Split `cc = 0` before invoking the negative-exponent ball theorem.
- `hZne` is essential for rewriting `Z.card = (Z.card - 1) + 1`.
- The complement may be empty; `prodRpow_boxSymm_lt_top` handles `Fin 0`.
- `prodRpow_boxSymm_lt_top` must actually be un-private before use.
- `hunit0` is unused by this upper-domination proof; that is harmless.
- Extra reindex APIs needed: `[UNVERIFIED/local✓] Finset.equivFin`, `Fintype.equivFin`, `Equiv.prod_comp`, `Equiv.sum_comp`.
- Full target proof remains `[LIKELY—verify]`; the core transport chains above are `[TC]`.

## RECOMMENDED SKELETON

1. `classical`; define `ev`, `mono`, `sos`, `g`, `Fsub`, `Gsub`, and `e`.
2. Obtain `hev : ∀ d, -1 < ev d` using `monomial_forall_neg_one_lt_iff_lt_threshold` `[UNVERIFIED/local✓]`.
3. Prove `ev j = 0` on `Z` from `hZa`, `hZjac`.
4. Copy the mirror’s hyperplane-null argument; obtain `mono =ᵐ[volume] fun u ↦ ∏ d, |u d| ^ ev d`.
5. Derive `hfactor_ae : g =ᵐ[volume] H ∘ e` using `Fintype.prod_subtype_mul_prod_subtype` and `Finset.sum_subtype` `[UNVERIFIED/local✓]`.
6. Define `R`, `box`, `boxZ`, `boxC`; prove `hR` and `box ∈ 𝓝 p` as in the mirror.
7. Reindex the complement with `φC`; use `prodRpow_boxSymm_lt_top` plus `hasFiniteIntegral_iff_ofReal` to get `hG`.
8. Split `cc = 0 ∨ 0 < cc`; obtain the Fin sum-block integrability from the zero-product box or `integrableOn_ball_norm_rpow_iff`.
9. Transport that result through `PiLp.volume_preserving_ofLp`, then through the `Z`-block `piCongrLeft`, obtaining `hF`.
10. Prove `hpre : e.symm ⁻¹' box = boxZ ×ˢ boxC` using `Equiv.preimage_piEquivPiSubtypeProd_symm_pi`.
11. Form `hprod` by `rw [IntegrableOn, ← Measure.prod_restrict]; exact hF.mul_prod hG`.
12. Transport with `((hmp.symm e).integrableOn_comp_preimage e.symm.measurableEmbedding).1`.
13. Set `hg_box := hmodel.congr hfactor_ae.symm.restrict`.
14. Choose the mirror’s ball `B ⊆ box ∩ {hW} ∩ {|unit| < Mub}`; set `hg_intB := hg_box.mono_set ...`.
15. Finish with `(hg_intB.const_mul Mub).mono' hmeas hbound`, copying the mirror’s measurability and pointwise domination spine.