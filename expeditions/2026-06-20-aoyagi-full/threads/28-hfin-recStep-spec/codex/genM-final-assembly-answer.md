Short answer: use the corank-3 `zσ`/`zE` pattern, but read `Sc` through the explicit Schur-complement formula. Also correct the radius: after `stepShearG`, the Morse radius is `r*T`, so `K = max 1 ((r : ℝ) * T)`, not `max 1 T`.

**Q1**

Yes, but first split out a generic `slotMatG_spec`; do not prove bijectivity directly from `RmatGnorm_eq_slot`.

Use:

```lean
slotMatG_spec :
  (finCongr hN p).succAbove (slotMatG r N hN hr p a b)
    =
  finCongr hN (eG r (σr a, σc b))
```

Then prove `slotMatG_injOn` from `slotMatG_spec`, `(finCongr hN).injective`, `(eG r).injective`, and swap injectivity. Then:

```lean
noncomputable def zσG ... :
    Fin N ≃ ((Fin (r-1) × Fin (r-1)) ⊕ (Fin (r-1) ⊕ Fin (r-1))) :=
  (Equiv.ofBijective
    (fun s =>
      slotMatG r N hN hr p (cellOfG (r-1) s).1 (cellOfG (r-1) s).2)
    (slotFunG_bijective ...)).symm
```

Card proof: `simp; ring` alone is fragile because of Nat subtraction. Use:

```lean
have hcard :
    (r - 1) * (r - 1) + ((r - 1) + (r - 1)) = N := by
  have hs : (r - 1) + 1 = r := by omega
  have hsq :
      ((r - 1) + 1) * ((r - 1) + 1)
        = (r - 1) * (r - 1) + ((r - 1) + (r - 1)) + 1 := by
    ring
  rw [hs, hN] at hsq
  omega
```

Then `zEG` is exactly:

```lean
(MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) zσG).trans
  (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))
```

Names CONFIRMED: `Equiv.ofBijective`, `Fintype.bijective_iff_injective_and_card`, `MeasurableEquiv.piCongrLeft`, `MeasurableEquiv.sumPiEquivProdPi`, `volume_measurePreserving_piCongrLeft`, `volume_measurePreserving_sumPiEquivProdPi`.

**Q2**

Use the explicit formula. Do not make the existential `Sc` the object of the readback.

Apply N2b, obtain:

```lean
obtain ⟨Sc, hSc_def, _hdet, hlo, _hup⟩ := hN2b RM S hbd hpivot hne
```

Then immediately prove/transport:

```lean
have hSc :
    Sc = ScOfG r N hN hr p z := by
  rw [hSc_def]
  ext a b
  -- j = 1, M11 = 1, M11⁻¹ = 1
  simp [ScOfG, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_one,
        RmatGnorm_pivot]
```

Some `simp` here may need local rewrites for `⟨1 + a, _⟩ = a.succ`; use `ext; simp [Fin.succ]` or a small helper. `Matrix.det_fin_one` and `Fin.sum_univ_one` are CONFIRMED in this repo. `Matrix.inv_one` is INFERRED; avoid depending on it by rewriting the `Fin 1` inverse block after proving the pivot block is `1`.

Then the carve readback should be a separate entrywise lemma:

```lean
ScOfG r N hN hr p ((zEG ...).symm (M, v))
  =
(fun a b => M (a,b) - bgShiftG (r-1) v a b)
```

Proof pattern:

```lean
ext a b
simp [ScOfG, bgShiftG]
rw [RmatGnorm_eq_slot, RmatGnorm_eq_slot, RmatGnorm_eq_slot]
rw [← zσG_symm_apply, zEG_symm_inl]
rw [← zσG_symm_apply, zEG_symm_inr]
rw [← zσG_symm_apply, zEG_symm_inr]
```

READBACK-VIA: explicit-formula.

**Q3**

High-level chain is right, but implement as carve-first or explicit-`ScOfG`-first:

```lean
innerSGen_eq_norm
→ zEG CoV / readback
→ N2b j=1 with Sc rewritten to Δ - bgShiftG v
→ ofReal_rpow_le_const_mul
→ stepShearG with b a = R 0 a.succ
→ enlarge boxes to common K
→ resolvedShiftRG_le with B = 1
→ integrate v over bounded box
```

The trickiest gluing point is the radius. `stepShearG (m := r-1)` gives:

```lean
morseBox 4 (((r-1)+1 : ℕ) * T) = morseBox 4 ((r : ℝ) * T)
```

So use:

```lean
let K : ℝ := max 1 ((r : ℝ) * T)
```

Then prove monotone inclusions for `Δ`, `S_bot`, and `T'` before calling `resolvedShiftRG_le`. `resolvedShiftRG_le` does not perform this incoming box enlargement; its internal enlargement is only the shifted residual `K → K+B`.

**Q4**

No hidden mathematical gap if the radius is corrected. The N2b `Sc` opacity is handled by `hSc_def`; the top-row match is bookkeeping with `fin_sum_block_split`/`Fin.sum_univ_one`; the only sharp trap is using `K = max 1 T`.

Expect more like 150-250 Lean lines if you include clean `zσG/zEG` helper lemmas, not 80-120.

ASSEMBLY: PURE-PLUMBING  
READBACK-VIA: explicit-formula