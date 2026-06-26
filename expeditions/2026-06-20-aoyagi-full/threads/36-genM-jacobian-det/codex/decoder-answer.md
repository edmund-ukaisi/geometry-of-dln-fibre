
```lean
def readRole (x : Fin N → ℝ) (ρ : ChartIdxRole M t) : ℝ :=
  if ρ = fixedSlot then 1 else x (chartIdxEquiv.symm ρ)

def radial (x : Fin N → ℝ) : ℝ :=
  x (chartIdxEquiv.symm fixedSlot)
```

Then build `GenBlk` structurally:

```text
GenBlk index 0:
  Bmat 0 = I
  Rmat 0 = 0
  Nblk 0, Wblk 0 zero-width/irrelevant

For s = k+1:
  K_s := lduAssemble (read LDU slots)
  N_s := read N slots
  X_s := read X slots
  E_s := read E slots, with fixedSlot read as 1

  Bmat s = [ K_s
             X_s * K_s ]

  Nblk s = N_s

  Rmat s = block matrix with only bottom-right block E_s
           -- so C_s = B_s * Q(N_s) + u • R_s
           --      = [[K, K N], [XK, XKN + uE]]

  Wblk s = read lift W_s        -- for s < L
  Rfin L = leaf E block          -- usually whole residual when t_L = 0
```

This makes the decoder disjoint where it should be disjoint: every genuine free nonradial coordinate is read from a unique role slot; the radial coordinate is the fixed residual slot repurposed as `u`.

If the current theorem hardcodes `u = x ⟨0, hN⟩`, either change it to a named `pRad`, or replace the opaque `Fintype.equivFin`-based `chartIdxEquiv` with a custom equivalence putting `fixedSlot` at coordinate `0`. I would prefer `pRad`; forcing `0` through an opaque equivalence will create avoidable proof debt.

**Item-3 Target**
Keep `φ_flat` as the rate-side chart:

```lean
φ_flat x = paramsEquivFlat M (chartParamsGen (u x) M t (genBlkFlat x) hle)
```

but define the factor list from the same role accessors and the same local block constructors. Then prove item-3 through a Params-level statement, not by chasing final flat coordinates first:

```lean
theorem composeFold_eq_phiFlat :
  composeFold fs = φ_flat
```

Best proof shape:

```lean
theorem composeFold_unflat_eq_chartParamsFlat :
  (fun x => (paramsEquivFlat M).symm (composeFold fs x))
    = chartParamsFlat M t ... := by
  funext x
  ext s i j
  -- unfold only the stage accessor lemmas
```

Then get `composeFold_eq_phiFlat` by applying `paramsEquivFlat M`.

This avoids making the final `paramsEquivFlat` ordering the main battlefield. The heavy lemmas should be local stage laws:

```lean
genBlkFlat_C_s_eq_schurFrame
genBlkFlat_A_s_eq_chainA
composeFold_after_radial_reads
composeFold_after_ldu_reads
composeFold_after_schur_has_C
composeFold_after_chain_has_layers
```

**Factor Construction**
Yes: make item-3 “by construction” as much as possible. Choose each conjugating CLE `E_s` to be the actual role split used by the decoder and by `paramsEquivFlat`/layer assembly. Do not pick arbitrary block extractions and later prove they coincide with a separately designed decoder.

The factor order should reflect dependencies:

```text
radial first          -- rightmost in composeFold
LDU factors           -- LDU slots -> K_s
Schur factors         -- K,N,X,E -> C_s
chain factors         -- C_{s+1}, W_s -> A_s
```

With `composeFold`’s `foldr`, that means the radial factor is last in the list if you write outer-to-inner factors.

**Bottom Line**
The clean decoder is **ChartIdx-role-based with one fixed residual slot**, not raw-`GenBlk`-field-based. The raw `GenBlk` role sizes do not and should not sum to `N`. The chart is square because the true coordinate space is:

```text
radial ⊕ nonfixed Schur/lift roles
```

and that is equivalent to `ChartIdx`, hence to `Fin (flatDim M)`.
