**1. Verdict**

S2. `repClosure` is typed by the coordinate space `RepCoord d → k`, so a chain of inclusions can compose only after every per-step degeneration has been transported to the fixed ambient `d`.

**2. Per-Step Statement**

I would state the chain-facing lemma with the fixed dimension vector explicit, and hide the coordinate extraction from `BoxMoveStep` behind a lower helper.

```lean
def multOfRank {N : ℕ} (r : ℤ → ℤ → ℤ) (hr : Supported (N : ℤ) r) :
    SuppArray (N : ℤ) ℤ :=
  ⟨diff r, supported_diff hr⟩

theorem boxMoveStep_realizer_repClosure_subset
    [Infinite k]
    {d : Fin (N + 1) → ℕ} {r r' : ℤ → ℤ → ℤ}
    (hr  : Supported (N : ℤ) r)
    (hr' : Supported (N : ℤ) r')
    (hm  : CMPlus (k := k) d (multOfRank r hr))
    (hm' : CMPlus (k := k) d (multOfRank r' hr'))
    (hstep : BoxMoveStep r r') :
    repClosure (orbitSet (realizer (k := k) (multOfRank r' hr') hm'))
      ⊆
    repClosure (orbitSet (realizer (k := k) (multOfRank r hr) hm))
```

The main implementation target should be the Fin-indexed nonsplit/split helper, e.g.

```lean
theorem nonsplitBox_realizer_repClosure_subset
    [Infinite k]
    {d : Fin (N + 1) → ℕ} {r r' : ℤ → ℤ → ℤ}
    (hr  : Supported (N : ℤ) r)
    (hr' : Supported (N : ℤ) r')
    (hm  : CMPlus (k := k) d (multOfRank r hr))
    (hm' : CMPlus (k := k) d (multOfRank r' hr'))
    {a c e : Fin (N + 1)} {b : Fin N}
    (hac : a < c) (hcb : c ≤ b.castSucc) (hbe : b.succ ≤ e)
    (hae : 1 ≤ (multOfRank r hr).1 (a : ℤ) (e : ℤ))
    (hcbm : 1 ≤ (multOfRank r hr).1 (c : ℤ) (b.castSucc : ℤ))
    (hbox :
      (multOfRank r' hr').1 =
        fun x y =>
          (multOfRank r hr).1 x y
            - singleDelta a e x y
            - singleDelta c b.castSucc x y
            + singleDelta a b.castSucc x y
            + singleDelta c e x y) :
    repClosure (orbitSet (realizer (k := k) (multOfRank r' hr') hm'))
      ⊆
    repClosure (orbitSet (realizer (k := k) (multOfRank r hr) hm))
```

Then `boxMoveStep_realizer_repClosure_subset` just destructs `hstep`, converts the integer box coordinates to `Fin`, proves/uses the split-vs-nonsplit branch, and applies the corresponding helper.

**3. Single Point To Whole Orbit**

Rank-pattern bridge alone is not enough. From one point
`canonicalCoord d D ∈ repClosure (orbitSet U)`, you cannot get `orbitSet D ⊆ repClosure (orbitSet U)` without stability of the target closure under base change.

Use this targeted lemma:

```lean
lemma orbitSet_subset_repClosure_orbitSet_of_canonical_mem
    {d : Fin (N + 1) → ℕ} {D U : Tuple (k := k) d}
    (hD : canonicalCoord d D ∈ repClosure (orbitSet U)) :
    orbitSet D ⊆ repClosure (orbitSet U)
```

Proof idea: if `x ∈ orbitSet D`, then `x = canonicalCoord d (P • D)`. Use:

```lean
lemma repClosure_orbitSet_smul_mem
    {d : Fin (N + 1) → ℕ} (U X : Tuple (k := k) d)
    (P : BaseChangeGroup (k := k) d)
    (hX : canonicalCoord d X ∈ repClosure (orbitSet U)) :
    canonicalCoord d (P • X) ∈ repClosure (orbitSet U)
```

This needs unlisted infrastructure: `orbitSet U` is `G_d`-stable, and precomposition by fixed base change sends polynomials to polynomials. You can prove this cheaply in the vanishing-ideal style: for `f ∈ vanishingIdeal (orbitSet U)`, precompose `f` with `A ↦ P • A`; the precomposed polynomial still vanishes on `orbitSet U`, so it vanishes at `D`.

**4. Residual And Dimension Computation**

Sharpest route: do not build a residual realizer. The residual only manufactures `rest`; it does not need its own ambient tuple. Add the lighter lemma:

```lean
lemma multiplicityArray_listOfArray_of_isKostant
    (m : SuppArray (N : ℤ) ℤ) (hm : IsKostantArray m) :
    multiplicityArray (listOfArray m) = m.1
```

This is a refactor of `multiplicityArray_listOfArray`; its proof already uses only `hm.1`.

Also add:

```lean
lemma foldDim_eq_cumul_multiplicityArray_diag
    (L : List (Fin (N + 1) × Fin (N + 1))) (t : Fin (N + 1)) :
    (foldDim L t : ℤ) =
      cumul (N : ℤ) (multiplicityArray L) (t : ℤ) (t : ℤ)
```

Then for nonsplit, define `m := multOfRank r hr` and

```lean
mRest.1 = fun x y =>
  m.1 x y - singleDelta a e x y - singleDelta c b.castSucc x y
rest := listOfArray mRest
```

The fixed-dimension proof is the pointwise chain:

```lean
calc
  (dg t : ℤ)
      = (intervalDim a e t : ℤ)
        + (intervalDim c b.castSucc t : ℤ)
        + (foldDim rest t : ℤ) := by simp [dg, add_assoc]
  _ = cumul (N : ℤ) (singleDelta a e) (t : ℤ) (t : ℤ)
        + cumul (N : ℤ) (singleDelta c b.castSucc) (t : ℤ) (t : ℤ)
        + cumul (N : ℤ) mRest.1 (t : ℤ) (t : ℤ) := by
          rw [intervalDim_eq_cumul_singleDelta_diag,
              intervalDim_eq_cumul_singleDelta_diag,
              foldDim_eq_cumul_multiplicityArray_diag,
              multiplicityArray_listOfArray_of_isKostant]
  _ = cumul (N : ℤ)
        (fun x y =>
          singleDelta a e x y
            + singleDelta c b.castSucc x y
            + mRest.1 x y)
        (t : ℤ) (t : ℤ) := by
          rw [cumul_add, cumul_add]; ring
  _ = cumul (N : ℤ) m.1 (t : ℤ) (t : ℤ) := by
          rw [hres_sum]
  _ = (d t : ℤ) := (hm.2 t).symm
```

Then `exact funext fun t => by exact_mod_cast hdiag t`.

Needed but unlisted sublemmas here: `mRest` is supported, `mRest` is `IsKostantArray`, `intervalDim_eq_cumul_singleDelta_diag`, and the box-drop `diff` formula if `BoxMoveStep` only stores `r' = boxDrop r ...`.

**5. Cast Landmines**

`(hgd : dg = d) ▸ Xgeom` is the right transport. Use tiny helper lemmas rather than rewriting through raw `canonicalCoord` goals:

```lean
lemma mem_repClosure_orbitSet_transport
    {d₀ d : Fin (N + 1) → ℕ} (h : d₀ = d)
    {D U : Tuple (k := k) d₀}
    (hm : canonicalCoord d₀ D ∈ repClosure (orbitSet U)) :
    canonicalCoord d (h ▸ D) ∈ repClosure (orbitSet (h ▸ U)) := by
  subst h
  simpa using hm
```

For ranks, peel casts in order:

```lean
rw [rankPattern_transport hgd Xgeom]
rw [rankPattern_transport hfold (intervalDirectSum L)]
rw [rankPattern_intervalDirectSum_eq_cumul]
```

Do not try to make the double `▸` definitionally disappear in the main proof. Prove rank lemmas first over `dg`, then transport once to `d`, then apply `repClosure_orbitSet_eq_of_rankPattern_eq` against the fixed-`d` realizers.