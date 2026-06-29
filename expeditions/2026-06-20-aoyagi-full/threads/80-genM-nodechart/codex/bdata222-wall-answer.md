**Winning Route: R2**

Choose the two leaf slots from the finite complement, not from `χ.symm` of leaf tags. This is the clean resolution.

Let

```lean
p0 := structPivot M222 hN
readerSet := {Kslot, Xslot, Nslot, W0slot, W1slot}
forbidden := insert p0 readerSet
free := (Finset.univ : Finset (Fin (routeMAmbient M222))) \ forbidden
```

Prove `2 ≤ free.card`, then choose two slots `lf0 lf1 ∈ free`, `lf0 ≠ lf1`. Now all needed inequalities are membership consequences:

```lean
lf0 ∈ free  ⟹  lf0 ≠ p0 ∧ lf0 ∉ readerSet
lf1 ∈ free  ⟹  lf1 ≠ p0 ∧ lf1 ∉ readerSet
```

No comparison between `χ.symm leafTag` and `⟨0,_⟩` is needed.

Yes, `rfin` and `B` can depend on the chosen `lf0 lf1`: define them after the `obtain`, or better package the choice in a `noncomputable def` via `Classical.choice`, then define `rfin222`, `active222`, and `B222` from that package. This is clean Lean.

Recommended shape:

```lean
structure LeafPair222 where
  lf0 lf1 : Fin (routeMAmbient M222)
  h0 : lf0 ∈ free222
  h1 : lf1 ∈ free222
  hne : lf0 ≠ lf1

noncomputable def leafPair222 : LeafPair222 :=
  Classical.choice exists_leafPair222
```

Then:

```lean
active222 : Finset (Fin (routeMAmbient M222)) :=
  {p0, leafPair222.lf0, leafPair222.lf1}
```

or `insert p0 {lf0, lf1}`.

**Lemma Sequence**

1. Reader distinctness:
   use `(χ.symm).injective h` plus `decide` on distinct `ChartIdx` tags. This proves:

```lean
readerSet.card = 5
```

2. Complement cardinal:
   avoid proving `p0 ∉ readerSet`.

```lean
have hforbidden_le : forbidden.card ≤ 6 := by
  by_cases hp : p0 ∈ readerSet
  · simp [forbidden, hp, readerSet_card]
  · rw [forbidden, Finset.card_insert_of_notMem hp, readerSet_card]
```

Then use:

```lean
Finset.card_sdiff
Finset.card_univ
Fintype.card_fin
routeMAmbient_M222
omega
```

to get `2 ≤ free.card`.

3. Extract two slots:
   use `Finset.exists_subset_card_eq` if available in your imports, or choose a `LeafPair222` by a small local existence lemma from `2 ≤ free.card`.

4. Active cardinal:

```lean
have hp_not_mem : p0 ∉ ({lf0, lf1} : Finset _) := ...
rw [Finset.card_insert_of_notMem hp_not_mem]
simp [lf0_ne_lf1, minAdm_M222]
```

5. PBO facts:

```lean
pivotBlowupOn active p0 x p0 = x p0
pivotBlowupOn active p0 x lf0 = x p0 * x lf0
pivotBlowupOn active p0 x lf1 = x p0 * x lf1
```

by `simp [pivotBlowupOn, lf0_ne_p0, lf1_ne_p0, lf0_mem_active, lf1_mem_active]`.

For reader slots `q`:

```lean
by_cases hq : q = p0
· simp [pivotBlowupOn, hq]
· have q_not_active : q ∉ active := ... -- from q ∈ readerSet and lf0/lf1 ∈ free
  simp [pivotBlowupOn, hq, q_not_active]
```

**Evaluation Of Alternatives**

`R1`: does not dodge the wall. If `S` is the two `χ.symm` leaf-tag slots, proving `structPivot ∉ S` is exactly the same opaque comparison. Cardinality alone cannot rule out `χ ⟨0,_⟩` being a leaf tag.

`R3`: possible only by banking a new lemma or replacing `chartIdxEquiv` with a computable model. There is no useful semantic Mathlib characterization of `Fintype.equivFin` that forces a specific point value. Treat it as opaque.

`R4`: not faithful for this `BData` route. The two non-pivot scaled coordinates must be the free leaf residual coordinates. If `B` multiplies leaf coordinates by `u` instead, the `u²` factor moves into `DB`; if reader slots are scaled, recovering them requires division by `u` and fails at `u = 0`.

**Biggest Risk**

The slot wall is solved by R2. The remaining risk is the custom Fix-B map: do not instantiate `B` as `phiGen 1 (genBlkFlatLiveR1 ...)`; the repo notes already identify that as false for the fixed pivot. `B` must be the additive-pivot boundary map, with `rfin` reading the complement-chosen `lf0 lf1`.