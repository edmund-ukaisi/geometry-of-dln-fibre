Recommend **Shape C**: split off the binding cell as green data, and leave only the complementary §4 chart cover as the named obligation. Deciding reason: `BranchData` alone has no way to certify “this came from the §4 Schur chart construction”, so a gap returning all of `R1Section4Data` is still too coarse; the distinguished achiever must be constructed outside the gap.

```lean
structure R1BindingCell (M₀ M : Fin (L+1) → ℕ) where
  split   : ChainDimSplit M
  codim   : ℕ
  witness : PivotWitness M₀ codim
  hbind   : codim = minAdm M₀   -- or your transported root-value statement
```

```lean
structure R1Section4ComplementData (M₀ M : Fin (L+1) → ℕ) where
  cells        : Type
  instFintype  : Fintype cells
  instNonempty : Nonempty cells
  split        : cells → ChainDimSplit M
  codim        : cells → ℕ
  witness      : ∀ c, PivotWitness M₀ (codim c)
  hnode        : ∀ c, Section4SchurNode M₀ M (split c) (codim c)
```

Here `Section4SchurNode` should be your existing analytic/chart predicate, not `True`. [INFERENCE]

Producer:

```lean
noncomputable def branchDataOfR1Section4
    (b : R1BindingCell M₀ M)
    (d : R1Section4ComplementData M₀ M) :
    BranchData M₀ M :=
{ cells := PUnit ⊕ d.cells
  instFintype := inferInstance
  instNonempty := ⟨Sum.inl PUnit.unit⟩
  split := fun x => Sum.elim (fun _ => b.split) d.split x
  codim := fun x => Sum.elim (fun _ => b.codim) d.codim x
  witness := fun x => Sum.elim (fun _ => b.witness) d.witness x }
```

The `T*`-profile `ChainDimSplit` should be constructed now, inside `R1BindingCell` construction, from `achieverPivotWitness` plus the width-drop identities and non-origin proof. It should not be part of the §4 gap. [INFERENCE]

Single named obligation:

```lean
opaque r1Section4ComplementData
    (M₀ M : Fin (L+1) → ℕ)
    (hM : ¬ isLeafNode M) :
    R1Section4ComplementData M₀ M
```

Non-vacuity guard: prove

```lean
lemma r1Branch_has_at_least_two_cells :
  2 ≤ Fintype.card (branchDataOfR1Section4 b d).cells
```

using `d.instNonempty`. Also useful: `b.split ≠ schurState M hlo`, but that alone does not rule out the single-cell trap.

Possible false assumption: `BranchData.witness` is over `M₀`, while `achieverPivotWitness` is for its input width vector. You need the green transport you mentioned to align these; otherwise the binding-cell type above must use the transported codim statement instead of `codim = minAdm M₀`.