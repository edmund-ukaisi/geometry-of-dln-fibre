## 1. MOTIVE

```lean
P s :=
  ∀ (R : ℝ) (acc : Params M → Params M),
    closedBall 0 R ⊆
      leafImages (tGeo acc (buildTree M (conOracle M) s))
```

Then:

```lean
refine (conRel_wf M).induction s ?_
intro s ih R acc
```

[INFERENCE] This is preferable to threading `R` through the well-founded state: `ih child hdesc` remains polymorphic and can be specialized at `f (max R 1)` and the child accumulator. Introducing `R` before induction would freeze it at the parent radius.

[FACT] With the present fixed unit `srcBox`, this exact universal statement is false at a terminal state for `R > 1`. Either radius-parameterize the leaf domains, or use a bounded motive `R ≤ budget s → …`. Keep the logical radius inside the motive; thread radius only through the domain/budget construction.

## 2. DESCENT SKELETON

- Put `r := max R 1`. For a closed-ball goal, split off `R < 0`; otherwise retain `0 ≤ R`.
- For every pivot child `p`, define its own domain
  `D p := leafImages (tGeo acc_p (buildTree … child_p))`.
- Instantiate the WF hypothesis exactly at the inflated radius:
  `ih child_p hdesc_p (f r) acc_p`, obtaining `closedBall 0 (f r) ⊆ D p`.
- Use the local shear estimate, plus global `C*` domination if needed:
  `closedBall 0 r ⊆ c.shear '' closedBall 0 (f r)`.
  Image monotonicity then gives `closedBall 0 r ⊆ c.shear '' D p`.
- Apply a leaf-indexed version of the node cover with `dom p := D p`, then rewrite the branch leaf-image union and select the corresponding child edge.

[FACT] `bornSiblings_union_covers` currently has one common `dom`; it cannot directly consume the varying `D p`. Also, it concludes `ball 0 R`, not `closedBall 0 R`. The clean fix is a family-domain closed-ball analogue, based on the already banked closed-ball block atom. Enlarging to `ball 0 (R+ε)` changes the inflation recurrence.

## 3. BOOKKEEPING LEMMAS

1. Image monotonicity:

   ```lean
   A ⊆ B → g '' A ⊆ g '' B
   ```

   [INFERENCE: likely Mathlib spelling `Set.image_mono`.]

2. Inflation control for `f_C r := r + C * r^2`:

   ```lean
   0 ≤ r → C ≤ Cstar → f_C r ≤ f_Cstar r
   ```

   Optionally also prove monotonicity in `r` on `0 ≤ r` when `0 ≤ Cstar`.

3. Shear–child composition:

   ```lean
   closedBall 0 r ⊆ σ '' closedBall 0 q →
   closedBall 0 q ⊆ D →
   closedBall 0 r ⊆ σ '' D
   ```

## 4. FRICTION

- **Motive freezes `R`.** Guard: define `P` explicitly and introduce `R acc` only after WF induction.
- **One `dom` versus pivot-dependent children; open versus closed ball.** Guard: first state the family-domain closed node clause; never replace `D p` by their union.
- **`max` and global inflation arithmetic.** Guard: set `r := max R 1`, record `1 ≤ r`, and use one explicit local-`C` ≤ global-`C*` lemma rather than asking automation to normalize it repeatedly.