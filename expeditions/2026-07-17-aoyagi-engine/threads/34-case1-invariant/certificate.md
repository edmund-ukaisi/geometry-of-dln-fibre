# Thread 34 — coupled Case-1 invariant certificate (pnp-case1)

> Controller-banked 2026-07-21 from the seat's final message (the seat wrote no certificate file
> per its brief; batteries are self-documenting). Controller independently re-ran
> `case1_witness_334.py` (EXIT 0) at banking. Decorrelated codex consult in `codex/`
> (converged on the identical split by its own route, including an independent impossibility
> proof that (D)+(B) cannot co-exist at J=0).

## VERDICT: HOLDS-WITH-CONDITIONS — PrincipalInv SPLITS

The coupled Case-1 preservation of `PrincipalInv` (the thread-32 leaf-4 sketch) splits into two
halves with **opposite truth-values**:

- **(D) Divisibility — holds ∀-general** (all L, all widths, corank ≥ 2), with an explicit
  witness law:
  - `b'₁ = u^δ · φ*b₁` where `δ = [J=0]` (the first pivot-clear multiplies the tracked divisor
    by the unit-power; later clears do not);
  - `q'_ij = (φ*q_ij) / u^δ` — the division is **exact** (polynomial), so the new quotients are
    continuous with no localization;
  - the right column-op `P` and the Schur shear compose into the chart map `g`; the left det-0
    row-op `Q₁` stays as the weighted projection cofactor
    `Q̂ = diag(b')·Q₁⁻¹·diag(b')⁻¹` — continuous, unipotent, `= I` at 0, off-diagonal entries
    may vanish — which regenerates the row quotients.
- **(B) Bézout / principality — obstructed per-step, exactly located**: FALSE for all `S < L`
  (the pending deep layer `∏_{s>S} C` vanishes at the deepest point ⟹ every quotient vanishes
  at 0 ⟹ a Bézout identity forces 0 = 1 by continuity) and for all `J = 0` (no cleared pivot);
  first TRUE at `S = L ∧ J ≥ 1` (a bare diagonal `b₁` entry) — i.e. **terminally**. A Case-1
  step at `S < L` cannot re-establish it even after clearing a pivot: the pivot row is
  `b₁·(deep-layer row)`, still not bare.

**Consequence for the ladder.** Leaf 4 as sketched (`case1_preserves_principalInv`, both
identities per step) preserves a property false at the root — vacuous induction. The
decomposition splits:

- Leaves 3/4 → `case2_preserves_stepInv` / `case1_preserves_stepInv`, where `StepInv` is
  region-quantified (open `nbhd ∋ 0`, `ContinuousOn` cofactors `U,V` with `U 0 = V 0 = I`,
  product identity as `Set.EqOn`), carries the chain `∀ i, b_{k₀} ∣ b_i`, and asserts
  **divisibility only** (`⟨entries⟩ ⊆ ⟨b_{k₀}⟩`, not `=`).
- NEW terminal lemma `terminal_bezout`: at the terminal state the cleared pivot gives
  `b_{k₀} = Σ (U⁻¹)_{1i}(V⁻¹)_{j1} · (∏C∘g)_ij` on `nbhd` (entry₁₁ = `b_{k₀}·unit`,
  `unit 0 ≠ 0`).
- `PrincipalInv` (both identities) is a **TERMINAL theorem**, assembled at leaf 5 (fold
  `StepInv` along the path, apply `terminal_bezout` at the leaf), feeding leaf 1
  (`RegionRepresents`) unchanged.

**In-tree corroboration**: thread-28 cert ("intermediate charts CAN be non-principal");
`worked.tex:659` (the chain is a terminal-chart invariant) — the paper itself uses principality
only at the terminal chart.

## Batteries (all EXIT 0; controller re-ran the first)

- `case1_witness_334.py` — (3,3,4) interior state `S=2, J=0`: (D) preserved through both Case-1
  sub-cases with the explicit q'-law; (B) false there and after 1(1), true only at bare-diagonal.
- `case1_deeplayer_killset.py` — (3,3,2,2) deep-layer Bézout-failure + (2,2,3,2) non-monotone.
- `case1_schur_cofactor.py` — the projection-cofactor witness transport (`Q̂` unipotent,
  regenerates quotients).

## Honest gaps (named, not silent)

- The ∀-L divisibility-chain preservation rests on the structural chain argument (the
  thread-28-flagged inductive-not-exhaustive residual); the thread-31 closed form
  `b_i = ∏_{t̃<i} u` supplies it structurally — to be carried as a named leaf hypothesis /
  proof obligation, per the elder's delta-ratification ruling.
- Two-of-more charts modeled; pivot-ordering (`k₀` rendering) needed for the Lean statement.
- Suggested boundary-marker lemma: `bezout_iff_terminal` (`b₁ ∈ ⟨entries⟩ ⇔ S=L ∧ J≥1`) to
  force terminal-only scoping in the skeleton.

## ADDENDUM (elder-ordered, 2026-07-21) — the division's BOOKKEEPING SIDE is corrected; the law survives
This certificate's witness law places the exact division on the WITNESS side: q′ = (φ*q)/u^δ with
b′ = u^δ·φ*b and the residual carried implicitly. Under the foldState data/proof split (the elder's
design guard), the division belongs on the RESIDUAL side: **resid′ = the strict transform
(the per-case Let-block closed forms — for center coordinates, blockBlowupCoordQuot, which is data),
and the witness law becomes q′ = q∘σ — no division on the witness at all.** The two bookkeepings are
mathematically equivalent (the u^δ factor sits in resid′ instead of q′); the EXACTNESS content —
this certificate's central finding — is unchanged and remains the load-bearing fact. Also corrected
in the same round: the composition ORDER (see thread-33's addendum — the per-step atom is
blockBlowupMap ∘ shear, blow-up outermost, THIS certificate's β∘σ_shear order, which the elder
adjudicated as the paper-faithful one; thread-33's opposite grouping was the initialization
artifact). Elder rulings in the journal, 2026-07-21 (FIX-A + FIX-RESID — "one mechanism, two
halves").
