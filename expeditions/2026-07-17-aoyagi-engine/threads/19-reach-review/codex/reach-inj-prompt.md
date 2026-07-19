# Independent audit: is this Lean injectivity argument sound?

You are an independent reviewer. I give you Lean 4 / Mathlib definitions and theorems from a
formalisation. Judge SOUNDNESS only; do not trust my framing. Report any gap, circularity, or
place where a stated theorem does not prove what its name suggests. Distinguish FACTS you can
verify from the text vs INFERENCES you are making. Do not write code I must build; reason about
the argument.

## Context (what the objects mean)

A construction builds a resolution tree by a well-founded recursion on a carrier state `ConState L`.
Each state carries an immutable per-divisor "birth corner" field:

    divBirthCoord : Fin s.numDiv → ℕ × ℕ

A divisor born at construction node `(layer, cleared)` records the pair `(layer, cleared)`. The
transitions are:
- `stepCase11 i` (merge): does NOT change layer/cleared/numDiv/divBirthCoord (only a profile field).
- `stepAppendAdvance e t₀` (birth): numDiv += 1, cleared += 1, layer unchanged, and
  divBirthCoord := Fin.snoc divBirthCoord (s.layer, s.cleared)  -- appends the OLD cleared, pre-increment
- `stepRollover`: layer += 1, cleared := 0, divBirthCoord unchanged.

The reachability invariant threaded down the construction:

    def CornerValid (M : Fin (L+1) → ℕ) (c : ℕ × ℕ) : Prop :=
      c.1 < L ∧ (∀ i : Fin (L+1), (i:ℕ) = c.1     → c.2 < M i) ∧
                (∀ i : Fin (L+1), (i:ℕ) = c.1 + 1 → c.2 < M i)

    def DivBirthInv (M) (s : ConState L) : Prop :=
      (∀ k, CornerValid M (s.divBirthCoord k)) ∧
      (∀ k, (s.divBirthCoord k).1 ≤ s.layer) ∧
      (∀ k, (s.divBirthCoord k).1 = s.layer → (s.divBirthCoord k).2 < s.cleared) ∧   -- "freshness"
      Function.Injective s.divBirthCoord

`widthMinUpto M n = min {M i : (i:ℕ) ≤ n}`, and `widthMinUpto_le : (i:ℕ) ≤ n → widthMinUpto M n ≤ M i`.

## The birth maintenance lemma (the crux)

At a birth the guard `hlt : s.cleared < widthMinUpto M (s.layer + 1)` holds (the non-rollover branch),
and `hlive : s.layer < L`. Claim: `DivBirthInv M s → DivBirthInv M (s.stepAppendAdvance e t₀)`.

Proof sketch given:
- New corner `(s.layer, s.cleared)` is valid:
  - layer: `s.layer < L` from hlive.
  - row bound: for `(i:ℕ) = s.layer`,      `s.cleared < widthMinUpto M (s.layer+1) ≤ M i` since `s.layer ≤ s.layer+1`.
  - col bound: for `(i:ℕ) = s.layer + 1`,  `s.cleared < widthMinUpto M (s.layer+1) ≤ M i` since `s.layer+1 ≤ s.layer+1`.
- New corner is fresh (not in range of old divBirthCoord): if `divBirthCoord j = (s.layer, s.cleared)`
  then `(divBirthCoord j).1 = s.layer` so freshness gives `(divBirthCoord j).2 < s.cleared`, but
  `(divBirthCoord j).2 = s.cleared` — contradiction.
- Injectivity preserved via `Fin.snoc_injective_of_injective hinj hnotmem`.
- Freshness re-established at the new state (cleared' = cleared+1): the appended corner has `.2 = cleared < cleared+1`;
  old corners at layer had `.2 < cleared < cleared+1`.
- Layer-bound: appended corner has `.1 = layer ≤ layer`; olds `≤ layer`.

Rollover maintenance: freshness becomes vacuous (`.1 = layer+1` impossible since olds have `.1 ≤ layer`).

## The birth-corner flat coordinate + its injectivity

`FlatIdx M = Σ (⟨s,i⟩ : Σ s : Fin L, Fin (M s.castSucc)), Fin (M s.succ)` (a triple layer/row/col).

    noncomputable def birthFlatCoord M s k (h : 0 < flatDim M) : Fin (flatDim M) :=
      if hL : (divBirthCoord k).1 < L then
        if hi : (divBirthCoord k).2 < M (Fin.castSucc ⟨(divBirthCoord k).1, hL⟩) then
          if hj : (divBirthCoord k).2 < M (Fin.succ ⟨(divBirthCoord k).1, hL⟩) then
            Fintype.equivFin (FlatIdx M) ⟨⟨⟨(dbc k).1, hL⟩, ⟨(dbc k).2, hi⟩⟩, ⟨(dbc k).2, hj⟩⟩  -- corner (a,b,b)
          else ⟨0,h⟩ else ⟨0,h⟩ else ⟨0,h⟩

Theorem `flatIdx_corner_inj`: if the FlatIdx sigma at `(a,b,b)` equals the one at `(a',b',b')` (with
their respective proofs) then `a = a' ∧ b = b'`. Proof: split outer sigma → col HEq + inner-pair eq;
split inner → layer eq `⟨a,_⟩ = ⟨a',_⟩` giving `a=a'`; then `Fin.heq_ext_iff` on the col component
(types `Fin (M (succ ⟨a,_⟩))` vs `Fin (M (succ ⟨a',_⟩))` equal since `a=a'`) gives `b=b'`. (The ROW
HEq component is discarded.)

Theorem `birthFlatCoord_injective`: under `DivBirthInv`, `fun k => birthFlatCoord M s k h` is injective.
Proof: validity ⟹ both k, k' take the real (equivFin) branch; equal flat coords ⟹ (equivFin injective)
equal sigmas ⟹ (flatIdx_corner_inj) equal corner pairs ⟹ (divBirthCoord injective from DivBirthInv)
k = k'.

Then `leafOfState.divCoord = fun i => birthFlatCoord M s ((t0Indices s).get i) h`, where
`t0Indices s = (List.finRange s.numDiv).filter (fun k => decide (divTilde k = 0))`, and its `.get`
is injective because `List.finRange` is Nodup, `.filter` preserves Nodup, and Nodup ⟹ injective_get.
So `leafOfState.divCoord` is injective (composition of two injectives).

## QUESTIONS

1. Is the birth maintenance lemma's validity step SOUND — in particular, does
   `s.cleared < widthMinUpto M (s.layer+1)` genuinely imply BOTH `s.cleared < M(layer)` (row) and
   `s.cleared < M(layer+1)` (col)? Check the index arithmetic (`layer ≤ layer+1` and `layer+1 ≤ layer+1`).

2. Does the fallback branch `⟨0,h⟩` of birthFlatCoord ever get consumed in the injectivity argument?
   I.e., is `birthFlatCoord_injective` genuinely establishing injectivity of the REAL map, or could a
   fallback collision (two divisors both mapping to `⟨0,h⟩`) sneak through under DivBirthInv?

3. Is `flatIdx_corner_inj` correct to recover `b=b'` from the COL component alone (discarding the row)?
   Is there any way distinct `(a,b)` ≠ `(a',b')` could still give equal FlatIdx sigmas at (a,b,b)/(a',b',b')?

4. Is the freshness invariant a genuine strengthening that CLOSES the induction (self-maintaining across
   births and rollovers), or is there a state where freshness could fail to be re-established — breaking
   the injectivity of divBirthCoord downstream?

5. Any circularity: does the injectivity of `birthFlatCoord` secretly ASSUME what it proves, or rely on
   the fallback being unreachable without proving it?

Be concrete. If a step is sound, say so and why. If you find a gap, give the minimal state/counterexample.
