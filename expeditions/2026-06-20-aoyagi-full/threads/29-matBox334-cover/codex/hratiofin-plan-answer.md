# Codex VET (gpt-5.5, xhigh) — hratiofin assembly

**Q1.** SOUND. With `R' r c = R (σr r) (σc c)` and `Aσ k j = A1 (σc k) j`, reindexing the mult sum
gives `(R'·Aσ) r j = (R·A1) (σr r) j`, and `frobSq` removes the output row permutation. Since `σc` is
a swap, inverse issues are only Lean rewrite-direction issues; guard by proving this exact local identity
in the same convention used for the substitution.

**Q2.** SOUND — substitute `A1` via `piCongrLeft σc`. Keeping A1 unpermuted forces a permuted wrapper
around the fixed-(0,0) `angularA1_integral_le`. Cheap guard: standalone box-invariance lemma
`A ∈ matBox 3 4 1 ↔ (fun k j => A (σc k) j) ∈ matBox 3 4 1`.

**Q3.** Order `b → g → raw → S → A0` (A0 = row 0 of A1, S = rows 1,2). Translate `raw ↦ Δ` with fixed
`b,g`, enlarge to matBox 2 2 2; THEN `g` is a vol factor. Translate `A0 ↦ T` with fixed `b,S`, enlarge to
morseBox 4 3; THEN `b` is a vol factor. Finally enlarge `S: matBox 2 4 1` to matBox 2 4 3.
HIGHEST-RISK error: dropping `b` or `g` as spectators BEFORE the translation that actually removes them.

**Q4.** CONFIRMED — feeding `d = raw - γβ` into `angularA1_integral_le` is exactly right (LHS reconstructs
the raw lower-right block; RHS uses the de-shifted Δ=d). Still need the outer `raw↦Δ` bound to compare the
z-domain with the resolved integral, but it is parameterwise LINEAR: for fixed b,g it is just
`measurePreserving_add_right` on the raw subblock. Do NOT package as one global product translation
depending on b,g; prove under fixed outer parameters.

Cheapest guard: two small parameterized translation/enlargement lemmas
(`raw ↦ raw - γβ ⊆ [-2,2]^4`, `A0 ↦ A0 + βS ⊆ [-3,3]^4`), drop params only AFTER applying them.
