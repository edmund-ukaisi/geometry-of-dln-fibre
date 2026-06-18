# Reproduction check - Lemma 2 and Theorem 3

Status: independent xhigh checker `Ramanujan`. No files were edited by the
checker. Source used: Aoyagi 2023 PDF pp. 10-13 and
`reproduction-draft.md`.

## Verdict

- **A1:** checked only for the algebraic block identities and rank formula on
  the explicit `det(A1) != 0` chart. Not formalisation-ready under the broad
  claim wording if it includes RLCT invariance or loss-germ preservation.
- **A2:** not reproduction-checked/formalisation-ready as stated. The algebraic
  induction is mostly correct, but the missing basis/open-chart hypotheses and
  the post-Theorem-3 RLCT reduction cross the allowed citation boundary.

## Findings

### Source fidelity

- **High.** The draft says target normalization comes from constant row/column
  changes. On PDF p. 11, Aoyagi says "By Lemma 1, we can assume" the normalized
  true product. The linear-algebra gloss is plausible, but pp. 10-13 do not
  justify RLCT safety of that normalization.
- **Medium.** The draft states Theorem 3 as happening "after local analytic
  coordinate changes." Aoyagi's theorem statement asserts regular triangular
  matrices `P1`, `P2`; the coordinate-change interpretation is reconstructed
  from the proof's "transform variables" language.
- **Medium.** The draft repairs Aoyagi's dimension notation in the induction
  step, especially the lower-right identity in `Q2''`. The repair appears
  mathematically right, but should be recorded as a source typo/normalization,
  not presented as direct transcription.

### Mathematical content

- No sign or block-multiplication error was found in Lemma 2 or the displayed
  induction algebra.
- The main proof-promotion risk is the induction assumption that `A1'` is
  invertible. Aoyagi says "we can assume `C1' A1'` is regular" on PDF p. 12.
  Lean needs a separate basis/open-chart lemma before relying on `A1'`
  invertibility.

### Missing hypotheses

- The setup must include Aoyagi's neighborhood/rank hypotheses from PDF p. 11:
  each `A^(s)` is near `A*^(s)` with rank `r^(s)`, and `r^(s) >= r`.
- Theorem 3 needs explicit `r <= H^(s)` for every layer and explicit open-chart
  assumptions for every inverted `r x r` block.
- The hidden through-layer basis choice is load-bearing, not optional.

### Hidden analytic citations

The RLCT equality after Theorem 3 uses more than block algebra:

- local coordinate invariance;
- generator replacement;
- regular-coordinate additivity.

Under the single allowed Lean citation boundary, these cannot be separate hidden
citations. They must be proved/avoided or folded explicitly into the one
normal-crossing-to-RLCT extraction interface.

### Boundary cases

The draft names the right boundary cases but does not check them. Lean targets
must handle:

- `r = 0`;
- `r = H^(1)`;
- `r = H^(L+1)`;
- intermediate `H^(s) = r`;
- the resulting empty matrices.

## Controller consequence

Split the target:

1. A narrow algebraic Lemma 2 chart theorem is ready for Lean statement design,
   after adding exact open-chart and size hypotheses.
2. Theorem 3's algebraic induction needs a source-faithful through-layer
   open-chart/basis lemma before formalisation.
3. The post-Theorem-3 RLCT formula is not formalisation-ready and must not be
   named as proved until the analytic boundary issue is resolved.
