# Reproduction - Lemma 5 terminal-minimum counted-datum classifier source attempt

Date: 2026-06-26.

Status: full classifier blocked by source; one conditional upper-bound target
is formalisation-ready.

## Goal

The Lean boundary is the supplied type

```text
TC.TerminalMinimumCountDatumClassifier
```

for a supplied terminal-candidate family `TC`.  Unfolding the abbreviation,
this is an `AoyagiLemma5CountDatumClassifier` on the finite set
`TC.terminalMinimumLabels`.  To construct it from the source one needs:

```text
classify : terminalMinimumLabels -> AoyagiLemma5CountDatum
mapsTo  : classify label in aoyagiLemma5CountDatumSet
injOn   : classify is injective on terminalMinimumLabels.
```

This note checks whether Aoyagi Lemma 5, PDF pp. 24-27, supplies these fields
without using the quiver-based paper or the cited normal-crossing-to-RLCT
extraction.

## Source Reproduction

Aoyagi proves the finite arithmetic feeding Lemma 5 as follows.

1. Lemma 3 gives the isolated quadratic minimum

   ```text
   A(a-1) = A(a) = a ell (ell-a).
   ```

2. Lemma 4 gives a sufficient criterion: if a vector `T_{s,k}` lies between
   the displayed lower and upper vectors and the associated increments are
   only `M-1` and `M`, then `T_{s,k}` corresponds to `lambda`.

3. Lemma 5's upper-count paragraph says that, when
   `t_{s,k}^{(S_{j+1}-1)} = H_j`, the possible values are counted by the
   intervals

   ```text
   Htilde_j <= H <= Htilde'_j,       j = 1,...,ell-1.
   ```

   The displayed interval-size profile sums to

   ```text
   1 + sum_j (|[Htilde_j,Htilde'_j]| - 1) = a(ell-a)+1.
   ```

4. The source then says that `J` is increased by one in Case 1(2), obtaining
   the upper bound, and displays branch families `(1)`--`(5)` for the lower
   bound.

The interval arithmetic and counted-datum codomain are already formalised.
The missing issue is not the finite sum; it is the classifier from arbitrary
terminal-minimum labels into that finite codomain.

## Missing Classifier Fields

The printed Lemma 5 paragraph does not give a Lean-level `classify` function.
For a label in `TC.terminalMinimumLabels`, one would still need a bridge from
the Lean label `(s,k)` to an Aoyagi source vector `T_{s,k}`, a selected-endpoint
chain `H`, and a rule choosing either the base datum or a nonbase datum
`some (j,H_j)`.

The `mapsTo` field is only conditional.  It follows from explicit terminal
chain data:

```text
H_0 = m_0,
H_ell = 0,
sum_i m_i = ell*(M-1)+a,
Delta_r(H) in {0,1},
```

together with a nonbase inequality when a nonbase coordinate is chosen.  This
is already represented by the terminal-binary maps-to theorem and the
first-nonbase selector.

The `injOn` field is not proved by the source.  The sentence that `J` increases
by one in Case 1(2) records blow-up progress; it is not a proof that two
terminal-minimum labels with the same counted datum are equal.

A back-to-label map is also absent.  The displayed families `(3)`, `(4)`, and
`(5)` have separate guard and terminal-endpoint issues recorded in the
displayed-family obstruction notes, so they cannot currently supply a
complete inverse from counted data to branch labels.

## Source-Faithful Conditional Target

The full classifier should remain supplied.  A smaller source-faithful target
does exist:

```text
TC.terminalMinimumLabels.card <= a * (N + 1 - a) + 1
```

from explicit Eq5 terminal endpoint-chain data and injectivity of the existing
deterministic selector

```text
label |-> aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase
           (N+1) (Hlabel label) TC.family.baseValue.
```

For each terminal-minimum label this theorem assumes:

- an Eq5 piecewise source vector;
- terminal-room inequality for the Eq5 endpoint-chain binary theorem;
- an endpoint chain `Hlabel label`;
- `H_0=m_0` and `H_(N+1)=0`;
- endpoint agreement
  `H_b = T(cut.point b - 1)` for `1 <= b < N+1`;
- injectivity of the deterministic first-nonbase selector on
  `TC.terminalMinimumLabels`.

Then `aoyagiLemma5Eq5_endpointChain_binaryIncrementPrefixDelta_of_terminalRoom`
supplies the binary increments, and the existing
`aoyagiLemma5FirstInteriorNonbaseCountDatumOrBase_candidates_card_le` theorem
gives the upper bound.

This removes the abstract counted-datum classifier object from this route,
but it does not prove the remaining injection from Aoyagi's source.  It is a
conditional upper-bound theorem, not Lemma 5 exactness.

## Kill Conditions

- Do not construct `TC.TerminalMinimumCountDatumClassifier` unconditionally
  from Aoyagi pp. 24-27.
- Do not read the Case 1(2) `J`-increase sentence as an injectivity theorem.
- Do not treat Lemma 4 as a converse from terminal-minimum labels to
  lambda-vectors.
- Do not use equations `(3)`, `(4)`, or `(5)` as complete source families
  without their explicit guard and terminal-endpoint hypotheses.

## Nonclaims

No source-backed counted-datum injection, back-to-label map, no-extra theorem,
branch-label injectivity, terminal-label exactness, pole-order statement,
normal-crossing theorem, or RLCT extraction is proved here.
