# Reproduction - Lemma 5 Source Chart-Family Reconstruction

Status: source reconstruction draft; not formalisation-ready.

This note rebuilds the remaining source-facing gap in Aoyagi Lemma 5 after the
finite count and supplied one-coordinate wrappers.  The goal is to isolate the
exact elementary obligations that would be needed before a Lean theorem can
claim the paper's source-backed chart-family realisation.

## Source

Aoyagi Lemma 5, PDF pp. 25-27, proceeds in four moves.

1. Define lower and upper chains `Htilde_j` and `Htilde'_j`, with
   `Htilde_ell = Htilde'_ell = 0`.
2. Use Lemma 4: a displayed vector `T_{s,k}` corresponds to `lambda` if
   `Ttilde <= T_{s,k} <= Ttilde'` and the induced chain increments are all
   `M-1` or `M`.
3. Count the intervals `{H : Htilde_j <= H <= Htilde'_j}` and obtain the
   elementary count `a(ell-a)+1`.
4. Assert that, using the displayed `T_{s,k}` formulas, the blow-up process is
   constructed in Case 1(2), establishing `theta = a(ell-a)+1`.

The Lean library already covers the count in step 3 and several supplied-data
one-coordinate wrappers.  The remaining gap is step 4.

## Existing Lean Boundary

Lean already has:

- interval/excess arithmetic and the total count
  `aoyagiHtildeIntervalValueSetNat_excess_sum_Icc`;
- supplied one-coordinate coverage by Eq3-shaped upper, Eq4 lower, and Eq5
  strict-offset values;
- supplied source-label wrappers for selected branch values under explicit
  actual-width and label-bound hypotheses;
- supplied recurrence/exponent-domain wrappers where terminal-exponent and
  least-value data are explicit hypotheses.

These are not source-backed chart-family construction theorems.

## Obligations For A Source-Backed Lemma 5 Theorem

For each displayed branch family in the PDF, a source-backed theorem needs the
following fields.

### Branch Data

For every intended label `(s,k)`:

```text
1 <= s <= L,
1 <= k <= n(s+1),
T(s) = k-1.
```

The current Lean source-label wrappers prove only selected cases under
explicit actual-width compatibility and supplied label bounds.  Known
counterexamples show that these bounds do not follow from Definition 3 alone.

### Chain Bounds

For every source coordinate `S`, the displayed vector must satisfy:

```text
Ttilde(S) <= T(S) <= Ttilde'(S).
```

This is the hypothesis needed by Lemma 4.  The current interval-value-set
theorems prove one-coordinate value membership, not full vectorwise bounds.

### Lemma 4 Increment Test

If `H_j` is read from the displayed vector by
`T(S_(j+1)-1)=H_j`, then each increment must be:

```text
H_(j-1) - H_j + M(S_(j+1)) = M-1 or M.
```

This is an elementary finite-difference check, but the PDF does not spell it
out for equations `(3)`, `(4)`, or `(5)`.

### Case 1(2) Chart Sequence

The final line of Lemma 5 says that equations `(3)` and `(4)` construct the
blow-up process in Case 1(2).  A formal theorem needs a finite chart sequence
with:

- the selected label at each step;
- the gap/admissibility condition used by Case 1(2);
- the recurrence update identifying the post-state;
- terminal endpoint convention and final `tilde t = 0`.

The source does not provide this sequence explicitly.

### Counting And Nonduplication

The finite interval count is already proved, but a source-backed order-count
theorem must still connect counted values to branch labels without loss or
duplication.  The supplied one-coordinate cardinality wrappers are local; they
do not aggregate over all `p` or prove that the printed branch families cover
all counted terminal variables.

## Equation-Specific Status

### Equation `(3)`

Safe current boundary:

- component-value upper endpoint under a supplied Eq3-shaped certificate;
- source-label status only under supplied actual-width compatibility and
  supplied label bounds.

Open source obligations:

- prove or supply `1 <= Htilde'_p+1 <= W_p` for p-general component labels;
- handle the printed special pair `(S_2-1,Htilde'_1+1)`, which is explicitly
  excluded from equation `(2)`;
- supply a terminal endpoint convention if the vector is to end with
  `tilde t = 0`.

Guardrails:

- Eq3 label legality is false from Definition 3 alone.
- At `a=1`, the printed special assignment puts value `1` at the terminal
  selected endpoint, while Definition 3 gives `Htilde'_ell=0`.

### Equation `(4)`

Safe current boundary:

- own-coordinate lower endpoint value under the repaired guards;
- source-label status under explicit actual-width compatibility.

Open source obligations:

- strengthen the printed guard `j0 <= a` to include own-coordinate consistency
  `j0 <= ell-a`;
- handle the selected cutoff `S_(j0+ell-a+2)`, which requires an additional
  index-existence or terminal convention;
- supply terminal/tail data for `tilde t = 0`;
- prove the full vectorwise chain bounds and Lemma 4 increments.

Guardrails:

- Eq4 terminal-collision width compatibility is not forced by Definition 3.
- The printed guard is too weak at boundary cases unless a source convention
  supplies extra endpoint data.

### Equation `(5)`

Safe current boundary:

- strict-offset value membership in the same-coordinate interval with both
  endpoints erased;
- source-label status under explicit block-local actual-width dominance;
- recurrence/exponent wrappers only with supplied post-data, terminal
  exponent equality, and least-value proof.

Open source obligations:

- derive the actual-width dominance for all off-selected source coordinates,
  or include it as a strengthened source assumption;
- prove that every strict offset branch participates in the intended Case
  1(2) sequence;
- aggregate over all strict offsets without overcounting.

Guardrail:

- Eq5 actual-width dominance is not forced by value-level selected-width
  hypotheses when duplicate selected width values occur.

## Formalisation Consequence

A source-backed Lemma 5 theorem should not be attempted yet.  The next honest
formalisation target is a supplied chart-family interface whose fields match
the obligations above.  Such an interface may be useful later, but it would be
a supplied-data boundary, not a proof that Aoyagi's displayed equations satisfy
the fields.

## Next Source-Reproduction Tasks

1. Reproduce the vectorwise inequalities `Ttilde <= T_{s,k} <= Ttilde'` for
   equations `(3)`, `(4)`, and `(5)` under explicit guards.
2. Reproduce the Lemma 4 increment test for the same equations.
3. Decide whether the Case 1(2) chart sequence can be reconstructed from
   earlier sections of the paper or must remain a supplied/cited boundary.
4. Only after those checks, design a Lean structure for supplied
   chart-family realisation and connect it to the existing count theorems.

## Nonclaims

- No source-backed displayed vector family is constructed here.
- No source-label legality is derived from Definition 3 beyond existing Lean
  theorems.
- No terminal `tilde t=0`, chart sequence, order count, normal crossings, or
  RLCT extraction is proved.
