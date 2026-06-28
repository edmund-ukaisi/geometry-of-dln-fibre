# Reproduction - selected-entry analytic atlas/source-production frontier

Date: 2026-06-28.

Status: pen-and-paper frontier recheck after the finite selected-entry layer
saturation audit.  This note intentionally proposes no Lean theorem.

## Question

Can the finite all-pivot selected-entry Case 2 certificate be promoted into a
`SelectedEntryAnalyticAtlasBoundary`, using Aoyagi pp. 19-22 as the source
calculation?

Answer: no.  Aoyagi pp. 19-22 support the displayed local Case 2 algebra, but
they do not by themselves define analytic chart domains, source-neighborhood
coverage, analytic transition maps, source-produced successor/suffix data, or
analytic Jacobian/volume-form compatibility.  A constructor from the finite
selected-entry certificate to `SelectedEntryAnalyticAtlasBoundary` would
therefore be a finite-to-analytic overclaim.

## Source Anchors

Aoyagi p. 19 begins Case 2 under the equality

```text
b_{J+1} = b_{J+2} = ... = b_{M(S)}
```

and blows up the residual block entries

```text
d_ij = 0
for i = J+1, ..., M(S) and j = J+1, ..., M^(S+1).
```

On the displayed pivot chart the residual block is written as a selected
scalar `u_{S,J+1}` times a normalized matrix whose pivot entry is `1`.
The page then lists the new bookkeeping data:

```text
t_{S,J+1}^{(i)} = M^(i+1)        for i = 1, ..., S-1,
t_{S,J+1}^{(S)} = ... = t_{S,J+1}^{(L)} = J,
\tilde t_{S,J+1} = J,
b'_i = u_{S,J+1} b_i             for i = J+1, ..., M(S),
M'_{S,J+1} = (M(S)-J)(M^(S+1)-J).
```

The actual-width/prefix-minimum convention here is the one already recorded in
the A4 width-split notes: `M^(S+1)` is the actual reduced width of the next
layer, while `M(S+1)` denotes the relevant prefix minimum.

Aoyagi pp. 20-21 define an elementary regular matrix `Q`, use it to transform
the normalized block and following factor, and set

```text
C'_J^(S+1) = Q^-1 C_J^(S+1).
```

The same pages define a regular matrix `P`, clear the first column into a block
`D'''_J`, and display the product identity relating

```text
P diag(b) D_J C_J^(S+1)
```

to a cleared expression with `diag(b')`, `D'''_J`, and `C'_J^(S+1)`.  The
previous corrected-weight scalar transport note records the finite scalar
bookkeeping: under the `b'_i = u b_i` convention, the selected scalar is already
absorbed into the transported weights, so the printed extra scalar must not be
turned into a separate analytic Jacobian claim.

Aoyagi p. 21 says that if the next same-stage pivot remains, the inductive
statement continues with `J` increased by one.  If not, `D'''_J` collapses to a
unit row or unit column and the product is rewritten as the inductive statement
with `S` increased by one.  Aoyagi p. 22 then states the final `S = L+1`
inductive statement and the candidate exponent formula.

## Reproduced Local Algebra

The Case 2 calculation has the following elementary content.

1. Choose the displayed pivot in the residual block and write each center
   entry as either `u` or `u` times a normalized coordinate.

2. Replace the lower-row weights by `b'_i = u b_i`.  This is the finite
   source of the corrected Case 2 new-label numerator

   ```text
   (M(S)-J)(M^(S+1)-J).
   ```

3. Apply the regular column operation `Q` to normalize the first row and
   transport the following factor by `Q^-1`.

4. Apply the regular row operation `P` to clear the first column after the
   weight substitution.

5. The remaining lower-right block is the successor residual block for the
   same-stage branch; if no same-stage pivot remains, the displayed unit row or
   unit column is stripped and the product advances to the next stage.

All five steps are finite matrix algebra or finite chart-map algebra.  They
support the existing selected-entry certificate layer and the finite
`SourceProductionObligation` consumers.  They do not define an analytic atlas.

## Branch Table

After the displayed pivot `(J+1,J+1)` is selected, three branch situations must
remain separate.

```text
continuing:
  J+2 <= prefixMinNat n (S+1)

actual-width stopped:
  n (S+1) = J+1

row-exhausted stopped:
  prefixMinNat n S = J+1
```

The source prose combines the two stopped cases through the condition that no
next same-stage pivot remains.  Lean-side source production must not collapse
them, because terminal payloads and suffix/source rows differ depending on
whether the actual next width stops first or the current prefix rows are
exhausted.

## Existing Lean Layer

The finite selected-entry layer already proves or packages:

- selected-entry chart maps and source chart points;
- finite center square-sum principalization;
- formal pivot-first Jacobian exponents;
- all-pivot finite selected-entry coverage of center values;
- finite affine overlap formulas, inverse laws, and cocycle;
- displayed Case 2 source-coordinate adapters;
- formula-level `SourceProductionObligation` constructors and consumers;
- a supplied `SelectedEntryAnalyticAtlasBoundary` structure whose analytic
  fields remain explicit.

This layer is useful, but it is still finite algebra.  It cannot fill:

- analytic chart domains or chart tokens;
- full analytic chart maps on source neighborhoods;
- source-neighborhood coverage;
- analytic or regular transition maps on overlaps;
- unit nonvanishing and regularity on chart domains;
- analytic Jacobian or volume-form compatibility;
- chart-produced successor, terminal, and suffix data;
- branch and termination coverage for the recursion.

## Rejected Constructor

Do not build

```text
SelectedEntryAnalyticAtlasBoundary.of_case2ResidualBlockCenterSqFormalJacobianChartFamilyCertificate_finiteSuppliedBranch
```

if its proof fills the analytic-atlas fields using finite all-pivot
selected-entry coverage, `SelectedEntryFiniteAffineTransitionRegularFamily`,
or `SourceProductionObligation` constructors.  Such a theorem would not add
source-produced analytic data; it would only rename finite chart algebra as
analytic coverage and regularity.

The only safe finite wrapper would be a deliberately non-analytic structure,
for example a `Case2FiniteSelectedEntryChartBoundary` whose fields are named
as finite coverage, finite affine overlap, and finite principalization.  That
wrapper is low value at this point unless a downstream theorem consumes
exactly that bundle.

## Next Real A4 Target

The next non-wrapper A4 target is a source-production and analytic-atlas
producer specification.  It should state, before any Lean implementation:

1. chart domains and chart tokens;
2. chart maps on those domains;
3. source-neighborhood coverage;
4. analytic or regular overlap maps;
5. unit/Jacobian/volume-form compatibility;
6. produced successor/suffix/terminal data on each chart;
7. branch and termination coverage.

Only after those fields are pinned should Lean introduce a new constructor or
tighten the A4/A0 final sockets.

The A2 adjacent-window source-readback adapter remains parked unless a
downstream theorem needs exactly that interface.  It would be a useful adapter,
not source production.

## Kill Conditions

- If a theorem uses finite selected-entry coverage as analytic atlas coverage,
  reject it.
- If a theorem uses finite affine transition formulas as analytic transition
  regularity without domains and overlap regularity, reject it.
- If a theorem uses `SourceProductionObligation` as source production without
  a produced source chart and coverage theorem, reject it.
- If a theorem collapses the continuing, actual-width-stopped, and
  row-exhausted stopped branches, reject it.
- If a theorem claims normal crossings, pole order, or RLCT from this finite
  Case 2 algebra, reject it.

## Nonclaims

This note proves no Lean theorem.  It does not prove analytic atlas existence,
coverage, transition regularity, analytic Jacobian control, source-produced
successor/suffix data, branch termination, normal crossings, pole order, or
RLCT.
