# Review - A2 With-Following Source-Cylinder Raw-Patch Handoff

Date: 2026-07-07.

Reviewers: xhigh read-only reviewers `Halley the 2nd`, `Planck the 2nd`, and
`Boole the 2nd`.

## Verdict

No issues found.

## Source Fidelity

The handoff relies on Aoyagi pp. 10-13 only for the elementary
Schur-complement/block-elimination calculation

```text
Q1 A Q2 = [[A1, 0], [0, A4 - A3 A1^{-1} A2]]
```

and its retained-passive p.13 source-chart iteration.  The source supports the
raw/source chart algebra, not a global Haar transport or RLCT statement.

## Boundary Check

The theorem keeps the key support hypothesis explicit:

```text
chartPiece ⊆ sourceChart '' (V ∩ sourceCylinder).
```

It also keeps the source-density lower bound explicit on `baseJ.restrict V`.
The proof preserves `sourceCylinder` through the endpoint containment step and
then delegates to the existing active-containment raw-patch theorem.

## Usefulness

The theorem closes the source-cylinder raw-patch/source-density socket.  The
next API rung should be a formal-product source-cylinder wrapper that consumes
this theorem while keeping the same public support condition.

## Residual Risk

Downstream wrappers must not weaken the public support hypothesis to plain
`chartPiece ⊆ p13SourceSet` or `chartPiece ⊆ sourceChart '' V`.  P.13 image
support can be derived internally, but the source-cylinder hypothesis is still
needed for the active selected-entry containment route unless a separate
shrink-into-cylinder or C-one support theorem is supplied.
