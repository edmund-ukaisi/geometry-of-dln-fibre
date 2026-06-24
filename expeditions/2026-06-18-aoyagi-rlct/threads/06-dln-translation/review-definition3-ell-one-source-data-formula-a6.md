# Review - Definition 3 `ell=1` source-data formula

Date: 2026-06-24.

Reviewer: xhigh independent reviewer `Avicenna the 3rd`.

## Verdict

PASS.  No required corrections.

## Source Fidelity

The reviewer checked Aoyagi PDF pp. 8-9 from the local source text.  The slice
is faithful to Definition 3's value-level selected/nonselected reduced-width
conditions, and to Theorem 2 specialized at `ell=1`, `a=1`.

## Mathematical Check

The proof correctly derives the previously supplied inputs from
`S : AoyagiDefinition3SourceData L 1 H r C`:

- selected positivity from the two strict selected inequalities;
- selected value-set cover from the landed `ell=1` obstruction;
- selected Nat-width provenance from source-range rank-width;
- the finite formula by delegating to the existing arbitrary-depth selected
  pair package.

For `ell=1`, the Theorem 2 finite formula becomes

```text
lambda = regularTerm + u*v/2,
order = 1.
```

## Lean/API Check

Focused Lean check passed:

```text
lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

The theorem is a source-data wrapper and does not duplicate the lower-level
selected-pair formula proof.

## Scope Check

No overclaim found.  The result does not infer `ell=1`, choose a canonical
branch, assert branch-independent formula payloads, add a final socket, or
claim Eq5 construction, chart production, normal crossings, pole order, RLCT
extraction, or quiver-based facts.
