# Review - A6 Definition 3 `L=2` branch formula rank-width removal

Date: 2026-06-26.

Reviewer: xhigh `Raman the 3rd`.

## Findings

No issues found in the A6 slice.

The Lean changes legitimately derive the source-range rank-width hypothesis
`hr`:

- Nat-valued reduced-width equalities imply nonnegativity of
  `(H s : Int) - r`, hence `r <= H s`
  (`Definition3Bridge.lean`, around
  `rank_le_of_aoyagiReducedWidthInt_eq_natCast`).
- The `L=2` three-source wrapper only dispatches over `s=1,2,3`.
- Triangle inequalities are first converted into the all-source strict
  selected inequality, then existing strict-to-rank-width machinery supplies
  `hr`.

The new formula wrappers only remove explicit `hr`: they delegate directly to
the existing `_rankWidth` theorems and pass the derived rank-width hypothesis
for the triangle odd branch, triangle even branch, and repeated-positive
branch.

No overclaiming was found.  The reproduction note keeps branches separate and
disclaims canonical branch selection, branch independence, Eq5, charts, normal
crossings, pole order, and RLCT extraction.  This matches the branch-selection
source audit's conclusion that Aoyagi PDF pp. 8-9 print no canonical
Definition 3 tie-breaker.

## Verification

The reviewer also ran focused elaboration successfully:

```text
env LEAN_NUM_THREADS=1 /home/ubuntu/.elan/bin/lake env lean DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

The controller separately had already run the focused module build with the
local shared Lake cache:

```text
cd lean
env LAKE_SHARED="$PWD/.lake-local-shared" scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```

## Residual Risk

The older repeated-positive and triangle parity statement cards describe the
earlier `_rankWidth` APIs.  That is stale as API documentation after this
slice, but not a soundness or source-fidelity issue.  Add cross-references to
the new no-`hr` wrapper statement card.
