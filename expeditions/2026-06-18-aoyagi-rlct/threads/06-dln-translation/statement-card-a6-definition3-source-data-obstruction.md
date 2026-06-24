# Statement card - A6 Definition 3 source-data obstruction

Status: Lean diagnostic landed.

Reproduction:
`reproduction-definition3-source-data-obstruction-a6.md`.

Independent source/Lean review:
`review-definition3-source-data-obstruction-a6.md`.

## Target

Record a finite diagnostic obstruction showing that Aoyagi Definition 3's
printed inequalities do not imply arbitrary selected-cutpoint/source-data
existence.

## Intended Lean Name

```text
AoyagiDefinition3SourceData.not_exists_widths_one_two_hundred
```

## Mathematical Content

For the reduced-width profile

```text
H(1)=1, H(2)=2, H(3)=100, r=0, L=2,
```

there is no `ell` and no strict selected-cutpoint package `C` satisfying

```text
AoyagiDefinition3SourceData 2 ell H 0 C.
```

The proof is finite:

- strict cutpoints in `{1,2,3}` force `ell=1` or `ell=2`;
- `ell=2` selects all three widths and fails `2*100 < 103`;
- `ell=1` selects two widths and the printed nonselected inequality has
  coefficient `ell-1=0`, forcing a positive selected sum to be `<=0`.

## Boundary

This is a guardrail theorem only.  It does not prove a corrected Definition 3,
does not classify when source data exists, and does not alter any downstream
wrapper that consumes supplied `AoyagiDefinition3SourceData`.

No selected-cutpoint construction, no Definition 3 source-data existence
theorem, no Eq5 construction, no Lemma 5 exactness, no chart production, no
normal crossings, no pole order, and no RLCT.

## Lean Status

Implemented in:

```text
lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean
```

Focused build passed:

```text
cd lean && scripts/lb DLNFibre.DLN.Aoyagi.Definition3Bridge
```
