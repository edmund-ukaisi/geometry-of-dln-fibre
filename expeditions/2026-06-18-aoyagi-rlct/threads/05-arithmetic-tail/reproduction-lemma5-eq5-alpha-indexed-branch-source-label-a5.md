# Reproduction - Lemma 5 Eq5 alpha-indexed branch source labels

Status: reproduced; Lean checked; xhigh review pending.

## Source

Aoyagi PDF p. 27, equation `(5)`, uses a strict offset parameter `alpha` and
assigns the own-coordinate label

```text
k = Htilde'_p + 1 - alpha.
```

In Lean, the strict Eq5 alpha domain is

```text
aoyagiLemma5Eq5AlphaDomain ell a p
  = { alpha | 1 <= alpha <= min(excess(ell,a,p), p-1) }.
```

The earlier source-label theorem already proves that if `alpha` is in this
domain, the source coordinate is in range, the selected width is bounded by the
actual width at that source coordinate, and

```text
k = Htilde'_p + 1 - alpha,
```

then `actualWidthLabel L n S k`.

## Reproduction

Let `branches : Finset beta` be a supplied finite family of Eq5 strict-offset
branch records.  Assume supplied maps

```text
alphaOf : beta -> Nat,
branchLabel : beta -> Sigma (fun _ : Nat => Nat).
```

The first component of `branchLabel b` is the source coordinate `S_b`, and the
second component is the label `k_b`.  For each branch `b`, assume:

```text
alphaOf b in aoyagiLemma5Eq5AlphaDomain ell a p,
1 <= S_b <= L,
W_p <= n(S_b+1),
k_b = Htilde'_p + 1 - alphaOf b.
```

Then the existing alpha-family source-label theorem applies branchwise, giving

```text
actualWidthLabel L n S_b k_b.
```

Equivalently, the supplied branch label lies in `actualWidthLabelFinset L n`.
This is only a finite-set packaging of source-label legality; it is not a
construction of the branch records.

For injectivity, additionally assume `alphaOf` is injective on `branches`.
If two supplied branch labels are equal, then their second coordinates are
equal.  Using the displayed formula for both labels gives

```text
Htilde'_p + 1 - alphaOf b = Htilde'_p + 1 - alphaOf c,
```

so `alphaOf b = alphaOf c`, and the supplied alpha injectivity gives `b=c`.
Thus `branchLabel` is injective on `branches`.

## Lean targets

```text
aoyagiLemma5Eq5_alphaIndexedBranch_actualWidthLabel_of_widthBound
aoyagiLemma5Eq5_alphaIndexedBranchLabel_mem_actualWidthLabelFinset_of_widthBound
aoyagiLemma5Eq5_alphaIndexedBranchLabel_injOn
```

## Nonclaims

- No construction of Eq5 branch records.
- No proof that branch alphas cover the strict alpha domain.
- No selected-span coverage or terminal exactness.
- No construction of the displayed vector.
- No classifier, back-to-label map, exact order count, pole order, normal
  crossings, or RLCT extraction.

Do not infer injectivity from alpha-domain coverage alone; this slice requires
`Set.InjOn alphaOf branches` explicitly.
