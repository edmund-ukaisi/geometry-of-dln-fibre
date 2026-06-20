**1. Elementary Degenerations**

Use the linked-segment form. For intervals
`I=[a,b]`, `J=[c,e]` with

```text
a < c <= b+1 <= e
```

set `I ∪ J = [a,e]` and `I ∩ J = [c,b]`, with `M_[c,b]=0` when `c=b+1`. The elementary degeneration in your rank direction is

```text
M_[a,e] ⊕ M_[c,b]  -->  M_[a,b] ⊕ M_[c,e].
```

For the overlapping case this is exactly

```text
a < c <= b < e.
```

For `c=b+1` it is the split

```text
M_[a,e]  -->  M_[a,b] ⊕ M_[b+1,e].
```

So: the split is the empty-intersection boundary case of the same linked-segment operation, but in a formalization it is cleaner as a separate constructor unless you allow zero intervals.

The rank drop is explicit:

```text
r'_{ij} = r_{ij} - 1   iff   a <= i < c  and  b < j <= e,
r'_{ij} = r_{ij}       otherwise.
```

The one-parameter family is the extension family for

```text
0 -> M_[c,e] -> M_[a,e] ⊕ M_[c,b] -> M_[a,b] -> 0,
```

with extension class `t`; `t≠0` gives the middle term, `t=0` gives the split sum. For the split case, put scalar `t` on the arrow `b -> b+1` and identities elsewhere.

Known/citable: Abeasis–Del Fra prove the rank-order/orbit-closure theorem; Lehalleur–Rimányi quote it as Theorem 3.8 and explicitly say the converse uses lace diagrams. ([arxiv.org](https://arxiv.org/html/2411.19920v2)) The exact-sequence realization is the usual Riedtmann–Zwara degeneration mechanism. ([arxiv.org](https://arxiv.org/abs/1506.05832))

Important caveat: a bare linked move is a codimension-one minimal disjoint degeneration, but after adding arbitrary common summands it need not be a cover of the full rank poset. Covers are the context-minimal applicable linked moves.

**2. Move-Existence Lemma**

The useful no-overshoot form is:

Given `s <= r`, `s ≠ r`, let `g = r-s`. There exists an applicable linked move on `m(r)` with indices

```text
a < c <= b+1 <= e
```

such that its drop rectangle

```text
D(a,c,b,e) = { (i,j) : a <= i < c and b < j <= e }
```

is contained in `{(i,j) : g_{ij} > 0}`. Then `r' = r - 1_D` satisfies

```text
s <= r' < r.
```

Deterministic choice rule that actually avoids overshoot:

1. In the finite interval `{u : s <= u < r}`, choose a maximal `u`, with any fixed lexicographic tie-break.
2. Then `r` covers `u`.
3. By the cover classification / elementary-operation theorem, `u` is obtained from `r` by one linked move.
4. Since `u >= s`, its drop rectangle lies inside the positive gap of `r-s`.

Equivalently for implementation: enumerate all applicable linked moves of `m(r)`, keep those with `D ⊆ supp(r-s)`, choose the lexicographically first. The theorem is exactly the assertion that this filtered list is nonempty.

This is the correct replacement for “split the longest bar at the first deficient column”; that rule can drop ranks outside `supp(r-s)`.

**3. Induction Measure**

Use

```text
Φ(r;s) = Σ_{i<j} (r_{ij} - s_{ij}).
```

The diagonal terms are zero because the dimension vector is fixed. A chosen move subtracts `1` on a nonempty rectangle `D ⊆ supp(r-s)`, so

```text
Φ(r';s) = Φ(r;s) - |D|.
```

Thus repeated moves terminate at `s`. No codimension or crossing statistic is needed for termination, although lace crossing number/codimension is the geometric shadow in the standard proofs.

**4. Verdict**

The induction is clean once the no-overshoot move-existence lemma is available.

But the move-existence lemma is the crux. Proving it is essentially the Abeasis–Del Fra / Zelevinsky multisegment / lace-diagram combinatorics. You can package it as a finite rank-array cover argument, but the proof that every cover is a linked-segment operation, and that some cover lies inside `[s,r]`, is the real content. So this does not give a genuinely elementary “just split bars by rank gaps” proof unless you reprove the lace/multisegment cover theorem in array language.

**5. Citations**

Primary: Abeasis–Del Fra, *Degenerations for the representations of an equioriented quiver of type A_m*, Boll. Unione Mat. Ital. Suppl. 2, 157–171, 1980; quoted as the rank-order closure theorem by Lehalleur–Rimányi. ([arxiv.org](https://arxiv.org/html/2411.19920v2))

Related standard machinery: Riedtmann–Zwara exact-sequence characterization of module degeneration; Bongartz-style minimal disjoint degeneration theory; Knutson–Miller–Shimozono for type-A lacing diagrams/quiver combinatorics. ([arxiv.org](https://arxiv.org/abs/1506.05832))