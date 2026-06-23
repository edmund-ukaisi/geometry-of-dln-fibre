**Bottom Line**

DERIVED: from the pinned definitions alone, you can prove only the arithmetic `aoyagiTheta ℓ a = a*(ℓ-a)+1`.

INFERENCE - needs paper check: the faithful Aoyagi chart axis set is not determined by `balancedSplit`, `cAch`, or `aTheta`. The repo’s R1 notes point to Aoyagi’s affine blow-up exceptional divisors: axes are divisor coordinates, with typical binding divisor data `(k,h) = (1, codim(center)-1)`. The claim that exactly `a(ℓ-a)+1` of those axes tie is Aoyagi Lemmas 4-5 content, not derivable from the definitions you listed.

**Ranked Interpretations**

1. **Actual Aoyagi exceptional-divisor axes** - most faithful.
   Axis set: exceptional divisor coordinates in one achiever branch of Aoyagi’s affine blow-up recursion, plus nonexceptional/unit coordinates if retained.
   Formula: for a smooth blow-up center of codimension `c_E`, `(k_E,h_E)=(1,c_E-1)`; unit directions have `k=0`.
   Tie axes: divisor types with `c_E = minAchieverCodim`; Aoyagi Lemmas 4-5 should identify them as one central/deepest divisor plus `a(ℓ-a)` transfer/mixed types.
   Status: INFERENCE - needs the paper’s chart bookkeeping. I would not define `achiverK/H` from this without reading pp.15-21 / Lemmas 4-5.

2. **Balanced transfer-axis surrogate** - best closed Lean witness, but not certified Aoyagi.
   Axis set: one diagonal axis, one spectator nonbinding axis, and directed transfer axes `(i,j) ∈ Fin ℓ × Fin ℓ`.
   Tie axes: diagonal plus transfers from a big split block to a small split block.
   This gives a genuine non-all-tied `monomialOrder`, but it is still a synthetic model unless R1/Aoyagi proves these are the resolution axes.

3. **Unordered complete-graph surrogate**.
   Axis set: diagonal, spectator, and unordered pairs `{i,j}` with `i<j`.
   Tie axes: diagonal plus mixed big-small pairs.
   This is more symmetric and counts unordered cross-pairs directly, but is slightly less convenient to encode as `Fin d`.

**Closed-Form Witness for Interpretation 2**

Let:

```text
ℓ := cAch M
P := Sprefix M (ℓ + 1)
a := aTheta M = P % ℓ
b := P / ℓ
d := 2 + ℓ * ℓ
```

Use axes:

```text
0             diagonal axis
1             spectator nonbinding axis
2 + i*ℓ + j   transfer axis (i,j), for i,j : Fin ℓ
```

Define:

```text
isBig(i) := i < a
isSmall(j) := a ≤ j

isTie(0) := true
isTie(1) := false
isTie(2 + i*ℓ + j) := isBig(i) ∧ isSmall(j)

achiverK M axis :=
  if axis = spectator then 0 else 1

achiverH M axis :=
  if isTie axis then b else b + 1
```

Then:

```text
axisRatio tie        = (b+1)/2
axisRatio non-tie    = (b+2)/2
axisRatio spectator  = ⊤
```

So the minimum is attained exactly on:

```text
{diagonal} ∪ { (i,j) | i < a ∧ a ≤ j }
```

Count:

```text
1 + #{i | i < a} * #{j | a ≤ j < ℓ}
= 1 + a * (ℓ - a)
= aoyagiTheta ℓ a
```

Thus, under `hL : 1 ≤ L` so `1 ≤ cAch M` and `a < ℓ`:

```text
monomialOrder (achiverChartDim M) (achiverK M) (achiverH M)
  = aoyagiTheta (cAch M) (aTheta M)
```

**Important Flags**

The `+1` diagonal should be treated as a genuinely distinct binding direction in the intended geometry, not as one of the pair axes. If you model it as all self-pairs `(i,i)`, you get `ℓ`, not `1`.

The `a(ℓ-a)` count is not both ordered directions. It is either unordered mixed big-small pairs, or directed transfers with the direction forced from big to small. Counting both orientations gives `2*a*(ℓ-a)`, wrong.

**Biggest Collapse Risk**

If you define the axis set as only the tying axes:

```text
d = a*(ℓ-a)+1
all tie
```

then you have just rebuilt the rejected trivial witness. Avoid this by making `d` larger than the tie count and including actual nonbinding axes: same-size/wrong-direction transfer axes, plus unit/spectator axes with `k=0`.

But the deeper risk is subtler: even the transfer-axis surrogate can still be a dressed-up free cover unless you prove these axes correspond to Aoyagi’s exceptional divisor types. For a faithful A2b, the missing lemma is:

```text
AoyagiAchieverAxes M ≃ diagonal ⊕ big-to-small transfer axes ⊕ nonbinding axes
```

with the stated `(k,h)` ratios. Without that, A2b is combinatorially valid but not yet resolution-faithful.