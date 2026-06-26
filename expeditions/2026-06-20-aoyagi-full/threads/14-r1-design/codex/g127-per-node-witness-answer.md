**Verdict: WITNESS.**

**FACT:** On the computed reduced node of `(3,3,3)`, the blow-up chart has a hard pivot `Â[0,0] = 1`. The row/column clearing matrices

```text
L = [[1,0,0],[-r,1,0],[-u,0,1]]
R = [[1,-p,-q],[0,1,0],[0,0,1]]
```

are unipotent, hence `det L = det R = 1`, and no division is used. The Schur block is

```text
S = [[s-pr, t-qr],
     [v-pu, w-qu]]
```

and the witnessed identity straightens the loss into regular pivot-row variables plus `||S · A2red||^2`.

**INFERENCE:** This is not special to the outer/top chain. At any reduced node with a hard pivot, the same block calculation applies. Writing

```text
A = [[1, a],
     [b, D]],
L = [[1, 0],
     [-b, I]],
R = [[1, -a],
     [0, I]],
S = D - b a,
```

we have

```text
L A R = [[1, 0],
         [0, S]]
```

with `L` and `R` transvections of determinant `1`. The pivot-row product variables are regular because the pivot is literally `1`, so their Jacobian block is the identity. The residual is the smaller chain product `S · Bred`, hence again a matrix-chain zero-core.

**Hard-1 Pivot Interface**

**FACT:** The raw zero-core origin has all-bilinear generators and no regular block, so straightening cannot start there. A blow-up is required first.

**INFERENCE:** At every nonterminal reduced node, the residual is again a zero-product matrix-chain core at its own origin. Blowing up the relevant coordinate/rank-stratum center gives affine charts indexed by a nonzero homogeneous coordinate; in each such chart, that chosen coordinate is normalized to `1`. Thus locally on every blow-up chart, the next pivot is again hard `1`.

Qualification: no single chart supplies the pivot for all exceptional directions, but the blow-up chart cover always supplies some hard-1 pivot locally. If the chosen pivot coordinate vanishes, that point belongs to another chart. That is not an obstruction.

**Residual / Recursion**

**FACT:** In the witnessed `(3,3,3)` reduced node, the residual is `||S · A2red||^2`, with `S` a `2 x 2` Schur factor and `A2red` the lower two rows of `A2`.

**INFERENCE:** This is the same class of object: a smaller matrix-chain zero-core `dlnLoss M' 0`. For dimensions `(m,n,...)`, the Schur step replaces the active factor by an `(m-1) x (n-1)` Schur factor and restricts the next factor to the matching `(n-1)` rows, so `ΣM' < ΣM` in every nonterminal step. Terminal zero-size or already-resolved cases simply stop the recursion.

**fm-2 Verdict**

`schur_straighten_exists` should be adjudicated as **WITNESS**, under the stated per-node post-blow-up interface:

```text
blow-up gives hard-1 pivot
→ determinant-1 transvection straightening
→ regular pivot-row block + smaller zero-core residual
→ recurse
```

No obstruction is exhibited by reduced nodes of the same class; the only obstruction is trying to straighten at the raw all-bilinear origin before the blow-up.