**Verdict**

Q1: **TRUE.** For every nonnegative integer width chain `M`,  
`minAdmRank(M) = minAdm(M)`.

Q2: **TRUE.** The cap-active case is not just the original recursion; it needs one extra structural fact: `minAdm(w, W)` is Lipschitz in the leading width with constant `min(W)`.

Q3: **PROVED.**
`minAdm` is permutation-invariant in all widths, and for fixed nonempty tail `W`,
if `n = min(W)`, then
```text
0 <= minAdm(w+d, W) - minAdm(w, W) <= d*n
```
for all `w,d >= 0`.

**Proof Sketch**

Let `F = minAdm`. For fixed tail `W`, write `H(w)=F(w,W)` and `n=min(W)`.

Key lemma: `H` is monotone and `n`-Lipschitz:
```text
H(w+d) <= H(w) + d*n.
```
This follows after proving `F` is permutation-invariant, so we may put the smallest tail width first: `W=(n,R)`. Then
```text
H(w)=min_r [(w-r)(n-r)+F(r,R)],   0 <= r <= min(w,n).
```
Using an optimizer for `H(w)` gives the upper Lipschitz bound immediately. Monotonicity follows by comparing an optimizer for `H(w+d)`; if its pivot `r <= w`, reuse it at `w`, and if `r>w`, use induction on the shorter tail `R`.

Permutation invariance is also internal to the recursion. Define
```text
(K_m f)(a)=min_{0<=t<=min(a,m)} (a-t)(m-t)+f(t).
```
Then `F(a,m1,...,mL)=K_m1 ... K_m(L-1) B_mL(a)`, where `B_m(a)=am`. The operators commute because the three-width quantity
```text
min_t (A-t)(B-t)+Ct
```
is symmetric in `A,B,C` by the explicit quadratic minimization formula. This proves adjacent swaps, hence full permutation invariance.

Now prove Q2. Let `W=(M2,...,ML)`, `n=min(W)`, and `u=min(M0,M1)`. The original recursion allows the cut `u`, whose first term is zero, so
```text
F(M0,M1,W) <= F(u,W).
```
For a cap-active cut `t`, we have `M1-t > n`, so the rank-corrected candidate is
```text
(M0-t)n + F(t,W).
```
By Lipschitz,
```text
F(u,W) <= F(t,W) + (u-t)n <= F(t,W) + (M0-t)n.
```
Therefore every cap-active rank-corrected candidate is still at least `F(M)`. Cap-inactive cuts are immediate from the original recursion.

Finally, Q1 follows by induction on the number of layers. The rank recursion has termwise smaller block charges, so `minAdmRank <= minAdm`. But by Q2, after replacing shorter-tail `minAdmRank` with `minAdm` by induction, every rank-recursion candidate is `>= minAdm(M)`. Hence equality.

By-hand checks consistent with the proof:
```text
M=(2,4,1):       minAdm = minAdmRank = 2
M=(4,4,2,2):     minAdm = minAdmRank = 4
M=(3,3,3,4):     minAdm = minAdmRank = 7
```

No counterexample exists under the stated integer recursion.