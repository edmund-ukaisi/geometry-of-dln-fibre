## Q1

**TRUE.** Assuming the concrete inclusion
\[
S=\operatorname{blockCoords}(d,\ell)\subseteq L=\operatorname{layerCoords}(d,\ell),
\]
the two clauses imply `Deg1SupportedOn resid S univ`. This includes `S = ∅`, where clause 1 already forces `resid j ≡ 0`.

No continuity of the `AffineOn` witnesses is needed.

## Q2

**FACT:** Steps 1–2 are correct. Since `V = univ`, `ignoresCoords_univ_iff_agree` implies that an `L`-ignoring function has equal values at any two points agreeing outside `L`. Your zeroed/probe points do agree with `u` outside `L`.

For Step 2, specialize immediately to `t = 1`; then
\[
b_x(u)\cdot1=0
\]
and `simpa` gives `b_x u = 0`.

A shorter argument eliminates Steps 1–2 individually. Let `z_S(u)` zero only the `S`-coordinates. Clause 1 gives `f(z_S(u))=0`. Since `z_S(u)` and `u` differ only inside `S ⊆ L`, affine coefficient invariance gives
\[
0=a(u)+\sum_{x\in L\setminus S}b_x(u)u_x.
\]
Splitting the affine formula at `u` into `L \ S` and `S` then yields directly
\[
f(u)=\sum_{x\in S}b_x(u)u_x.
\]
This is likely the cleanest algebraic helper lemma.

## Q3

Your probe construction is the right canonical continuity repair. Define, for `i ∈ S`,
\[
q_i(u)_k=
\begin{cases}
1,&k=i,\\
0,&k\in S,\ k\ne i,\\
u_k,&k\notin S,
\end{cases}
\qquad c_i(u)=f(q_i(u)).
\]

Then:

- `f` is continuous because clause 1 expresses it as a finite sum of products of continuous functions.
- `q_i` is continuous and depends only on coordinates outside `S`.
- Hence `c_i = f ∘ q_i` is continuous and ignores `S`.
- The derived representation gives
  \[
  c_i(u)=f(q_i(u))=b_i(q_i(u))=b_i(u)
  \]
  for `i ∈ S`.

Subtle correction: **`c_i = b_i` is only needed, and automatically forced, for `i ∈ S`**. It need not hold for `i ∉ L`, because `AffineOn` places no condition on those unused `b_i`. Define `c_i := 0` for `i ∉ S`.

There is no route through proving `f` itself ignores `S`: generally it does not. The probe decomposition is the direct route.

## Q4

Useful confirmed v4.29 idioms:

- Use `classical` for the finset membership branches.
- Prefer `ignoresCoords_univ_iff_agree` over chains of updates.
- For probes, use
  ```lean
  Function.update (zeroS u) i 1
  ```
  where `zeroS u k := if k ∈ S then 0 else u k`.
- `Function.update_self` and `Function.update_of_ne` are present. The latter expects “queried coordinate ≠ updated coordinate”; a `.symm` is often needed.
- Use `Finset.sum_sdiff hSL` to split `L` into `L \ S` and `S`.
- For the original Step 2, `Finset.sum_eq_single` isolates the probe coordinate.
- From a universally quantified identity, avoid zero-product reasoning:
  ```lean
  have h := hprod (1 : ℝ)
  simpa using h
  ```

Continuity names verified in this checkout are `continuousOn_univ`, `continuousOn_finset_sum`, `ContinuousOn.mul`, `continuous_apply`, `continuous_pi`, `Continuous.update`, and `Continuous.comp`.