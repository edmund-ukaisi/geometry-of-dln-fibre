**G3.4 Verdict: COVER-EXHAUSTIVE.**

**FACT:** The rank-vector strata form a complete partition of `{C^(1)...C^(L)=0}`. For any fibre point, `t_j = rank(C^(1)...C^(j))` is weakly decreasing, satisfies `t_L=0`, and obeys `t_j <= M^{j+1}`. Conversely, every admissible rank vector is realised by choosing nested image subspaces and lifting through the partial products. Thus
`{prod=0} = disjoint union_t S(t)` exactly, not merely up to a null set.

For `(3,3,3)`, this is just the four cases `rank(A1)=0,1,2,3`, so `S(0,0), S(1,0), S(2,0), S(3,0)` exhaust the fibre.

**INFERENCE:** The full iterated pivot atlas reaches every admissible stratum, provided “pivot atlas” means all pivot minors/all coordinate flag charts, not one generic pivot choice. At a point of `S(t)`, each nonzero rank `t_j` partial product has some nonzero `t_j`-minor; choose those pivots, then the verified Schur-complement recursion gives the smaller tail-chain with the tail rank vector. Induction over the recursion gives a branch reaching `S(t)`. Therefore no admissible stratum is missed.

A single fixed pivot chart would miss coordinate pieces, but the full pivot atlas does not.

**G3.5(i) Verdict: SOUND, with the full-block interpretation.**

Let `m0 = min_Adm Mval`.

A terminal residual smooth block is a nondegenerate quadratic block
`x_1^2 + ... + x_n^2`, so its cone divisor has ratio `n/2`. In the flag/pivot resolution, the dimension `n = n_block` is not an arbitrary leftover count: it is the total smooth quadratic normal block accumulated along a completed recursive branch. The branch choices determine an admissible terminal rank vector `t_leaf`, and the accumulated block dimension is exactly

`n_block = Mval(t_leaf)`.

Hence `n_block >= m0`.

This matches the `(2,2,2)` delta branch: its residual block has `n_block=4`, corresponding to a non-minimal admissible value, while `m0=3`.

Caveat: counting only a last local smooth summand, rather than the full terminal residual quadratic block, would be the wrong object. Such a partial block need not itself be `>= m0`.

**G3.5(ii) Verdict: SOUND, assuming the stated flag-resolution theorem.**

There is no intermediate divisor of smaller ratio if every blow-up center is a strict transform of an admissible rank stratum, or of the corresponding admissible rank stratum in a verified recursive subchain. Non-admissible rank vectors are empty rank conditions, and coordinate pivot boundaries are either outside the chart or belong to lower-rank admissible strata covered by other branches.

Thus the only divisor types are:

- stratum-divisors, with ratio `Mval(t)/2 >= m0/2`;
- terminal residual smooth-block cone-divisors, with ratio `n_block/2 = Mval(t_leaf)/2 >= m0/2`.

If an implementation inserted extra auxiliary blow-ups not identified with admissible rank strata or terminal smooth blocks, that would be a proof gap. Under the stated flag-resolution, it does not occur.

**G3.5(iii) Verdict: SOUND.**

Pick any admissible achiever `t*` with `Mval(t*) = m0`. By G3.4, some branch reaches `S(t*)`. The blow-up of that stratum gives `(k,h)=(1,m0-1)`, hence ratio

`(h+1)/(2k) = m0/2`.

By (i) and (ii), no other divisor has smaller ratio. Therefore the chart monomial threshold equals exactly

`(1/2) min_Adm Mval`.

For `(3,3,3)`, both `S(1,0)` and `S(2,0)` attain `Mval=7`, so both give binding ratio `7/2`.

This chart-value match is a resolution-plus-`Mval` fact once cover exhaustiveness, center classification, and the residual-block inequality are proved. The separate A1/Aoyagi arithmetic is not needed for that chart computation, though it is an independent confirmation of the same RLCT closed form.