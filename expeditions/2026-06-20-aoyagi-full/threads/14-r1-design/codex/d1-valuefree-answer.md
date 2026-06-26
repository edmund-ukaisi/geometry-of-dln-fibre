VALUE-FREE, conditional on the stated normal-form and strata-coverage facts; no use of R1’s core RLCT value.

**Aoyagi Thm 2 Proof**
Let `K(w)=Σ_i f_i(w)^2`, with each `f_i` homogeneous of degree `n_i>0`, and let `a` be another zero of `K`.

1. Choose the blow-up/radial chart `w=t(a+u)` over the direction `a`.
   Label: PURE-ALGEBRA / CHANGE-OF-VARIABLES.

2. Homogeneity gives
   `f_i(t(a+u)) = t^{n_i} f_i(a+u)`, hence
   `K(t(a+u)) = Σ_i |t|^{2n_i} f_i(a+u)^2`.
   Label: PURE-ALGEBRA.

3. For `|t|<1`,
   `Σ_i |t|^{2n_i} f_i(a+u)^2 <= Σ_i f_i(a+u)^2 = K(a+u)`.
   Label: PURE-ALGEBRA.

4. Apply same-point monotonicity in the common blow-up chart, with the same Jacobian density on both sides:
   the scaled pullback has RLCT no larger than the unscaled germ.
   Label: SAME-POINT-MONOTONICITY.

5. By blow-up/change-of-variables, the scaled pullback is a local contribution to the RLCT at the deepest point `0`; the unscaled germ is just the germ at `a`, with an extra harmless `t` variable/Jacobian factor.
   Thus `lambda_0(K) <= lambda_a(K)`.
   Label: CHANGE-OF-VARIABLES.

6. No admissible-tree minimum, monomial-threshold formula, or closed-form RLCT computation appears.
   Label: USES-VALUE: none.

FACT: this is exactly a comparison argument. It uses homogeneity to create an inequality and monotonicity to turn that inequality into an RLCT inequality. It does not compute either side.

**Answer To (B)**
FACT: at a non-deepest fibre point `v`, the translated generators generally are not homogeneous; the nonzero linear leading part reflects regular/smooth directions.

The reduction is: take the Jacobian rank of the generator map at `v`, use a local constant-rank/implicit-function/Morse-with-parameters split, and put the loss germ into

`Q(x) + K_res(y)`

where `Q(x)=x_1^2+...+x_q^2` is the nondegenerate quadratic block and `K_res` is the remaining homogeneous residual core. The regular variables are the linear directions; after solving/removing them, the residual generators are again multilinear/homogeneous in the unresolved core variables.

This does not require R1. It uses local analytic coordinate changes, Jacobian rank, and the algebraic homogeneity of the residual product. The only elementary numerical contribution is `q/2` from the regular quadratic block; that is not the R1 core value.

**Answer To (C)**
The “cover all fibre strata and place a deepest point in each stratum’s specialization closure” obligation is value-free.

It is a fibre-stratification statement: classify rank patterns, choose block/rank normal forms, show every fibre point lies in one such chart, and show surplus-rank data can be specialized/degenerately scaled to the minimal-rank `r` configuration. That is linear algebra/algebraic geometry of the fibre, not a resolution-value computation.

If this coverage/specialization statement is missing, D1 has a structural gap. But the missing ingredient is not R1.

**Clean Decomposition Of D1>=**
For each fibre point `v`:

1. Use local analytic changes to reduce the germ at `v` to a regular block plus homogeneous residual core.
2. Regular directions contribute `q/2 >= 0`.
3. Use Aoyagi’s homogeneous scaling comparison on the residual/core model to compare the deepest specialization with the point represented by `v`.
4. Use S1 to transport the comparison back to the original loss germ.
5. Conclude `lambda_deepest(F) <= lambda_v(F)`.

INFERENCE: assuming the normal-form and strata-coverage hypotheses are established, D1>= is independent of R1. R1 is only needed later to compute the actual closed-form value of the deepest/core RLCT.