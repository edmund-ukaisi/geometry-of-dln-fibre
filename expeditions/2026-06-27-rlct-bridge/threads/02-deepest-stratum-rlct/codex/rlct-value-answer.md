lambda = 3/2; pole multiplicity m = 4.

**Method**

I used a rank/SVD blow-up followed by a toric Newton calculation on the resolved angular model.

Write each matrix as `A_i = rho_i U_i`, with `||U_i||_F = 1`. Then

`K = (rho_1 rho_2 rho_3 rho_4)^2 H(U_1,U_2,U_3,U_4)`

and the radial measure contributes `rho_i^3 d rho_i`, giving radial threshold `2`. Since the angular threshold below is `3/2`, the radial variables do not determine the RLCT.

Near the deepest angular stratum, put

`D_i = diag(1,u_i)`,
`R_j ~ [[c_j, -1], [1, c_j]]`.

Then the relevant product is

`D4 R3 D3 R2 D2 R1 D1`.

After multiplying out and making analytic coordinate changes/unit rescalings, the entry ideal becomes

`J = < z r - c p,  a(c - z q),  d r,  a d q >`

in 7 singular angular variables. The Newton/toric LP for the unsquared entry ideal uses the monomial terms

`zr, cp, ac, azq, dr, adq`

and gives

`lct(J) = 3`.

Because `K` is a sum of squares of the entries, the RLCT is half of this:

`lambda = 3/2`.

The critical Newton face has dimension `3` in `7` variables, so the pole order is

`m = 7 - 3 = 4`.

**Newton Degeneracy**

The original polynomial `K` is Newton-degenerate. Its homogeneous Newton face is `K` itself, and `K` vanishes on the real torus: for example, choose nonzero-entry rank-one `A1,A2` with `A2 A1 = 0`, and choose nonzero-entry invertible `A3,A4`. Since `K` is a sum of squares, the gradient also vanishes there. So the naive Newton/homogeneous value `2` is not tight.

**Cross-Check**

At a generic rank-one bottleneck, say `im(A1) = ker(A2)` with the other directions full rank, the angular loss is locally equivalent to three independent squares:

`u1^2 + u2^2 + c1^2`.

That gives `3/2`, matching the resolved computation. The 2-layer `2x2` product `A2 A1` has exactly this local model, so it is a useful smaller sanity check.

Confidence: high for `lambda = 3/2`; moderate for `m = 4`. The most likely way this is wrong is a missed binomial-cancellation chart in the angular ideal that changes the critical face multiplicity.