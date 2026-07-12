## Q1

(a) **FORCED:** `tailProd_width2` makes every width-2 tail exactly \(I_{M_1}\). Hence the rank-deficient `diag(1,0)` tail is excluded.

(b) **FORCED:** \(I I^\top-1I=0\), and `Matrix.PosSemidef.zero` supplies the required PSD proof. With `minAdm > 0` and `hdim`, `corankLeaf_rpow_lt_top` applies below \(aM_1/2\).

(c) **INFERRED:** the branch is satisfiable; for example \(M=(1,1)\), \(a=1\), coordinate residuals, \(d=1\), uniform support \(1\), and `jac=1` satisfy genuine carrier, β, and tied γ′. Thus the tie only forces the correct identity tail, not vacuity.

(d) The measurable isomorphisms alone do not force dimension equality. However, provenance and residual linearity make their composite a linear bijection \(\mathbb R^{M_0M_1}\simeq\mathbb R^{aM_1}\), so `LinearEquiv.finrank_eq` gives \(a=M_0\) when \(M_1>0\); thus \(a>M_0\) is unsatisfiable but harmless, and #4 remains valid using the actual \(a\).

SOUND

## Q2

(a) **FORCED:** `witnessDecoration222_faithful` explicitly inhabits the tied γ′ clause with the varying genuine tail product. This suffices to refute clause-local mid-recursion vacuity, though it does not itself prove full `adm`.

(b) **INFERRED:** there is no incompatibility. Take `e := (eFront M).symm`; `measurePreserving_eFront` supplies MP, `eFront_preimage_box` gives the domain equality, and `prod_front_peel` gives `prod M (e z) = z.1 · prod (dropHead M) z.2`. The missing `genuineCarrier` theorem is therefore a formalization omission, not a mathematical obstruction.

SUFFICIENT