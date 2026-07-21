\[
\boxed{\rho=\max_{\text{charts }C}\#\{\text{binding divisors present in }C\}.}
\]

Indeed, every point lies in some normal-crossing chart, so the binding divisors through it are among that chart’s coordinate hyperplanes. Conversely, all binding coordinate hyperplanes in a chart meet at its origin. Thus the maximum-over-points definition equals the maximum per-chart binding count.

The naive total ignores incidence. For \([3,3,1,1]\), the two minimizing profiles occur in incompatible charts: no point lies on both corresponding divisors. Hence naive \(=2\), while every chart contains at most one and \(\rho=1\).

The claimed
\[
\rho=a(\ell-a)+1
\]
is not derivable from the supplied structure. Its exact proof requires two additional facts about the recursion leaves:

- Upper bound: every leaf realizes at most \(a(\ell-a)+1\) mutually compatible minimizing profiles.
- Attainment: at least one leaf realizes exactly that many.

Neither follows from the number or values of the minimizing lattice profiles; in particular, total existence does not imply simultaneous realization. The calibration data are consistent with the formula but cannot prove either statement.

Therefore the formula is exact for the true pole multiplicity only if those two leaf-incidence claims are established. The most likely gap in a proof based merely on enumerating minimizers is attainment—assuming minimizing profiles coexist in one chart—although the upper bound also needs an explicit recursion argument.