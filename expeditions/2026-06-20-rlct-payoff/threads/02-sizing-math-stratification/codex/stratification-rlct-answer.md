**Q1**

Let `X_M := closure(O_M) = orbitRankLocus M`, ordered by rank patterns:  
`X_S ⊆ X_R` iff `rankPattern(S) ≤ rankPattern(R)` entrywise.

Precise stratification:

`Σ^r_d = ⋃_{M : m_{0N}=r} O_M`.

Proof: orbits partition `Rep_d`, and the product rank is exactly the corner multiplicity `m_{0N}`.

Also:

`Σbar^r_d = {rank(mult) ≤ r} = ⋃_{M : m_{0N}≤r} X_M`.

Proof: if `m_{0N}≤r`, then every point of `X_M` has corner rank `≤ m_{0N}≤r`, since `X_M` is the determinantal rank locus bounded by `M`’s rank pattern. Conversely, any point of `Σbar^r` lies in some orbit `O_S` with `s_{0N}≤r`, hence lies in `X_S`.

Components are indexed by **maximal**, not minimal, rank patterns. More precisely, the irreducible components of the exact rank stratum are the dense open pieces

`X_M ∩ Σ^r_d`

where `M` is maximal, under entrywise rank-pattern order, among Kostant partitions with `m_{0N}=r`. Their closures in `Rep_d` are the corresponding `X_M`.

For the closed locus `Σbar^r`, components are the `X_M` maximal among `m_{0N}≤r`. These agree with the previous list once one knows the rank-raising/density fact: every maximal component of `Σbar^r` meets `Σ^r`, equivalently no component is trapped in `Σbar^{r-1}`. If not assumed, this is the subtle point.

`θ = numTop d r`: yes, for top-dimensional components of `Σ^r`.

Load-bearing lemma: if `X_M ⊊ X_L` are irreducible orbit closures inside `Rep_d`, then  
`codim X_L < codim X_M`.

Proof: proper inclusion of irreducible closed subsets strictly raises dimension. Since geometric codimension equals `codimForm`, strict containment strictly lowers `codimForm`.

Therefore, if a corner-`r` orbit closure has minimal codimension among all corner-`r` orbits, it cannot be contained in a larger corner-`r` orbit closure. Hence it is maximal, so it gives a component. Non-components are contained in larger corner-`r` closures and have strictly larger codimension. Thus the number of top-dimensional components equals the min-codim count `numTop d r`.

**Q2**

(a) The cited analytic input is Aoyagi’s DLN RLCT theorem: for the squared Frobenius loss

`K^DLN_B(A) = ||mult(A)-B||^2`

with `rank B = r`, the RLCT equals the explicit DLN value, namely half of the same minimised codimension invariant appearing geometrically.

What Aoyagi supplies is the **analytic lower bound/equality**, not the algebraic geometry of the fibre. The general Atiyah/Bernstein inequality only gives

`rlct(K^DLN_B) ≤ codim(mult^{-1}(B))/2`.

Our contribution is the geometric identification

`codim(mult^{-1}(B)) = cCodim d r`

or the corresponding min over Voigt/orbit-closure codimensions. Substituting this codimension into Aoyagi’s analytic formula gives the paper’s equality.

Subtlety: Aoyagi does not prove the orbit-closure/codimension computation; it proves that the analytic RLCT lands on that number.

(b) No general reason to expect

`rlcm(K^DLN_B) = θ`.

`θ` counts top-dimensional irreducible components of the fibre or rank locus. `rlcm` is the order of the largest pole of the local/global zeta function; it is controlled by the worst local normal-crossing/exceptional-divisor configuration after resolution.

Multiple top-dimensional components usually add residues, not pole orders. For disjoint smooth components, the pole order stays `1`, while `θ` can be larger. Conversely, a single singular component can produce higher pole order. Under products/sums, RLCT multiplicities obey analytic rules such as “sum gives multiplicities adding minus one” in independent variables, which is not how irreducible component counts behave.

So equality may occur in special DLN cases, but it is not a consequence of the component count or codimension theorem. It would need a separate analytic/resolution theorem.