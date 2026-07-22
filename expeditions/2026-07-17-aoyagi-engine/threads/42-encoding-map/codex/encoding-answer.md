1. Certify that `enc` is well-defined, surjective, and an order-embedding:
\[
T\le T' \iff \operatorname{enc}(T)\le\operatorname{enc}(T').
\]
The reverse implication is load-bearing because it reflects order. A merely forward-monotone map may send incomparable \(T,T'\) to comparable diagrams—or even the same diagram—thereby inventing order relations absent from \(P\). Coordinate-sum encoding has exactly this defect: sums discard coordinate distribution, especially since covers need not increase the sum by one.

2. Birkhoff’s construction is canonical:
\[
T\longmapsto\{j\in J(P):j\le T\},
\]
giving \(P\cong\operatorname{Idl}(J(P))\). After identifying \(J(P)\) with the \(a\times(\ell-a)\) cell grid, these ideals are precisely `BoxPart(ℓ,a)`. The representation into \(\operatorname{Idl}(J(P))\) is canonical and unique. An isomorphism to the specifically labelled box is unique only after fixing that grid identification; abstractly, target automorphisms can produce alternatives (notably transpose when the box is square). Matching numerical invariants alone is insufficient; the join-irreducible/cover order must be verified.

3. A genuine loosening first breaks the element count: it admits additional profiles, so the domain no longer has \(\binom{\ell}{a}\) elements. Consequently no bijection—and hence no order-isomorphism—to `BoxPart` can exist. Such extra profiles may also cease to realize `minAdm`, but cardinality already obstructs the result. Thus the running-min cap is load-bearing.