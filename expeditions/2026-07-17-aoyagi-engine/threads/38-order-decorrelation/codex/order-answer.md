1. **Atom:** \(\boxed{B\circ S}\).

2. The blow-up substitution gives each parent block coordinate as \(d_{ij}=u\,d'_{ij}\), so \(B\) maps intermediate coordinates to parent coordinates and is outermost. The shear expresses each intermediate \(d'_{ij}\) in terms of child coordinates and shear parameters, so \(S\) maps child to intermediate and is innermost. Therefore
\[
\text{child}\xrightarrow{S}\text{intermediate}\xrightarrow{B}\text{parent},
\]
hence the atom is \(B\circ S\).

3. **YES.** Pulling back any parent block coordinate gives
\[
(B\circ S)^*(d_{ij})=u\,S^*(d'_{ij}),
\]
and \(S\) fixes \(u\), with \(S^*(d'_{ij})\) polynomial in the child/shear coordinates.

The other order need not give the same answer: applying the shear outside the blow-up can introduce terms not uniformly multiplied by \(u\), so divisibility of every parent-frame block coordinate is not guaranteed.