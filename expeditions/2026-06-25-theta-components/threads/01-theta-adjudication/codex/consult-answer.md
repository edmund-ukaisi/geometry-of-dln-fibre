**VERDICT**

- [fact] `theta_geom` counts QIP minimizers/top-dimensional irreducible components; LR states this directly in the QIP theorem. [main.tex](/home/ubuntu/workspace/geometry-of-dln-fibre/paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex:1155)
- [fact] Aoyagi’s `theta` is the pole order, equivalently `max Card{j : (h_j+1)/(2k_j)=lambda}`. [aoyagi-2023-extracted-text.txt](/home/ubuntu/workspace/geometry-of-dln-fibre/theory/aoyagi-2023-reproduction/aoyagi-2023-extracted-text.txt:238)
- [inference] They are genuinely different invariants; the SLT order counts how many minimal-ratio exceptional divisors meet in a resolution chart, not how many top-dimensional components the original fibre has.
- [fact] For `(2,2,2,2,2)`, `m=4`, `S=10`, `delta=10-4*3=-2`, so `theta_geom = binom(4,2)=6`.
- [fact] Exact QIP enumeration: `G(e)=sum_{j<=i} e_i e_j` over the 10 compositions of `2` into 4 parts; the six two-support vectors have `G=3`, and the four doubled vectors have `G=4`.
- [fact] Therefore the component/QIP count is `6`, not `5`.
- [fact] Aoyagi’s closed form gives `M=ceil(10/4)=3`, `a=10-(3-1)4=2`, hence `theta_order=2(4-2)+1=5`.
- [inference] Thus `5` is a pole-order count if Aoyagi’s resolution computation is accepted; it is not the count of top-dimensional components.

**MECHANISM**

- [fact] With `b=S mod m`, `|delta|=min(b,m-b)`, and Aoyagi’s formula becomes `theta_order = b(m-b)+1 = |delta|(m-|delta|)+1`.
- [fact] The Voronoi/QIP count is `theta_geom = binom(m, |delta|)`: choose which `|delta|` active coordinates get the rounding correction.
- [inference] Aoyagi’s `a(ell-a)+1` enumerates minimal-ratio resolution directions: an `a x (ell-a)` crossing count plus one base direction.
- [inference] The agreement at `|delta|<=1` is the small-binomial identity `binom(m,0)=1` and `binom(m,1)=m=(m-1)+1`, not a general structural equality.
- [fact] For `|delta|>=2`, `binom(m,|delta|) > |delta|(m-|delta|)+1`, so Aoyagi’s number undercounts components if misread as a component count.

**RISK**

- [inference] The main risk is a `+1` convention/transcription issue for pole multiplicity: pole order versus the `log log n` exponent/order-minus-one. This does not affect the exact QIP count `6`.

**ONE-LINE REGION**

- [fact] Agreement iff `|delta| <= 1`, equivalently `S mod m in {0,1,m-1}`.