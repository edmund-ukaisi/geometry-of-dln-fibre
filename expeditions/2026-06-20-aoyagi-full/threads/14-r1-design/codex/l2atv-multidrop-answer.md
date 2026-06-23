**Q1.** [FACT] The derivative image is  
\[
\operatorname{im} dP=\sum_s \operatorname{Im}(C_L\cdots C_{s+1})\otimes \operatorname{Row}(C_{s-1}\cdots C_1).
\]
The suffix images form an increasing flag in the output, and the prefix row-spaces form a decreasing flag in the input dual. [FACT] In bases adapted to these two flags, this is a Ferrers-type union of rectangles, not an arbitrary coupled matrix. Multi-drop layers can contribute to the same output coordinate, but they contribute through different layer variables. [INFERENCE] Choose one layer variable as pivot for each rectangle coordinate and put duplicate contributors into kernel/core coordinates. That gives triangular Gaussian elimination with unit pivots after row/variable changes. No forced shared-pivot obstruction appears.

**Q2.** [FACT] A downstream drop can make the larger upstream rank block singular if one insists on pivoting on the whole earlier high-rank block. That is the wrong block. [FACT] The actual regular pivot at layer \(s\) only uses the suffix-surviving subspace \(\operatorname{Im}(C_L\cdots C_{s+1})\) and the prefix-surviving row space of \(C_{s-1}\cdots C_1\). On those chosen rank subblocks, bases may be chosen so the relevant minors are identity, hence units. [INFERENCE] Later drops shrink the available rectangle; they do not turn a selected surviving pivot into a zero pivot.

**Q3.** [FACT] Because the derivative image is built from two monotone flags, adding another drop only adds or removes boundary rectangles in the same Ferrers diagram. [INFERENCE] The multi-drop case is therefore a serialization of single-drop peels, provided the peel is phrased on the current surviving suffix/prefix rectangle, not on the raw pre-drop rank. Overlaps between layers are kernel directions of \(dP\), handled by Schur-complement/Gaussian elimination, not irreducible coupling.

**Q4.** [INFERENCE] I do not see a smallest breaking \(T_v\). The only false version is the naive one: “highest-rank layer pivots on its full high-rank block.” That fails whenever a later drop kills part of that block, but those killed coordinates are not regular directions of \(dP\). [FACT] For the L2 split, the regular directions are exactly the rank-\(dP\) flag-rectangle directions, and these admit unit pivots in adapted bases.

VERDICT: WITNESS (serializes triangular-unit at all \(T_v\))