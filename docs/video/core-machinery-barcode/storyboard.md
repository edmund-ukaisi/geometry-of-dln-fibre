# Storyboard: The Core Machinery as a Barcode

Target: one silent 8-10 minute visual-first lesson for a mathematically mature
graduate reader.

## 1. Opening Motif

On screen: a matrix chain fades in.

Caption:

> A chain of matrices hides a finite barcode.

Visual purpose: set the recurring motif. The chain is not just a product; it is
a transport system for directions.

## 2. The Multiplication Map

On screen:

$$
k^{d_0} \xrightarrow{A_1} k^{d_1} \xrightarrow{A_2}
\cdots \xrightarrow{A_N} k^{d_N}
$$

Then:

$$
\operatorname{mult}(A_\ast)=A_N\cdots A_1.
$$

Caption:

> The multiplication map keeps the endpoint map and forgets the interior.

Visual purpose: make the map concrete before introducing quivers or orbits.

## 3. Rank Pattern

On screen: curved interval arrows appear above the chain, then an upper
triangular table.

$$
r_{ij}=\operatorname{rank}(A_j\cdots A_{i+1}), \qquad r_{ii}=d_i.
$$

Caption:

> The corner rank is only one measurement. The rank pattern records every
> interval.

Visual purpose: shift attention from the full product to all interval
compositions.

## 4. Base Change

On screen: each vector space gets a change-of-basis label \(P_i\). The interval
composition telescopes:

$$
(P\cdot A)_j\cdots(P\cdot A)_{i+1}
=P_j(A_j\cdots A_{i+1})P_i^{-1}.
$$

Caption:

> Base change relabels coordinates. Interval ranks do not change.

Visual purpose: explain why rank patterns are orbit invariants.

## 5. One Interval Module

On screen: a single horizontal bar born at vertex \(i\), alive through \(j\),
dead outside.

$$
M_{ij}: \quad 0 \to \cdots \to k \xrightarrow{1} \cdots
\xrightarrow{1} k \to 0 \to \cdots
$$

Caption:

> An interval module is one direction that survives exactly across one block.

Visual purpose: give the atomic visual object.

## 6. Gabriel Decomposition

On screen: several bars stack into a barcode.

$$
A_\ast \cong \bigoplus_{i\le j} M_{ij}^{m_{ij}}.
$$

Caption:

> Gabriel's theorem says every chain is a direct sum of these bars.

Visual purpose: present the classification object.

## 7. Ranks Count Bars

On screen: bracket an interval \([i,j]\) under the barcode and highlight every
bar containing it.

$$
r_{ij}=\sum_{a\le i,\ b\ge j} m_{ab}.
$$

Caption:

> The rank across \([i,j]\) is the number of bars that cover \([i,j]\).

Visual purpose: make the cumulative transform visually obvious.

## 8. Inclusion-Exclusion

On screen: a four-term stencil isolates one exact bar multiplicity.

$$
m_{ij}=r_{ij}-r_{i,j+1}-r_{i-1,j}+r_{i-1,j+1}.
$$

Caption:

> Inclusion-exclusion turns survival counts back into exact bar counts.

Visual purpose: show uniqueness of the barcode from the rank pattern.

## 9. The Running Example \((2,2,2)\)

On screen:

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix}, \qquad
B=\begin{pmatrix}0&0\\0&1\end{pmatrix}.
$$

Threads:

- \(e_2^{(0)}\) dies immediately: \([0,0]\).
- \(e_1^{(0)}\) survives to vertex 1: \([0,1]\).
- \(e_2^{(1)}\) survives to vertex 2: \([1,2]\).
- \(e_1^{(2)}\) is born at vertex 2: \([2,2]\).

Rank table:

$$
\begin{pmatrix}
2&1&0\\
 &2&1\\
 & &2
\end{pmatrix}.
$$

Caption:

> The product is zero because no bar survives from 0 all the way to 2.

Visual purpose: tie every abstract object to the core example.

## 10. Six Orbits and the Closing Slogan

On screen: six points labelled by \((r_{01},r_{12})\), all with \(r_{02}=0\).

Caption:

> For fixed dimensions, orbits, rank patterns, and barcodes are equivalent
> finite data.

Closing formula:

$$
\text{orbits}
\Longleftrightarrow
\text{rank patterns}
\Longleftrightarrow
\text{barcodes}.
$$
