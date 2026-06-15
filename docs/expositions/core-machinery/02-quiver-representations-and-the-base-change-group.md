---
title: "Quiver Representations and the Base-Change Group"
status: draft
source: exposition
topics: [core-machinery, quiver-representations, base-change-group, orbits, equivariance]
created: "2026-06-14"
updated: "2026-06-14"
---

# Quiver Representations and the Base-Change Group

[Chapter 1](01-tuples-and-the-multiplication-map.md) fixed a dimension vector
$\underline d = (d_0, \ldots, d_N)$, the space of composable tuples
$\operatorname{Rep}_{\underline d} = \prod_{i=1}^N \operatorname{Mat}_{d_i,
d_{i-1}}(k)$, and the multiplication map
$\operatorname{mult}(A_\ast) = A_N \cdots A_1$. A tuple
$A_\ast = (A_1, \ldots, A_N)$ is a chain

$$
k^{d_0} \xrightarrow{\ A_1\ } k^{d_1}
\xrightarrow{\ A_2\ } \cdots
\xrightarrow{\ A_N\ } k^{d_N}.
$$

This chapter introduces the right notion of "the same chain in different
coordinates" and shows that the product rank — indeed the rank of every interval
composition — depends only on the chain up to that equivalence. The equivalence
classes are the orbits of a group acting on $\operatorname{Rep}_{\underline d}$,
and the rank loci of Chapter 1 are unions of these orbits. The remaining chapters
show the orbits are finite in number and classify them.

## 2.1 The chain as a quiver representation

A choice of coordinates on each $k^{d_i}$ is incidental: the chain itself is a
diagram of vector spaces and linear maps. We name the diagram.

!!! definition "Definition 2.1 — The equioriented type-A quiver and its representations"
    The **equioriented type-A quiver** on $N+1$ vertices is the directed graph

    $$
    0 \longrightarrow 1 \longrightarrow \cdots \longrightarrow N,
    $$

    one arrow from each vertex to its successor. A **representation** of it
    assigns a $k$-vector space $V_i$ to each vertex $i$ and a linear map
    $f_i \colon V_{i-1} \to V_i$ to each arrow. A tuple $A_\ast$ is the
    representation with $V_i = k^{d_i}$ and $f_i = A_i$.

A representation carries no more data than the chain, but the word lets us speak
of maps *between* chains.

!!! definition "Definition 2.2 — Morphism and isomorphism of representations"
    A **morphism** $A_\ast \to A'_\ast$ between two representations with the same
    quiver is a family of linear maps $\varphi_i \colon V_i \to V'_i$, one per
    vertex, that commutes with the arrows: $\varphi_i \circ A_i = A'_i \circ
    \varphi_{i-1}$ for every $i$. It is an **isomorphism** when every $\varphi_i$
    is invertible.

An isomorphism is a change of basis at each vertex that carries one chain to the
other; the diagram

$$
\begin{array}{ccc}
k^{d_{i-1}} & \xrightarrow{\ A_i\ } & k^{d_i} \\[2pt]
\big\downarrow{\scriptstyle \varphi_{i-1}} & & \big\downarrow{\scriptstyle \varphi_i} \\[2pt]
k^{d_{i-1}} & \xrightarrow{\ A'_i\ } & k^{d_i}
\end{array}
$$

commutes. Isomorphic tuples are the same chain read in different coordinates.

## 2.2 The base-change group

Collecting one invertible map per vertex gives the group whose action realizes
"change of coordinates".

!!! definition "Definition 2.3 — The base-change group $G_{\underline d}$ and its action"
    The **base-change group** is the product of general linear groups, one per
    vertex,

    $$
    G_{\underline d} = \prod_{i=0}^{N} \operatorname{GL}_{d_i}(k).
    $$

    An element $P = (P_0, \ldots, P_N)$ acts on a tuple $A_\ast$ by changing
    basis at the source and target of each map:

    $$
    (P \cdot A_\ast)_i = P_i \, A_i \, P_{i-1}^{-1},
    \qquad i = 1, \ldots, N.
    $$

This is a group action: the identity tuple of matrices fixes every $A_\ast$, and
$(PQ) \cdot A_\ast = P \cdot (Q \cdot A_\ast)$, because the basis changes compose
vertex by vertex.

??? info "Formalised in Lean — Core.BaseChange"
    ```lean
    abbrev BaseChangeGroup (d : Fin (N + 1) → ℕ) : Type u :=
      ∀ v : Fin (N + 1), (Matrix (Fin (d v)) (Fin (d v)) k)ˣ

    def baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d) :
        Tuple (k := k) d :=
      fun i ↦ Units.val (P i.succ) * A i * Units.val ((P i.castSucc)⁻¹)

    instance : MulAction (BaseChangeGroup (k := k) d) (Tuple (k := k) d) where
      smul := baseChange
      one_smul := baseChange_one
      mul_smul := baseChange_mul
    ```

    `BaseChangeGroup d` is $G_{\underline d}$, a unit (invertible matrix) at each
    of the $N+1$ vertices. On edge $i$ (Lean's $0$-based index for the paper's
    $A_{i+1}$) the action conjugates by the target-vertex unit `P i.succ` on the
    left and the source-vertex unit inverse on the right, exactly
    $P_i A_i P_{i-1}^{-1}$. The `MulAction` instance is the group-action law.

The orbit of $A_\ast$ under $G_{\underline d}$ is the set of tuples reachable by
a base change. Comparing Definitions 2.2 and 2.3: a base change $P$ with
$P \cdot A_\ast = A'_\ast$ is the same data as an isomorphism $A_\ast \to
A'_\ast$ whose vertex maps are the $P_i$. So two tuples lie in the same
$G_{\underline d}$-orbit exactly when they are isomorphic as representations
(Theorem 2.4 of the paper); in this development that identification is built into
the definitions, and "orbit" and "isomorphism class" name the same partition of
$\operatorname{Rep}_{\underline d}$.

## 2.3 Rank is constant on orbits

The maps we care about are unchanged, as ranks, by base change.

!!! theorem "Orbit-invariance of interval ranks"
    For every base change $P \in G_{\underline d}$ and indices $i \le j$,

    $$
    \operatorname{rank}\big( (P \cdot A_\ast)_j \cdots (P \cdot A_\ast)_{i+1} \big)
    = \operatorname{rank}\big( A_j \cdots A_{i+1} \big).
    $$

    In particular, taking $i = 0$, $j = N$, the product rank
    $\operatorname{rank}\operatorname{mult}(A_\ast)$ is constant on
    $G_{\underline d}$-orbits.

The reason is that base change conjugates each interval composition by invertible
matrices, and conjugation by invertibles preserves rank.

??? proof "The interval composition conjugates; the inner units cancel"
    Write out the composition of a base-changed tuple from vertex $i$ to vertex
    $j$:

    $$
    (P \cdot A_\ast)_j \cdots (P \cdot A_\ast)_{i+1}
    = (P_j A_j P_{j-1}^{-1})(P_{j-1} A_{j-1} P_{j-2}^{-1}) \cdots
      (P_{i+1} A_{i+1} P_i^{-1}).
    $$

    Each interior pair $P_{m}^{-1} P_{m}$ cancels, leaving only the outermost
    units:

    $$
    (P \cdot A_\ast)_j \cdots (P \cdot A_\ast)_{i+1}
    = P_j \,(A_j \cdots A_{i+1})\, P_i^{-1}.
    $$

    Multiplying a matrix by an invertible matrix on either side does not change
    its rank, so the two interval compositions have equal rank. The full product
    rank is the case $i = 0$, $j = N$:
    $\operatorname{mult}(P \cdot A_\ast) = P_N \operatorname{mult}(A_\ast)
    P_0^{-1}$.

??? info "Formalised in Lean — Core.BaseChange"
    The telescoping identity (`submult_baseChange`) and its rank consequence
    (`rankPattern_baseChange`) are proved by induction on the upper index:

    ```lean
    theorem submult_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
        (i j : Fin (N + 1)) (hij : i ≤ j) :
        submult d (baseChange P A) i j hij
          = Units.val (P j) * submult d A i j hij * Units.val ((P i)⁻¹)

    theorem rankPattern_baseChange (P : BaseChangeGroup (k := k) d) (A : Tuple (k := k) d)
        (i j : Fin (N + 1)) (hij : i ≤ j) :
        rankPattern d (baseChange P A) i j hij = rankPattern d A i j hij
    ```

    Here `submult d A i j` is the interval composition $A_j \cdots A_{i+1}$ from
    Chapter 1; `rankPattern d A i j` is its rank, the array $r_{ij}$ treated in
    Chapter 4. The rank identity uses
    `Matrix.rank_mul_eq_left_of_isUnit_det` and its right-hand counterpart:
    multiplying by a unit-determinant matrix preserves rank.

## 2.4 The rank loci are unions of orbits

The product rank is constant on orbits, so a tuple's membership in a rank locus
depends only on its orbit.

!!! theorem "Local consequence — Rank loci are $G_{\underline d}$-stable"
    Each of the loci $\Sigma^r_{\underline d}$ and
    $\overline{\Sigma}^{\,r}_{\underline d}$ from Chapter 1 is a union of
    $G_{\underline d}$-orbits: if $A_\ast$ lies in one of them and
    $P \in G_{\underline d}$, then $P \cdot A_\ast$ lies in the same one.

This is the first structural gain. A rank locus, defined by a polynomial
condition on the product, is assembled from whole orbits. The fiber
$\operatorname{mult}^{-1}(B)$ is not itself orbit-stable — its definition fixes
the matrix $B$, not just its rank — but the equivariance
$\operatorname{mult}(P \cdot A_\ast) = P_N \operatorname{mult}(A_\ast) P_0^{-1}$
moves the fiber over $B$ to the fiber over $P_N B P_0^{-1}$, so the fibers over
matrices of a fixed rank are all base-change-equivalent.

What makes "union of orbits" useful is that the orbits are finite in number, so
the union is finite. That finiteness is the subject of the next chapter:
Gabriel's theorem decomposes every tuple into a finite list of elementary pieces,
and the number of orbits is the number of ways those pieces can occur.

!!! example "Example 2.6 — A base change of the $(2,2,2)$ rank-one tuple"
    Take $\underline d = (2,2,2)$ and the tuple

    $$
    A = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix},
    \qquad
    B = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix},
    $$

    so $BA = 0$ and $\operatorname{rank} A = \operatorname{rank} B = 1$. Apply the
    base change that is the identity at vertices $0$ and $2$ and
    $P_1 = \left(\begin{smallmatrix} 1 & 1 \\ 0 & 1 \end{smallmatrix}\right)$ at
    vertex $1$:

    $$
    A' = P_1 A = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix},
    \qquad
    B' = B P_1^{-1} = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}
      \begin{pmatrix} 1 & -1 \\ 0 & 1 \end{pmatrix}
      = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix}.
    $$

    The pair $(A', B')$ still satisfies $B'A' = 0$ with both factors of rank one,
    so it lies in the same rank locus $\Sigma^0_{(2,2,2)}$; the base change has
    moved within the orbit without changing any interval rank. This is the
    concrete $\operatorname{GL}_2(\mathbb Q)$ base change used as the
    non-vacuity witness for the classification in Chapter 5
    (`Core.Orbit.witnessBaseChangeQ`).

## Sources and cross-references

The quiver translation and the $G_{\underline d}$-action are Section 2 of the
paper and Section 2 of the [high-level overview](../paper-digest/high-level-overview.md);
orbit-invariance of rank is used throughout Section 3. The orbit/isomorphism
identification is Theorem 2.4 of the paper. The formal counterpart is
`DLNFibre.Core.BaseChange`.

The next chapter is Gabriel's theorem for this quiver: every tuple is a direct
sum of interval modules, which makes the orbit set finite and combinatorial.
