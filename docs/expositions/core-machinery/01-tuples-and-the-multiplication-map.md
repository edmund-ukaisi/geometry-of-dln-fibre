---
title: "Composable Matrix Tuples and the Multiplication Map"
status: draft
source: exposition
topics: [core-machinery, matrix-tuples, multiplication-map, rank-loci]
created: "2026-06-14"
updated: "2026-06-14"
---

# Composable Matrix Tuples and the Multiplication Map

This is the first chapter of a self-contained development of one piece of
linear algebra: how a chain of linear maps composes, and what the set of chains
with a prescribed composite looks like as a geometric object. The composite of
a chain is a single matrix, so the question "which chains have a given
composite?" is a question about the fibers of one polynomial map between affine
spaces. These fibers have a rigid, finite combinatorial structure, and these
chapters build the machinery that exposes it.

We work over an arbitrary field $k$; nothing here needs $k$ to be $\mathbb R$ or
$\mathbb C$. The geometric and analytic payoffs that motivate the study — the
codimension of these fibers and, through it, a learning-theoretic invariant of
deep linear networks — appear in later chapters and are not used here.

The development runs in five chapters:

1. the objects: tuples of composable matrices, the multiplication map, and the
   loci it defines (this chapter);
2. the reinterpretation of a tuple as a representation of a quiver, the
   change-of-basis group, and its orbits;
3. Gabriel's theorem in this case: every tuple decomposes uniquely into simple
   interval pieces;
4. two ways to record a tuple up to change of basis — its rank pattern and its
   Kostant partition — and the inclusion–exclusion formula relating them;
5. the classification: the rank pattern is a complete invariant, which makes
   orbits, isomorphism classes, and Kostant partitions the same data.

## 1.1 The space of composable tuples

We first fix the shapes of the matrices in our chains.

!!! definition "Definition 1.1 — Dimension vector and the space of tuples"
    A **dimension vector** is a tuple of nonnegative integers

    $$
    \underline d = (d_0, d_1, \ldots, d_N).
    $$

    Write $\operatorname{Mat}_{a,b}(k)$ for the space of $a \times b$ matrices
    over $k$, identified with the linear maps $k^{b} \to k^{a}$. The **space of
    composable tuples** with dimension vector $\underline d$ is the product

    $$
    \operatorname{Rep}_{\underline d}
    = \prod_{i=1}^{N} \operatorname{Mat}_{d_i, d_{i-1}}(k).
    $$

    We write $A_\ast = (A_1, \ldots, A_N)$ for a point of
    $\operatorname{Rep}_{\underline d}$ and call it a **tuple**; its $i$-th entry
    is a matrix $A_i \colon k^{d_{i-1}} \to k^{d_i}$. The subscript $\ast$ is a
    reminder that $A_\ast$ denotes the whole list, not a single matrix.

The word "composable" records the only constraint: the target dimension of
$A_i$ matches the source dimension of $A_{i+1}$, so the maps line up into a
chain

$$
k^{d_0} \xrightarrow{\ A_1\ } k^{d_1}
\xrightarrow{\ A_2\ } \cdots
\xrightarrow{\ A_N\ } k^{d_N}.
$$

As a variety, $\operatorname{Rep}_{\underline d}$ is an affine space of dimension
$\sum_{i=1}^N d_i d_{i-1}$, with one coordinate per matrix entry. On its own it
carries no further structure; the questions of this chapter concern the
multiplication map defined on it in §1.2 and the subsets defined by rank
conditions on that map in §1.3.

??? info "Formalised in Lean — Core.Setup.Tuple"

    ```
    abbrev Tuple (d : Fin (N + 1) → ℕ) : Type u :=
      ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k
    ```

    A tuple is the dependent function $i \mapsto A_i$. The $N+1$ vertices
    $0,\ldots,N$ are indexed by `Fin (N+1)` (the argument `d`) and the $N$ maps
    by `Fin N`. The map at index $i$ runs from vertex `i.castSucc` (numerically
    $i$) to vertex `i.succ` (numerically $i+1$), so in the paper's $1$-based
    naming it is $A_{i+1} \colon k^{d_i} \to k^{d_{i+1}}$; its Lean type is
    `Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`.

## 1.2 The multiplication map

The chain has a composite, and reading off that composite is the map we study.

!!! definition "Definition 1.2 — The multiplication map"
    The **multiplication map** for dimension vector $\underline d$ is

    $$
    \operatorname{mult} \colon \operatorname{Rep}_{\underline d}
    \longrightarrow \operatorname{Mat}_{d_N, d_0}(k),
    \qquad
    \operatorname{mult}(A_\ast) = A_N A_{N-1} \cdots A_1.
    $$

    It sends a tuple to the single linear map $k^{d_0} \to k^{d_N}$ obtained by
    composing the whole chain.

Each entry of the product matrix is a polynomial in the entries of the $A_i$, so
$\operatorname{mult}$ is a morphism of affine spaces. For $0 \le i \le j \le N$,
the **interval composition** $A_j A_{j-1} \cdots A_{i+1}$ is the map from vertex
$i$ to vertex $j$ (the empty product, equal to the identity, when $i = j$); the
full composite is the case $i = 0$, $j = N$. We record two facts about
$\operatorname{mult}$.

1. **The composite is the longest interval composition.** Its rank, together
   with the ranks of all the shorter interval compositions, measures how much
   the chain collapses between each pair of vertices. These ranks are a complete
   record of a tuple up to change of basis, and extracting $(C, \theta)$ from
   them is the work of the later chapters.
2. **The multiplication map is far from injective.** It imposes $d_N d_0$
   polynomial equations on a tuple with $\sum_{i=1}^N d_i d_{i-1}$ coordinates,
   so its nonempty fibers are positive-dimensional. The shape of these fibers is
   the object of study.

??? info "Formalised in Lean — Core.Setup.mult"

    ```
    def mult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
        Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k :=
      multPrefix d A (Fin.last N)
    ```

    `mult` is the composite $A_N \cdots A_1$, assembled from the prefix products
    `multPrefix`. The interval compositions $A_j \cdots A_{i+1}$ are
    `Core.Submult.submult i j`, and the two agree at the top:

    ```
    theorem mult_eq_submult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
        mult d A = submult d A 0 (Fin.last N) (Fin.zero_le _)
    ```

## 1.3 The loci we study

We now define subsets of $\operatorname{Rep}_{\underline d}$ by imposing
conditions on the composite $\operatorname{mult}(A_\ast)$.

!!! definition "Definition 1.3 — Product-rank loci and fibers"
    Fix $0 \le r \le \min_i d_i$ and a matrix
    $B \in \operatorname{Mat}_{d_N, d_0}(k)$. The **product-rank-$r$ locus** and
    the **product-rank-$\le r$ locus** are

    $$
    \Sigma^{r}_{\underline d}
    = \{\, A_\ast : \operatorname{rank}(A_N \cdots A_1) = r \,\},
    \qquad
    \overline{\Sigma}^{\,r}_{\underline d}
    = \{\, A_\ast : \operatorname{rank}(A_N \cdots A_1) \le r \,\},
    $$

    and the **fiber** over $B$ is

    $$
    \operatorname{mult}^{-1}(B)
    = \{\, A_\ast : A_N \cdots A_1 = B \,\}.
    $$

The locus $\overline{\Sigma}^{\,r}_{\underline d}$ is Zariski **closed** and
contains $\Sigma^{r}_{\underline d}$; indeed $\Sigma^{r}_{\underline d}$ is open
in it, being the complement of the smaller closed locus
$\overline{\Sigma}^{\,r-1}_{\underline d}$. The closure bar follows the paper's
usage: for $r \le \min_i d_i$ the set $\Sigma^{r}_{\underline d}$ is also dense
in $\overline{\Sigma}^{\,r}_{\underline d}$, so the latter is genuinely the
Zariski closure of the former. That density — every rank-$\le r$ tuple is a
limit of rank-exactly-$r$ tuples — uses the orbit-closure order (Theorem 3.8 of
the paper) and is not part of the elementary closed-ness; we take it from the
paper. The closed-ness itself, and the precise sense in which rank can only drop
in the limit, are elementary.

??? proof "Why $\overline{\Sigma}^{\,r}_{\underline d}$ is closed: rank drops in the limit, never jumps"
    The product $\operatorname{mult}(A_\ast) = A_N \cdots A_1$ is a
    $d_N \times d_0$ matrix whose entries are polynomials in the entries of
    $A_\ast$. For any matrix $M$ and any $s$, the condition
    $\operatorname{rank} M \ge s$ holds exactly when some $s \times s$ minor of
    $M$ is nonzero, and each minor is a polynomial in the entries of $M$.
    Composing, each $s \times s$ minor of $\operatorname{mult}(A_\ast)$ is a
    polynomial in the entries of $A_\ast$. Hence

    $$
    \{\, A_\ast : \operatorname{rank} \operatorname{mult}(A_\ast) \ge s \,\}
    $$

    is the locus where at least one of these finitely many polynomials is
    nonzero — a Zariski **open** set. Its complement
    $\{\operatorname{rank} \le s-1\}$ is therefore Zariski closed; taking
    $s = r+1$ gives the claim for $\overline{\Sigma}^{\,r}_{\underline d}$.

    The same minors explain why rank can only drop in the limit. Suppose a
    family $A_\ast(t)$ approaches $A_\ast(0)$ and has
    $\operatorname{rank} \operatorname{mult}(A_\ast(t)) = \rho$ for all $t \ne 0$
    near $0$. If the limit had rank $\ge \rho + 1$, some
    $(\rho{+}1) \times (\rho{+}1)$ minor would be nonzero at $t = 0$; being a
    continuous function of $t$, it would stay nonzero for small $t \ne 0$,
    forcing $\operatorname{rank} \ge \rho+1$ there too — against
    $\operatorname{rank} = \rho$. So the limit has rank $\le \rho$: a limit can
    lose rank but never gain it. This is why rank-$\le r$ is a closed condition
    and rank-$= r$ is only locally closed.

The most basic case is $r = 0$: the **zero-product locus**
$\Sigma^0_{\underline d} = \{A_\ast : A_N \cdots A_1 = 0\}$, which already equals
$\overline{\Sigma}^{\,0}_{\underline d}$ (rank $\le 0$ means rank $0$) and is the
fiber over $B = 0$.

The two numbers these chapters are built to compute are attached to these loci.

!!! definition "Definition 1.4 — The top invariants $C$ and $\theta$"
    For a locus that is a finite union of irreducible varieties, let $C$ be the
    smallest codimension occurring among its irreducible components — the
    codimension of the **top-dimensional** components — and let $\theta$ be the
    number of components of that smallest codimension.

Computing $(C, \theta)$ for $\overline{\Sigma}^{\,r}_{\underline d}$ and for
$\operatorname{mult}^{-1}(B)$ is the destination of the later chapters; this
chapter does not compute them. What these chapters supply first is the structure
that makes $(C,\theta)$ computable: a decomposition of
$\operatorname{Rep}_{\underline d}$ into finitely many change-of-basis orbits, on
which the product rank is constant and orbit codimension is a combinatorial
quantity.

??? info "Formalised in Lean — Core.Setup loci"

    ```
    def productRankLocus (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
      {A | (mult d A).rank = r}

    def productRankLocusLE (d : Fin (N + 1) → ℕ) (r : ℕ) : Set (Tuple (k := k) d) :=
      {A | (mult d A).rank ≤ r}

    def fibre (d : Fin (N + 1) → ℕ)
        (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Set (Tuple (k := k) d) :=
      {A | mult d A = B}
    ```

    `productRankLocus` is $\Sigma^r$, `productRankLocusLE` is
    $\overline{\Sigma}^{\,r}$, and `fibre` is $\operatorname{mult}^{-1}(B)$, as
    subsets of `Tuple d`. The invariants $C$ and $\theta$ are not yet
    formalised; they are named here only to fix the target.

## 1.4 Two examples

The smallest examples already show that these loci have several components, and
they are worth carrying through these chapters.

!!! example "Example 1.5 — Two scalar factors, $\underline d = (1,1,1)$"
    Here $N = 2$ and every matrix is a scalar, so
    $\operatorname{Rep}_{(1,1,1)} = k \times k$ with coordinates $(a_1, a_2)$
    and $\operatorname{mult}(a_1, a_2) = a_2 a_1$. The zero-product locus is

    $$
    \Sigma^0_{(1,1,1)} = \{\, (a_1,a_2) : a_2 a_1 = 0 \,\}
    = \{a_1 = 0\} \cup \{a_2 = 0\},
    $$

    the union of the two coordinate axes in $k^2$. It has two irreducible
    components, each of codimension $1$, so $C = 1$ and $\theta = 2$. Already in
    this case the zero-product locus is reducible, and neither component is
    contained in the other.

!!! example "Example 1.6 — Two square factors, $\underline d = (2,2,2)$"
    Here $N = 2$ and a point is a pair of $2\times 2$ matrices
    $k^2 \xrightarrow{A} k^2 \xrightarrow{B} k^2$, so
    $\operatorname{Rep}_{(2,2,2)} = k^8$ and the zero-product locus is
    $\Sigma^0_{(2,2,2)} = \{(A,B) : BA = 0\}$. It has three irreducible
    components (Example 4.3 of the paper):

    - $\{A = 0\}$, of codimension $4$;
    - $\{B = 0\}$, of codimension $4$;
    - $\{\det A = \det B = 0\ \text{and}\ BA = 0\}$, of codimension $3$.

    The top-dimensional part is the third component alone, so $C = 3$ and
    $\theta = 1$.

    ??? note "Why the third component is the largest"
        On the third component $A$ and $B$ are generically rank one. A rank-one
        $A$ has a line as image and a rank-one $B$ has a line as kernel, and
        $BA = 0$ says exactly that

        $$
        \operatorname{im}(A) \subseteq \ker(B),
        $$

        i.e. these two lines coincide. Choosing that common line, and then
        choosing rank-one maps $A$ with that image and $B$ with that kernel, is
        a family of dimension $5$ — larger than the two families $\{A=0\}$ and
        $\{B=0\}$ of dimension $4$. The condition $BA=0$ is therefore not a
        condition on one factor alone; it constrains how the image of $A$ sits
        inside the kernel of $B$, and the largest family is the one where both
        factors degenerate compatibly.

The contrast between the two examples is the point of these chapters: in the
scalar case "the product vanishes" means "one factor vanishes", but already for
$2\times 2$ matrices the dominant way to make a product vanish is for both
factors to degenerate so that an image lands in a kernel. Tracking this
incidence data by hand becomes hopeless as $N$ and the $d_i$ grow. The quiver
language of the next chapters is what makes it bookkeepable.

!!! question "Checkpoint"
    For $\underline d = (1,1,1,1)$ (three scalar factors $a_1,a_2,a_3$),
    describe $\Sigma^0$ and find $C$ and $\theta$.

??? tip "Solution"
    The composite is $a_3 a_2 a_1$, which vanishes iff some factor does, so

    $$
    \Sigma^0_{(1,1,1,1)} = \{a_1=0\} \cup \{a_2=0\} \cup \{a_3=0\},
    $$

    three coordinate hyperplanes in $k^3$. Each has codimension $1$, so $C=1$
    and $\theta = 3$. In general, for $\underline d = (1,\ldots,1)$ with $N$
    factors, $\Sigma^0$ is the union of the $N$ coordinate hyperplanes, with
    $C=1$ and $\theta = N$.

## Sources and cross-references

The objects of this chapter are those of Sections 1 and 4 of the paper, and of
Sections 1 and 4 of the [high-level overview](../paper-digest/high-level-overview.md),
where the same two examples appear and the invariants $C$ and $\theta$ are
placed in the context of the paper's main theorems. The formal counterparts live
in `DLNFibre.Core.Setup` (the objects) and `DLNFibre.Core.Submult` (the
multiplication map and its interval compositions).

The next chapter reinterprets a tuple $A_\ast$ as a representation of a quiver
and introduces the change-of-basis group whose orbits organize all of these
loci.
