---
title: "Gabriel's Theorem: Interval Modules and the Barcode"
status: draft
source: exposition
topics: [core-machinery, gabriel-theorem, interval-modules, barcode, direct-sum]
created: "2026-06-14"
updated: "2026-06-14"
---

# Gabriel's Theorem: Interval Modules and the Barcode

[Chapter 2](02-quiver-representations-and-the-base-change-group.md) identified
the $G_{\underline d}$-orbits of $\operatorname{Rep}_{\underline d}$ with the
isomorphism classes of representations of the quiver
$0 \to 1 \to \cdots \to N$, and showed the rank loci are unions of orbits. For
that to be useful the orbits must be few. This chapter exhibits them: every
representation is a direct sum of one-dimensional "interval" pieces, so an
isomorphism class is recorded by how many of each piece occur — a finite list of
nonnegative integers. This is Gabriel's theorem for the equioriented type-A
quiver, and we phrase its decomposition as a **barcode**.

## 3.1 The interval modules

The elementary pieces are the representations that are one-dimensional on a
contiguous block of vertices and zero elsewhere, with the arrows acting as the
identity wherever both endpoints are present.

!!! definition "Definition 3.1 — The interval module $M_{ij}$"
    For $0 \le i \le j \le N$, the **interval module** $M_{ij}$ is the
    representation with vertex spaces

    $$
    (M_{ij})_l =
    \begin{cases} k & i \le l \le j, \\ 0 & \text{otherwise}, \end{cases}
    $$

    and arrow maps equal to the identity $k \to k$ on each edge whose endpoints
    both lie in $[i,j]$, and zero on every other edge. Its dimension vector is
    the indicator of the interval $[i,j]$.

So $M_{ij}$ is the chain

$$
0 \to \cdots \to 0 \to
\underset{i}{k} \xrightarrow{\,1\,} k \xrightarrow{\,1\,} \cdots
\xrightarrow{\,1\,} \underset{j}{k}
\to 0 \to \cdots \to 0,
$$

a single one-dimensional thread that is born at vertex $i$, carried forward
unchanged by the arrows, and dies after vertex $j$. The longest one, $M_{0N}$,
is one-dimensional at every vertex with identity maps throughout; the shortest,
$M_{ii}$, is a single $k$ at vertex $i$ with no nonzero arrow.

??? info "Formalised in Lean — Core.IntervalModule.intervalModule"

    ```
    def intervalDim (i j : Fin (N + 1)) (l : Fin (N + 1)) : ℕ :=
      if i ≤ l ∧ l ≤ j then 1 else 0

    def intervalActive (i j : Fin (N + 1)) (t : Fin N) : Prop :=
      i ≤ t.castSucc ∧ t.succ ≤ j

    def intervalModule (i j : Fin (N + 1)) : Tuple (k := k) (intervalDim i j) :=
      fun t _ _ ↦ if intervalActive i j t then (1 : k) else 0
    ```

    `intervalDim i j` is the indicator dimension vector ($1$ on $[i,j]$); an edge
    is `intervalActive` when both its endpoints lie in $[i,j]$, and there the
    edge map is the $1 \times 1$ identity. Off the interval the vertex space is
    $0$-dimensional, so the constant-$1$ formula typechecks uniformly.

## 3.2 Direct sums

Representations add by stacking, vertex by vertex.

!!! definition "Definition 3.2 — Direct sum of representations"
    The **direct sum** $A_\ast \oplus A'_\ast$ of two representations is the
    representation with vertex spaces $V_l \oplus V'_l$ and arrow maps the
    block-diagonal $A_i \oplus A'_i = \left(\begin{smallmatrix} A_i & 0 \\ 0 &
    A'_i \end{smallmatrix}\right)$.

Its dimension vector is the sum of the two dimension vectors. A finite direct sum
of interval modules, $\bigoplus_{(i,j)} M_{ij}^{\,m_{ij}}$ with each $M_{ij}$
repeated $m_{ij}$ times, is therefore a block-diagonal tuple, and its dimension
at vertex $l$ is $\sum_{i \le l \le j} m_{ij}$ — each interval covering $l$
contributing one.

??? info "Formalised in Lean — Core.IntervalModule"

    ```
    def dirSum {d d' : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) (B : Tuple (k := k) d') :
        Tuple (k := k) (fun l ↦ d l + d' l)

    noncomputable def intervalDirectSum :
        (L : List (Fin (N + 1) × Fin (N + 1))) → Tuple (k := k) (foldDim L)
      | [] => zeroTuple
      | p :: ps => dirSum (intervalModule p.1 p.2) (intervalDirectSum ps)
    ```

    `dirSum` places two tuples in block-diagonal position;
    `intervalDirectSum L` folds it over a list `L` of interval endpoints (the
    multiplicities are list multiplicities), giving
    $\bigoplus_{(a,b) \in L} M_{ab}$ over the dimension vector `foldDim L`.

## 3.3 Gabriel's theorem and the barcode

The interval modules are the only indecomposable representations of this quiver,
and every representation is built from them.

!!! theorem "Theorem 2.5 of the paper (Gabriel, equioriented type A) — existence"
    Every finite-dimensional representation of $0 \to 1 \to \cdots \to N$ is
    isomorphic to a direct sum of interval modules:

    $$
    A_\ast \;\cong\; \bigoplus_{0 \le i \le j \le N} M_{ij}^{\,m_{ij}}
    $$

    for some multiplicities $m_{ij} \in \mathbb N$. Equivalently, every tuple
    lies in the $G_{\underline d}$-orbit of such a block-diagonal tuple.

We record the decomposition as a **barcode**: the multiset of intervals $[i,j]$
that occur, with $M_{ij}$ contributing one bar $[i,j]$ per copy. A bar
$[i,j]$ is a one-dimensional thread alive on vertices $i$ through $j$; at each
vertex $l$ the threads alive there (the bars with $i \le l \le j$) form a basis
of $V_l$, and each arrow carries each alive thread to the next vertex or kills
it at the end of its bar. This is the picture behind the name: the representation
is a stack of horizontal bars, one per indecomposable summand.

The theorem has two halves. **Existence** — that a decomposition exists — is the
substantial geometric content and is what we prove here. **Uniqueness** — that
the multiplicities $m_{ij}$ are determined by $A_\ast$ — is deferred to
[Chapter 4](04-rank-patterns-and-kostant-partitions.md), where it falls out of
the rank pattern almost for free.

The existence proof peels one bar at a time.

??? proof "Peeling one bar per step (proof idea)"
    Work by induction on the total dimension $\sum_l \dim V_l$. If the
    representation is zero there is nothing to do. Otherwise choose a vertex
    where a thread can be started and follow it as far forward as the arrows
    allow, obtaining a single interval $[i,j]$ together with a line of vectors
    $v_i \in V_i, \ldots, v_j \in V_j$ with $A_l v_{l-1} = v_l$ along the
    interval and the thread dying after $j$. The span of this line is an interval
    submodule $M_{ij}$, and one shows it splits off as a direct summand: there is
    a complementary subrepresentation $W_\ast$ with
    $A_\ast \cong M_{ij} \oplus W_\ast$. The complement has strictly smaller
    total dimension, so the induction hypothesis decomposes it, and prepending
    the peeled bar gives a barcode for $A_\ast$.

    The work is in producing the complement at every vertex simultaneously and
    compatibly with the arrows — choosing, vertex by vertex, a complement to the
    peeled line that the maps respect. This is where the equioriented type-A
    structure is used: the single forward direction lets the complements be
    built by one pass.

Mathlib has no type-A Gabriel theorem, so the existence half was built from
scratch. It is proved first for an abstract chain of finite-dimensional vector
spaces and then transported to a tuple by reading each matrix as the linear map
$x \mapsto A_i x$.

??? info "Formalised in Lean — Core.Barcode and Core.Gabriel"
    The abstract-chain statement (`Core.Barcode`) packages a barcode as a finite
    family of bars with the trajectory and basis conditions:

    ```
    def HasBarcode (P : ∀ t, Submodule k (V t)) : Prop :=
      ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)) (line : Fin M → ∀ t, V t),
        (∀ lam, birth lam ≤ death lam)
        ∧ (∀ lam t, ¬ (birth lam ≤ t ∧ t ≤ death lam) → line lam t = 0)
        ∧ (∀ lam t, birth lam ≤ t → t ≤ death lam → line lam t ≠ 0)
        ∧ (∀ lam (e : Fin N), birth lam ≤ e.castSucc → e.succ ≤ death lam →
              f e (line lam e.castSucc) = line lam e.succ)
        ∧ (∀ lam (e : Fin N), death lam < e.succ → f e (line lam e.castSucc) = 0)
        ∧ (∀ t, iSupIndep (fun lam => k ∙ line lam t))
        ∧ (∀ t, ⨆ lam, (k ∙ line lam t) = P t)

    theorem hasBarcode_of_isSubrep [∀ t, FiniteDimensional k (V t)]
        (P : ∀ t, Submodule k (V t)) (hP : IsSubrep V f P) : HasBarcode V f P

    theorem hasBarcode_tuple (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
        HasBarcode (chainSpace k d) (chainEdge d A) (fun _ ↦ ⊤)
    ```

    The last two clauses of `HasBarcode` are existence's heart: at every vertex
    the bar-lines are independent (`iSupIndep`) and span (`⨆ = P t`), so they
    form a basis adapted to the interval decomposition.
    `hasBarcode_of_isSubrep` is the existence half of Gabriel on an abstract
    chain (total-dimension strong induction, one bar peeled per step);
    `hasBarcode_tuple` transports it to a tuple via
    $f_t = (A_t)\,\cdot$, the map `chainEdge`. Both are sorry-free and
    axiom-clean.

## 3.4 Decomposing the running example

The barcode of a concrete tuple is found by tracing threads through the chain.

!!! example "Example 3.3 — The $(2,2,2)$ rank-one tuple as a barcode"
    Take the pair from Example 2.6,

    $$
    A = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix},
    \qquad
    B = \begin{pmatrix} 0 & 0 \\ 0 & 1 \end{pmatrix},
    $$

    a representation $k^2 \xrightarrow{A} k^2 \xrightarrow{B} k^2$ with $BA = 0$.
    Trace the standard basis threads, writing $e^{(l)}_1, e^{(l)}_2$ for the
    basis of $V_l = k^2$:

    - $e^{(0)}_2$: killed immediately, $A e^{(0)}_2 = 0$. A bar $[0,0]$, i.e.
      $M_{00}$.
    - $e^{(0)}_1$: $A e^{(0)}_1 = e^{(1)}_1$, then $B e^{(1)}_1 = 0$. A bar
      $[0,1]$, i.e. $M_{01}$.
    - $e^{(1)}_2$: not reached from $V_0$, and $B e^{(1)}_2 = e^{(2)}_2$. A bar
      $[1,2]$, i.e. $M_{12}$.
    - $e^{(2)}_1$: not reached from $V_1$. A bar $[2,2]$, i.e. $M_{22}$.

    So

    $$
    (A, B) \;\cong\; M_{00} \oplus M_{01} \oplus M_{12} \oplus M_{22},
    $$

    with multiplicities $m_{00} = m_{01} = m_{12} = m_{22} = 1$ and the other
    $m_{ij} = 0$. The dimension check holds at each vertex: vertex $0$ carries
    the bars $[0,0]$ and $[0,1]$ ($\dim = 2$), vertex $1$ carries $[0,1]$ and
    $[1,2]$ ($\dim = 2$), vertex $2$ carries $[1,2]$ and $[2,2]$ ($\dim = 2$).

    This is the decomposition the next chapter reads off the rank pattern, and it
    is the orbit used as the classification witness over $\mathbb Q$
    (`Core.Gabriel.tupleWitnessQ`).

!!! question "Checkpoint"
    Which interval modules occur in the decomposition of the $(2,2,2)$ tuple
    with $A = B = \left(\begin{smallmatrix} 1 & 0 \\ 0 & 1 \end{smallmatrix}\right)$
    (the identity pair)?

??? tip "Solution"
    Both maps are the identity, so each standard basis thread survives the whole
    chain: $e^{(0)}_1$ and $e^{(0)}_2$ each give a bar $[0,2]$. Hence the tuple is
    $M_{02}^{\,2}$, with $m_{02} = 2$ and all other multiplicities $0$. Its
    product rank is $2$ (the composite is the identity), matching $m_{0N} = r$ as
    the count of full-length bars.

## Sources and cross-references

Interval modules, Gabriel's theorem for the equioriented type-A quiver
(Theorem 2.5 of the paper), and the decomposition into a barcode are Section 2 of
the paper and Section 2 of the
[high-level overview](../paper-digest/high-level-overview.md). The existence half
is formalised in `DLNFibre.Core.Barcode` (abstract chains) and
`DLNFibre.Core.Gabriel` (tuples); the interval modules and their direct sums are
in `DLNFibre.Core.IntervalModule`.

The next chapter records a barcode in two equivalent ways — the **rank pattern**
$r_{ij}$ and the **Kostant partition** $m_{ij}$ — and proves the
inclusion–exclusion formula that converts between them. Uniqueness of the Gabriel
multiplicities is a corollary.
