---
title: "Composable Matrix Chains and the Type-A Quiver Classification"
status: archived
source: exposition
topics: [core-machinery, quiver-representations, gabriel, rank-pattern, kostant, orbit-classification]
created: "2026-06-15"
updated: "2026-06-18"
---

# Composable Matrix Chains and the Type-A Quiver Classification

!!! warning "Archival / non-canonical"
    This is a consolidated single-file draft of the core-machinery development.
    The **canonical** exposition is the numbered chapter series indexed in
    [`README.md`](README.md) (chapters 1–5). This file is kept as a continuous-read
    source/archive; it is not maintained in step with the chapters and is not linked
    from the index. Prefer the numbered chapters. In particular, the per-result
    status claims in §6 / the Formalisation section (calling Cor 3.5, Thm 3.8, and
    the $(C,\theta)$ computations "cited, not reproved") are **superseded** — those
    are now Proved in `DLNFibre.Core`; see [`ROADMAP.md`](../../../ROADMAP.md) for
    current status.

Let $A_1, \ldots, A_N$ be composable matrices, $A_i$ of size $d_i \times
d_{i-1}$, with product $A_N \cdots A_1$. We study the chains with a prescribed
product, classified up to change of basis at each space.

Already the two-step case is not determinantal. For scalars $a_1, a_2$ the
product $a_2 a_1$ vanishes iff $a_1 = 0$ or $a_2 = 0$, two lines in the plane.
For $2 \times 2$ matrices $A, B$ the locus $\{BA = 0\}$ has three irreducible
components: $\{A = 0\}$ and $\{B = 0\}$, each of dimension $4$, and the closure
of the set where $A$ and $B$ both have rank one with $\operatorname{im} A
\subseteq \ker B$, of dimension $5$. The largest component is the last; it is
governed by an incidence between the image of one factor and the kernel of the
other, not by the vanishing of either. The classification below organizes that
incidence data and makes the dimension and component counts computable.

We work over an arbitrary field $k$. The development is independent of any
neural-network interpretation: the deep-linear-network loss whose geometry it
controls, and the resulting log-canonical threshold, belong to a later part and
are not used here. The results are those of Lehalleur and Rimányi (2024),
Sections 2–3, and each central definition and theorem is formalised in the Lean
library `DLNFibre.Core` (the collapsible notes give the declarations). The
argument runs from the space of chains and its rank loci (§1) through the
base-change action (§2), Gabriel's decomposition (§3), and the rank-pattern and
Kostant encodings (§4) to the classification (§5).

## 1. The space of chains and its rank loci

A **dimension vector** is a list $\underline d = (d_0, d_1, \ldots, d_N)$ of
nonnegative integers. A **composable tuple** of shape $\underline d$ is a chain

$$
k^{d_0} \xrightarrow{\ A_1\ } k^{d_1}
\xrightarrow{\ A_2\ } \cdots
\xrightarrow{\ A_N\ } k^{d_N},
$$

with $A_i \in \operatorname{Mat}_{d_i, d_{i-1}}(k)$. Write $A_\ast = (A_1, \ldots,
A_N)$ for the chain and $\operatorname{Rep}_{\underline d} = \prod_{i=1}^N
\operatorname{Mat}_{d_i, d_{i-1}}(k)$ for the space of all of them, an affine
space of dimension $\sum_{i=1}^N d_i d_{i-1}$.

The **multiplication map** sends a chain to its product,

$$
\operatorname{mult} \colon \operatorname{Rep}_{\underline d}
\longrightarrow \operatorname{Mat}_{d_N, d_0}(k),
\qquad
\operatorname{mult}(A_\ast) = A_N A_{N-1} \cdots A_1,
$$

a morphism of affine spaces, since its entries are polynomials in the entries of
the $A_i$. Its rank loci and fibers are the objects of study: for $0 \le r \le
\min_i d_i$ and $B \in \operatorname{Mat}_{d_N, d_0}(k)$,

$$
\Sigma^{r}_{\underline d} = \{A_\ast : \operatorname{rank}(A_N \cdots A_1) = r\},
\qquad
\overline{\Sigma}^{\,r}_{\underline d} = \{A_\ast : \operatorname{rank}(A_N \cdots A_1) \le r\},
$$

and the fiber $\operatorname{mult}^{-1}(B) = \{A_\ast : A_N \cdots A_1 = B\}$. The
zero-product locus $\Sigma^0_{\underline d}$ is the fiber over $B = 0$.

The locus $\overline{\Sigma}^{\,r}_{\underline d}$ is the Zariski-closed set cut
out by the $(r{+}1) \times (r{+}1)$ minors of the product, and it is the closure
of $\Sigma^{r}_{\underline d}$; the closed part is recorded below.

??? proof "Rank is lower semicontinuous"
    For a matrix $M$, $\operatorname{rank} M \ge s$ holds iff some $s \times s$
    minor is nonzero. The minors of $\operatorname{mult}(A_\ast)$ are polynomials
    in the entries of $A_\ast$, so $\{\operatorname{rank}\operatorname{mult} \ge
    s\}$ is open and $\overline{\Sigma}^{\,s-1}_{\underline d}$ is closed. Along a
    family $A_\ast(t) \to A_\ast(0)$ with rank $\rho$ for $t \ne 0$, a limit of
    rank $\ge \rho+1$ would have a nonzero $(\rho{+}1)$-minor at $t = 0$, hence
    nonzero for small $t \ne 0$ — contradicting rank $\rho$ there. So rank can
    only drop in the limit. (That $\Sigma^{r}_{\underline d}$ is dense in
    $\overline{\Sigma}^{\,r}_{\underline d}$ is not elementary; it follows from
    the orbit-closure order, Lehalleur–Rimányi, Theorem 3.8.)

The invariants to be computed for these loci are the codimension $C$ of the
top-dimensional irreducible components and their number $\theta$. For the
$2\times 2$ example, $C = 3$ and $\theta = 1$. Computing $(C, \theta)$ in general
is the subject of the later parts; the classification developed here is its
prerequisite.

??? info "Formalised in Lean — the objects (`Core.Setup`, `Core.Submult`)"

        abbrev Tuple (d : Fin (N + 1) → ℕ) : Type u :=
          ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k

        def mult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
            Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k :=
          multPrefix d A (Fin.last N)

        def productRankLocus   (d) (r : ℕ) : Set (Tuple d) := {A | (mult d A).rank = r}
        def productRankLocusLE (d) (r : ℕ) : Set (Tuple d) := {A | (mult d A).rank ≤ r}
        def fibre (d) (B) : Set (Tuple d) := {A | mult d A = B}

    The $N+1$ vertices are indexed by `Fin (N+1)`, the $N$ maps by `Fin N`. The
    interval compositions $A_j \cdots A_{i+1}$ of §4 are `Core.Submult.submult i
    j`, with `mult_eq_submult` the case $0 \to N$. The invariants $C, \theta$ are
    not yet formalised.

## 2. The base-change group and its orbits

Changing basis in each $k^{d_i}$ by an invertible matrix $P_i$ replaces $A_i$ by
$P_i A_i P_{i-1}^{-1}$. The **base-change group**

$$
G_{\underline d} = \prod_{i=0}^{N} \operatorname{GL}_{d_i}(k)
$$

acts on $\operatorname{Rep}_{\underline d}$ by $(P \cdot A_\ast)_i = P_i A_i
P_{i-1}^{-1}$, and classifying chains up to change of basis means describing the
orbit space $\operatorname{Rep}_{\underline d} / G_{\underline d}$.

A chain is a representation of a **quiver** — a directed graph with a vector
space at each vertex and a linear map along each arrow. The relevant graph is the
path

$$
0 \longrightarrow 1 \longrightarrow \cdots \longrightarrow N
$$

with all arrows in one direction; this is the **equioriented** orientation of the
Dynkin diagram $A_{N+1}$, so the chains are representations of the equioriented
type-$A$ quiver. A base change is an isomorphism of such representations, so the
$G_{\underline d}$-orbits are the isomorphism classes (Lehalleur–Rimányi,
Theorem 2.4).

Interval ranks are orbit invariants. For $i \le j$,

$$
(P \cdot A_\ast)_j \cdots (P \cdot A_\ast)_{i+1}
= P_j \,(A_j \cdots A_{i+1})\, P_i^{-1},
$$

the interior factors $P_m^{-1} P_m$ cancelling, and rank is unchanged under
multiplication by invertible matrices. Hence $\operatorname{rank}(A_j \cdots
A_{i+1})$ is constant on orbits, and each $\Sigma^r_{\underline d}$,
$\overline{\Sigma}^{\,r}_{\underline d}$ is a union of orbits.

??? info "Formalised in Lean — the action (`Core.BaseChange`)"

        abbrev BaseChangeGroup (d : Fin (N + 1) → ℕ) : Type u :=
          ∀ v : Fin (N + 1), (Matrix (Fin (d v)) (Fin (d v)) k)ˣ

        def baseChange (P : BaseChangeGroup d) (A : Tuple d) : Tuple d :=
          fun i ↦ Units.val (P i.succ) * A i * Units.val ((P i.castSucc)⁻¹)

        theorem rankPattern_baseChange (P) (A) (i j) (hij : i ≤ j) :
            rankPattern d (baseChange P A) i j hij = rankPattern d A i j hij

    `submult_baseChange` is the telescoping identity; `rankPattern_baseChange`
    its rank consequence (`rankPattern d A i j` is the rank of $A_j \cdots
    A_{i+1}$, §4).

## 3. Gabriel's theorem: decomposition into interval modules

For $0 \le i \le j \le N$, the **interval module** $M_{ij}$ is the representation
that is one-dimensional on the vertices $i, \ldots, j$, zero elsewhere, with
identity maps along the interval:

$$
0 \to \cdots \to \underset{i}{k} \xrightarrow{\,1\,} k \xrightarrow{\,1\,}
\cdots \xrightarrow{\,1\,} \underset{j}{k} \to \cdots \to 0.
$$

Its dimension vector is the indicator of $[i,j]$. The direct sum of two
representations has vertex spaces $V_l \oplus V'_l$ and block-diagonal arrow
maps, so a finite sum $\bigoplus_{i \le j} M_{ij}^{\,m_{ij}}$ is a block-diagonal
chain with dimension $\sum_{i \le l \le j} m_{ij}$ at vertex $l$.

!!! theorem "Gabriel's theorem, equioriented type $A$ (Lehalleur–Rimányi, Theorem 2.5)"
    Every representation is isomorphic to a direct sum of interval modules,

    $$
    A_\ast \;\cong\; \bigoplus_{0 \le i \le j \le N} M_{ij}^{\,m_{ij}}.
    $$

    Equivalently, every chain is base-change-equivalent to a block-diagonal chain
    of interval modules.

Such a decomposition is a **barcode**: a multiset of intervals $[i,j]$, one bar
per interval summand. A bar $[i,j]$ is a one-dimensional summand supported on
vertices $i$ through $j$; at each vertex $l$ the bars with $i \le l \le j$ form a
basis, and each arrow maps an alive bar to the next vertex or to zero at its end.

For the $2 \times 2$ pair $A = \left(\begin{smallmatrix} 1 & 0 \\ 0 & 0
\end{smallmatrix}\right)$, $B = \left(\begin{smallmatrix} 0 & 0 \\ 0 & 1
\end{smallmatrix}\right)$ with $BA = 0$, tracing the standard basis through
$k^2 \xrightarrow{A} k^2 \xrightarrow{B} k^2$ gives the bars

```
            vertex 0      vertex 1      vertex 2
  e1 :        •─────────────•                        bar [0,1]   (M01)
  e2 :        •                                      bar [0,0]   (M00)
              (new at 1)    •─────────────•          bar [1,2]   (M12)
              (new at 2)                  •          bar [2,2]   (M22)
```

so $(A, B) \cong M_{00} \oplus M_{01} \oplus M_{12} \oplus M_{22}$, with each
vertex carrying two bars.

Existence is proved by induction on $\sum_l \dim V_l$, peeling one interval per
step: a maximal forward-running line through a chosen vector spans an interval
submodule $M_{ij}$ that splits off as a direct summand, leaving a chain of
smaller total dimension. The single forward orientation is what lets the
complement be chosen vertex by vertex; for a general quiver the statement is
deeper. Mathlib has no type-$A$ Gabriel theorem, so existence was proved from the
ground up — first for an abstract chain of vector spaces, then transported to a
matrix tuple via $x \mapsto A_i x$. Uniqueness of the multiplicities is deferred
to §4, where it follows from the rank pattern.

??? info "Formalised in Lean — interval modules and Gabriel existence"
    Interval modules and their block sums (`Core.IntervalModule`):

        def intervalModule (i j : Fin (N + 1)) : Tuple (intervalDim i j) :=
          fun t _ _ ↦ if intervalActive i j t then (1 : k) else 0

        noncomputable def intervalDirectSum :
            (L : List (Fin (N + 1) × Fin (N + 1))) → Tuple (foldDim L)
          | []      => zeroTuple
          | p :: ps => dirSum (intervalModule p.1 p.2) (intervalDirectSum ps)

    Existence (`Core.Barcode`, `Core.Gabriel`) carries a barcode as a finite
    family of bars (birth, death, a line running along the interval) independent
    and spanning at every vertex:

        def HasBarcode (P : ∀ t, Submodule k (V t)) : Prop :=
          ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)) (line : Fin M → ∀ t, V t),
            (∀ lam, birth lam ≤ death lam) ∧ … ∧
            (∀ t, iSupIndep (fun lam => k ∙ line lam t)) ∧
            (∀ t, ⨆ lam, (k ∙ line lam t) = P t)

        theorem hasBarcode_tuple (d) (A : Tuple d) :
            HasBarcode (chainSpace k d) (chainEdge d A) (fun _ ↦ ⊤)

    Sorry-free and axiom-clean.

## 4. Rank patterns and Kostant partitions

A barcode admits two numerical encodings.

The **rank pattern** is the array $r_{ij} = \operatorname{rank}(A_j \cdots
A_{i+1})$ for $i \le j$, with $r_{ii} = d_i$. It is computed from the matrices and
is constant on orbits (§2).

The **multiplicity array** $m_{ij}$ records the number of bars $[i,j]$, i.e. the
multiplicity of $M_{ij}$. It is a **Kostant partition** of $\underline d$: since
the bars alive at vertex $k$ form a basis of $V_k$,

$$
d_k = \sum_{i \le k \le j} m_{ij}, \qquad 0 \le k \le N.
$$

The two encodings are related by inclusion–exclusion. A bar $[a,b]$ contributes
to $r_{ij}$ — survives the composition from $i$ to $j$ — iff it covers the whole
interval, $a \le i$ and $b \ge j$:

```
              i           j
              |←—————————→|
  [a,b]:   •——————————————————•        a ≤ i, b ≥ j :  contributes to r_ij
  [a',b']:        •—————•               does not cover [i,j] :  does not
```

Hence

$$
r_{ij} = \sum_{a \le i,\ b \ge j} m_{ab},
$$

a corner sum of the multiplicities, inverted by the four-term second difference

$$
m_{ij} = r_{ij} - r_{i,\,j+1} - r_{i-1,\,j} + r_{i-1,\,j+1}
$$

(out-of-range entries $0$). The two transforms are mutually inverse
(Lehalleur–Rimányi, Proposition 3.1).

Two consequences follow. First, the Gabriel decomposition is unique: $m_{ij}$ is
the second difference of the rank pattern, which is determined by the chain, so
the multiplicities are. Second, for the running example the ranks

$$
\underline r =
\begin{pmatrix} 2 & 1 & 0 \\ & 2 & 1 \\ & & 2 \end{pmatrix}
$$

($\operatorname{rank} A = \operatorname{rank} B = 1$, $\operatorname{rank} BA =
0$, diagonal $\underline d$) have second difference $m_{00} = m_{01} = m_{12} =
m_{22} = 1$, the four bars above.

??? info "Formalised in Lean — the inversion and its consequences"
    The abstract inversion (`Core.RankPattern`):

        noncomputable def cumul (N : ℤ) (m : ℤ → ℤ → R) : ℤ → ℤ → R := …  -- ∑_{k≤i, j≤l≤N} m k l
        def diff (r : ℤ → ℤ → R) : ℤ → ℤ → R := …                        -- four-term second difference
        noncomputable def cumulDiffEquiv (N : ℤ) : SuppArray N R ≃ SuppArray N R

    On the tuple side (`Core.Gabriel`), `exists_barcode_rankPattern` gives $r_{ij}$
    as the count of bars covering $[i,j]$ (with the Kostant constraint), and
    `rankPattern_eq_cumul_barMult` forces the multiplicities to be $\operatorname{
    diff}$ of the rank pattern.

## 5. The classification: the rank pattern is a complete invariant

!!! theorem "Complete invariant (Lehalleur–Rimányi, Corollary 2.9)"
    Two chains have the same rank pattern iff they lie in the same
    $G_{\underline d}$-orbit:

    $$
    \big(\forall\, i \le j,\ r_{ij}(A_\ast) = r_{ij}(B_\ast)\big)
    \iff
    \exists\, P \in G_{\underline d},\ P \cdot A_\ast = B_\ast.
    $$

The forward implication is §2. For the converse, equal rank patterns give equal
multiplicities (§4), so $A_\ast$ and $B_\ast$ decompose into the same bars.
Pairing each bar of one with the bar of the other having the same endpoints and
sending bar-line to bar-line defines an invertible map at each vertex; the
trajectory conditions make it commute with the arrows, giving a base change
$P$ with $P \cdot A_\ast = B_\ast$.

Taking $B_\ast = \bigoplus M_{ij}^{\,m_{ij}}$ gives a canonical representative:
every chain is base-change-equivalent to the block-diagonal sum of its own bars,
its **normal form**, and each orbit contains exactly one such block chain. The
correspondence orbit $\mapsto$ rank pattern is therefore a bijection between
orbits and realizable rank patterns, and through the inversion of §4 between
orbits and Kostant partitions of $\underline d$. Orbits, isomorphism classes,
realizable rank patterns, and Kostant partitions are four descriptions of one
finite set.

??? note "The orbits of $\Sigma^0$ for $\underline d = (2,2,2)$"
    The orbits inside $\Sigma^0$ are the Kostant partitions with $m_{02} = 0$
    (no full bar $M_{02}$, equivalently $r_{02} = \operatorname{rank} BA = 0$).
    Solving $d_k = \sum_{i \le k \le j} m_{ij}$ gives six, listed by rank corner
    $(r_{01}, r_{12})$ (with $r_{02} = 0$) and normal form:

    | $(r_{01}, r_{12})$ | normal form | chain |
    |:---:|:---|:---|
    | $(0,0)$ | $M_{00}^2 \oplus M_{11}^2 \oplus M_{22}^2$ | $A = B = 0$ |
    | $(0,1)$ | $M_{00}^2 \oplus M_{11} \oplus M_{12} \oplus M_{22}$ | $A=0$, $\operatorname{rank} B = 1$ |
    | $(0,2)$ | $M_{00}^2 \oplus M_{12}^2$ | $A=0$, $\operatorname{rank} B = 2$ |
    | $(1,0)$ | $M_{00} \oplus M_{01} \oplus M_{11} \oplus M_{22}^2$ | $\operatorname{rank} A = 1$, $B=0$ |
    | $(1,1)$ | $M_{00} \oplus M_{01} \oplus M_{12} \oplus M_{22}$ | rank one each, $\operatorname{im} A = \ker B$ |
    | $(2,0)$ | $M_{01}^2 \oplus M_{22}^2$ | $\operatorname{rank} A = 2$, $B=0$ |

    The three orbits with an entrywise-maximal rank corner — $(0,2)$, $(2,0)$,
    $(1,1)$ — have closures the three components of $\Sigma^0_{(2,2,2)}$ from the
    introduction; the others sit inside them ($(0,1) \le (0,2)$, $(1,0) \le
    (2,0)$, $(0,0)$ below all). The $(1,1)$ component has codimension $3$, the
    others $4$, so $C = 3$, $\theta = 1$.

??? info "Formalised in Lean — the classification (`Core.Orbit`, `Core.OrbitKostant`)"

        theorem rankPattern_eq_iff_orbit (A B : Tuple d) :
            (∀ i j (hij : i ≤ j), rankPattern d A i j hij = rankPattern d B i j hij)
              ↔ ∃ P : BaseChangeGroup d, P • A = B

        theorem baseChange_normalForm (A : Tuple d) :
            ∃ (L) (h : foldDim L = d) (P : BaseChangeGroup d),
              P • A = h ▸ intervalDirectSum L ∧ …

        noncomputable def orbitKostantEquiv (d) :
            Quotient (orbitSetoid d) ≃ RealizableRank d

    `orbit_of_rankPattern_eq` is the construction (equal ranks → equal
    multiplicities → a relabelling of bars → a `Basis.equiv` intertwiner → the
    base change); `orbitKostantEquiv` is the resulting bijection. Sorry-free and
    axiom-clean.

## 6. Beyond the classification

The classification fixes, for each $\underline d$, the orbits of chains (the
Kostant partitions), their normal forms, and the complete invariant. The
remaining quantities are dimensions. The codimension of an orbit closure is the
dimension of its normal slice $\operatorname{Ext}(M, M)$ (Lehalleur–Rimányi,
Corollary 3.5, after Voigt); which closures are irreducible components is settled
by the orbit-closure order (their Theorem 3.8); from these the codimension $C$
and the count $\theta$ admit three computations — a Poincaré series, a quadratic
integer program, and a closest-lattice-point formula — and yield the
log-canonical threshold of the deep-linear-network loss (their Theorem 8.6).
These rest on the classification proved here and are cited, not reproved.

## Formalisation

Every definition and theorem above is formalised in Lean 4 + Mathlib, in
`DLNFibre.Core`, sorry-free and axiom-clean:

| Section | Lean module(s) |
|:---|:---|
| 1. chains, multiplication, loci | `Core.Setup`, `Core.Submult` |
| 2. base-change group, rank-invariance | `Core.BaseChange` |
| 3. interval modules, Gabriel existence | `Core.IntervalModule`, `Core.Barcode`, `Core.Gabriel` |
| 4. rank pattern $\leftrightarrow$ Kostant, inversion | `Core.RankPattern`, `Core.Gabriel` |
| 5. complete invariant, normal form, bijection | `Core.Orbit`, `Core.OrbitKostant` |

Cited to Lehalleur–Rimányi and not formalised: the orbit-closure order
(Theorem 3.8), the $\operatorname{Ext}$ codimension (Corollary 3.5), the
computations of $(C,\theta)$ (Sections 5–7), and the log-canonical-threshold
identity (Theorem 8.6). See [`ROADMAP.md`](../../../ROADMAP.md).

## Sources

S. Pepin Lehalleur and R. Rimányi, *Geometry of the fibers of the multiplication
map of deep linear neural networks* (2024); source at
`paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`. A map of the whole
paper is the [high-level overview](../paper-digest/high-level-overview.md).
