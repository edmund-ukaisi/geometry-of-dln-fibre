---
title: "The Classification: Orbits and Kostant Partitions"
status: draft
source: exposition
topics: [core-machinery, complete-invariant, normal-form, corollary-2.9, orbit-classification]
created: "2026-06-14"
updated: "2026-06-14"
---

# The Classification: Orbits and Kostant Partitions

The previous chapters assembled the pieces. A tuple is a representation of the
type-A quiver ([Chapter 2](02-quiver-representations-and-the-base-change-group.md));
it decomposes into interval modules ([Chapter 3](03-gabriels-theorem-interval-modules-and-the-barcode.md));
and its barcode is recorded by either the rank pattern or the Kostant partition,
which convert by inclusion–exclusion ([Chapter 4](04-rank-patterns-and-kostant-partitions.md)).
This chapter closes the circle. The rank pattern, already known to be constant on
orbits, is shown to be a **complete** invariant: tuples with the same rank
pattern lie in the same orbit. Consequently the orbits, the isomorphism classes,
the realizable rank patterns, and the Kostant partitions of $\underline d$ are
four names for one finite set.

## 5.1 The rank pattern is a complete invariant

Chapter 2 showed equal orbits force equal rank patterns. The reverse is the
substantial direction.

!!! theorem "The rank pattern is a complete invariant (heart of Corollary 2.9 of the paper)"
    Two tuples $A_\ast, B_\ast \in \operatorname{Rep}_{\underline d}$ have the
    same rank pattern if and only if they lie in the same $G_{\underline
    d}$-orbit:

    $$
    \big(\forall\, i \le j,\ r_{ij}(A_\ast) = r_{ij}(B_\ast)\big)
    \quad\Longleftrightarrow\quad
    \exists\, P \in G_{\underline d},\ P \cdot A_\ast = B_\ast.
    $$

The forward direction is the construction; the backward direction is the
orbit-invariance of Chapter 2. The forward direction runs through the barcode.

??? proof "Equal rank patterns build a base change (proof idea)"
    Suppose $A_\ast$ and $B_\ast$ have equal rank patterns. By the uniqueness of
    Chapter 4, their barcode multiplicities agree: both decompose as the same
    direct sum $\bigoplus M_{ij}^{\,m_{ij}}$ of interval modules, with identical
    $m_{ij}$. Choose barcodes for each (Chapter 3). Because the multiplicities
    match, there is a bijection between the bars of $A_\ast$ and the bars of
    $B_\ast$ pairing each bar with one of the same endpoints $[i,j]$.

    Each bar carries a one-dimensional line through its interval. Sending the
    line of an $A_\ast$-bar to the line of the paired $B_\ast$-bar, vertex by
    vertex, defines at each vertex $t$ a linear isomorphism $\varphi_t \colon
    V_t \to V_t$ — it takes the $A_\ast$-barcode basis of $V_t$ to the
    $B_\ast$-barcode basis. The trajectory conditions (the arrows carry each
    line forward along its bar) make $\varphi$ commute with the arrows, so
    $\varphi$ is an isomorphism of representations $A_\ast \to B_\ast$. Its
    vertex maps assemble into a base change $P \in G_{\underline d}$ with
    $P \cdot A_\ast = B_\ast$.

??? info "Formalised in Lean — Core.Orbit"

    ```lean
    theorem orbit_of_rankPattern_eq {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d)
        (h : ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
          rankPattern d A i j hij = rankPattern d B i j hij) :
        ∃ P : BaseChangeGroup (k := k) d, P • A = B

    theorem rankPattern_eq_iff_orbit {d : Fin (N + 1) → ℕ} (A B : Tuple (k := k) d) :
        (∀ (i j : Fin (N + 1)) (hij : i ≤ j),
            rankPattern d A i j hij = rankPattern d B i j hij)
          ↔ ∃ P : BaseChangeGroup (k := k) d, P • A = B
    ```

    `orbit_of_rankPattern_eq` is the forward construction: equal rank patterns
    give equal bar-multiplicity arrays (`diff_cumul`), a relabelling of bars, a
    `Basis.equiv` intertwiner $\varphi_t$ at each vertex, and finally the base
    change $P$ (`baseChange_of_intertwine`). `rankPattern_eq_iff_orbit` packages
    both directions as the complete invariant. Sorry-free and axiom-clean.

## 5.2 The Gabriel normal form

Specializing $B_\ast$ to the block-diagonal direct sum gives a canonical
representative for each orbit.

!!! theorem "The Gabriel normal form"
    Every tuple $A_\ast$ is $G_{\underline d}$-equivalent to the interval direct
    sum of its own bars: there is a list $L$ of interval endpoints with
    multiplicity array $\underline m = \operatorname{diff}(r(A_\ast))$, a
    dimension match $\operatorname{foldDim} L = \underline d$, and a base change
    $P$ with

    $$
    P \cdot A_\ast = \bigoplus_{(i,j) \in L} M_{ij}.
    $$

The right-hand side is manifestly a direct sum of interval modules, so this is
the explicit normal form: every orbit contains exactly one block-diagonal tuple
$\bigoplus M_{ij}^{\,m_{ij}}$, and the orbit is named by the multiplicities.

??? info "Formalised in Lean — Core.Orbit.baseChange_normalForm"

    ```lean
    theorem baseChange_normalForm {d : Fin (N + 1) → ℕ} (A : Tuple (k := k) d) :
        ∃ (L : List (Fin (N + 1) × Fin (N + 1))) (h : foldDim L = d)
          (P : BaseChangeGroup (k := k) d),
          P • A = h ▸ intervalDirectSum L ∧ (∀ p ∈ L, p.1 ≤ p.2) ∧
          ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
            (rankPattern d A i j hij : ℤ) = cumul (N : ℤ) (multiplicityArray L) (i : ℤ) (j : ℤ)
    ```

    Built from the complete invariant by exhibiting `intervalDirectSum L` (the
    list $L$ of the tuple's own bars) as a tuple with the same rank pattern as
    `A`, then applying `orbit_of_rankPattern_eq`. The final clause records that
    $L$'s multiplicity array is the second difference of the rank pattern.

## 5.3 Orbits, rank patterns, and Kostant partitions coincide

The complete invariant gives the bijection at the head of the chapter.

!!! definition "Definition 5.1 — Realizable rank patterns"
    A **realizable rank pattern** of $\underline d$ is an array that arises as
    $r(A_\ast)$ for some tuple $A_\ast \in \operatorname{Rep}_{\underline d}$.

!!! theorem "Corollary 2.9 of the paper — orbits $\leftrightarrow$ Kostant partitions"
    The map $A_\ast \mapsto r(A_\ast)$ descends to a bijection

    $$
    \{\, G_{\underline d}\text{-orbits of } \operatorname{Rep}_{\underline d} \,\}
    \;\xrightarrow{\ \sim\ }\;
    \{\, \text{realizable rank patterns of } \underline d \,\}.
    $$

    Through the inclusion–exclusion inversion of Chapter 4, the realizable rank
    patterns correspond to the Kostant partitions of $\underline d$. So orbits,
    isomorphism classes, realizable rank patterns, and Kostant partitions are the
    same finite set.

The bijection is the complete invariant read as a quotient: injectivity is the
forward direction of §5.1 (equal rank pattern $\Rightarrow$ same orbit), and
surjectivity is the definition of "realizable". Composing with the
$\operatorname{cumul}/\operatorname{diff}$ bijection turns the right-hand side
into Kostant partitions.

??? info "Formalised in Lean — Core.OrbitKostant.orbitKostantEquiv"

    ```lean
    abbrev RealizableRank (d : Fin (N + 1) → ℕ) := ↥(Set.range (rankFn (k := k) d))

    noncomputable def orbitKostantEquiv (d : Fin (N + 1) → ℕ) :
        Quotient (orbitSetoid (k := k) d) ≃ RealizableRank (k := k) d :=
      (Quotient.congrRight (fun A B ↦ (rankFn_eq_iff_orbit A B).symm)).trans
        (Setoid.quotientKerEquivRange (rankFn d))
    ```

    `orbitSetoid d` is the orbit relation; `rankFn d A` is the rank pattern as a
    total function (the complete invariant); `RealizableRank d` is its range.
    `orbitKostantEquiv` is the bijection orbits $\leftrightarrow$ realizable rank
    patterns, via the first isomorphism theorem `Setoid.quotientKerEquivRange`.
    Identifying realizable rank patterns with Kostant partitions is the
    `cumulDiffEquiv` of Chapter 4. Sorry-free and axiom-clean.

## 5.4 The orbits of the $(2,2,2)$ zero-product locus

The classification makes the components of Chapter 1 explicit. The zero-product
locus $\Sigma^0_{\underline d}$ is the union of the orbits with $r_{0N} = 0$,
equivalently $m_{0N} = 0$ — those Kostant partitions with no full-length bar
$M_{0N}$.

!!! example "Example 5.2 — Six orbits, three components"
    For $\underline d = (2,2,2)$, the Kostant partitions with $m_{02} = 0$ are
    six. Writing each orbit by its rank corner $(r_{01}, r_{12})$ (with
    $r_{02} = 0$ throughout) and its block-diagonal normal form:

    | $(r_{01}, r_{12})$ | normal form | description |
    |:---:|:---|:---|
    | $(0,0)$ | $M_{00}^2 \oplus M_{11}^2 \oplus M_{22}^2$ | $A = B = 0$ |
    | $(0,1)$ | $M_{00}^2 \oplus M_{11} \oplus M_{12} \oplus M_{22}$ | $A = 0$, $\operatorname{rank} B = 1$ |
    | $(0,2)$ | $M_{00}^2 \oplus M_{12}^2$ | $A = 0$, $\operatorname{rank} B = 2$ |
    | $(1,0)$ | $M_{00} \oplus M_{01} \oplus M_{11} \oplus M_{22}^2$ | $\operatorname{rank} A = 1$, $B = 0$ |
    | $(1,1)$ | $M_{00} \oplus M_{01} \oplus M_{12} \oplus M_{22}$ | $\operatorname{rank} A = \operatorname{rank} B = 1$, $\operatorname{im} A = \ker B$ |
    | $(2,0)$ | $M_{01}^2 \oplus M_{22}^2$ | $\operatorname{rank} A = 2$, $B = 0$ |

    These six orbits stratify $\Sigma^0_{(2,2,2)}$. Its three irreducible
    components from Chapter 1 are the closures of the three orbits that are
    maximal in the orbit-closure order — entrywise-maximal rank patterns: the
    $(0,2)$ orbit ($\{A=0\}$), the $(2,0)$ orbit ($\{B=0\}$), and the $(1,1)$
    orbit ($\{\det A = \det B = 0,\ BA = 0\}$). The remaining three orbits sit in
    their closures: $(0,1) \le (0,2)$, $(1,0) \le (2,0)$, and $(0,0)$ below all.

    The top-dimensional component is the $(1,1)$ orbit's closure, of codimension
    $3$, so $C = 3$ and $\theta = 1$ — recovering Chapter 1. The codimension
    values and the orbit-closure order itself are the content of the chapters
    after this part (the $\operatorname{Ext}$ codimension, Cor 3.5 of the paper,
    and the closure order, Thm 3.8); the classification of the six orbits and
    their rank patterns is the content of this part.

## 5.5 What this part establishes, and what comes next

The classification is complete and, in Lean, sorry-free and axiom-clean. To
restate it plainly: for a fixed dimension vector $\underline d$, the
$G_{\underline d}$-orbits of composable matrix tuples are in bijection with the
Kostant partitions of $\underline d$, the bijection sending an orbit to its rank
pattern; every orbit has the block-diagonal normal form $\bigoplus M_{ij}^{\,
m_{ij}}$; and the rank loci of Chapter 1 are the finite unions of orbits selected
by the value of $r_{0N}$.

What this part does **not** do is measure the orbits. The codimension of an orbit
closure — and hence the invariants $C$ and $\theta$ — comes from the normal slice
$\operatorname{Ext}(M, M)$ (Cor 3.5 of the paper), and which orbit closures are
components comes from the orbit-closure order (Thm 3.8). Those build directly on
the classification established here, and lead to the paper's three computations of
$(C, \theta)$ and the real-log-canonical-threshold payoff for deep linear
networks. They are the subject of the chapters beyond this part.

## Sources and cross-references

The complete invariant, the normal form, and the orbit–Kostant bijection are
Corollary 2.9 of the paper (with Theorem 2.4 for the orbit/isomorphism
identification), and Section 2 of the
[high-level overview](../paper-digest/high-level-overview.md). The formal
counterparts are `DLNFibre.Core.Orbit` (`orbit_of_rankPattern_eq`,
`rankPattern_eq_iff_orbit`, `baseChange_normalForm`) and
`DLNFibre.Core.OrbitKostant` (`orbitKostantEquiv`). The orbit-closure order
(Thm 3.8) and the $\operatorname{Ext}$ codimension (Cor 3.5) used in Example 5.2
are not yet formalised; they are cited to the paper.
