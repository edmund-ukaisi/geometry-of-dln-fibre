---
title: "Rank Patterns and Kostant Partitions"
status: draft
source: exposition
topics: [core-machinery, rank-pattern, kostant-partition, inclusion-exclusion, proposition-3.1]
created: "2026-06-14"
updated: "2026-06-14"
---

# Rank Patterns and Kostant Partitions

[Chapter 3](03-gabriels-theorem-interval-modules-and-the-barcode.md) showed every
tuple is a direct sum of interval modules, recorded as a barcode. This chapter
gives two numerical records of that barcode — the **Kostant partition**, which
lists the multiplicities directly, and the **rank pattern**, which lists the
ranks of the interval compositions — and the inclusion–exclusion formula that
converts between them. Two consequences follow. The rank pattern, an invariant we
can read off any tuple by computing ranks, determines the Gabriel multiplicities;
so the decomposition of Chapter 3 is unique. And the rank patterns that arise are
exactly the cumulative transforms of Kostant partitions.

## 4.1 The rank pattern

The first record is computed directly from the matrices, with no reference to the
decomposition.

!!! definition "Definition 4.1 — The rank pattern"
    The **rank pattern** of a tuple $A_\ast$ is the upper-triangular array

    $$
    r_{ij} = \operatorname{rank}\big( A_j A_{j-1} \cdots A_{i+1} \big),
    \qquad 0 \le i \le j \le N,
    $$

    the rank of the interval composition from vertex $i$ to vertex $j$, with the
    diagonal convention $r_{ii} = d_i$ (the empty composition is the identity on
    $k^{d_i}$).

The product rank of Chapter 1 is the corner entry $r_{0N}$. By the orbit-
invariance of interval ranks (Chapter 2), the whole array $r_{ij}$ is constant
on $G_{\underline d}$-orbits, so it is an invariant of the isomorphism class.

??? info "Formalised in Lean — Core.Submult.rankPattern"

        noncomputable def rankPattern (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
            (i j : Fin (N + 1)) (hij : i ≤ j) : ℕ :=
          (submult d A i j hij).rank

        theorem rankPattern_self [Nontrivial k] (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
            (i : Fin (N + 1)) : rankPattern d A i i le_rfl = d i

    `rankPattern d A i j` is the rank of the interval composition
    `submult d A i j` (Chapter 1); `rankPattern_self` is the diagonal convention
    $r_{ii} = d_i$.

## 4.2 The Kostant partition

The second record lists the barcode multiplicities.

!!! definition "Definition 4.2 — The Kostant partition"
    Given the Gabriel decomposition
    $A_\ast \cong \bigoplus_{i \le j} M_{ij}^{\,m_{ij}}$ of Chapter 3, its
    **multiplicity array** is $\underline m = (m_{ij})_{0 \le i \le j \le N}$,
    the number of bars $[i,j]$. The array is a **Kostant partition** of
    $\underline d$ when the multiplicities recover the dimension at every vertex:

    $$
    d_k = \sum_{i \le k \le j} m_{ij}, \qquad 0 \le k \le N.
    $$

The Kostant condition is automatic for the multiplicities of a genuine barcode:
the bars alive at vertex $k$ are exactly those with $i \le k \le j$, and they
form a basis of $V_k$, so they number $d_k$. The condition is the constraint that
picks out, among all arrays of nonnegative integers, those that can be the
barcode of a tuple with dimension vector $\underline d$.

??? info "Formalised in Lean — Core.IntervalModule.multiplicityArray"

        def multiplicityArray (L : List (Fin (N + 1) × Fin (N + 1))) : ℤ → ℤ → ℤ :=
          fun a b ↦ (L.map (fun p ↦ if a = (p.1 : ℤ) ∧ b = (p.2 : ℤ) then 1 else 0)).sum

    A barcode is carried as a list `L` of interval endpoints (Chapter 3);
    `multiplicityArray L` counts how often each $(a,b)$ occurs, the array
    $\underline m$. The Kostant constraint $d_k = \sum_{i \le k \le j} m_{ij}$
    appears as a hypothesis of the rank-pattern theorem below
    (`exists_barcode_rankPattern`, the alive-bar count at $(t,t)$ equals $d_t$).

## 4.3 The two records convert: Proposition 3.1

The rank pattern is a cumulative count of the multiplicities, and the
multiplicities are recovered from the rank pattern by a second difference.

The first direction reads the rank pattern off the barcode. The composition from
$i$ to $j$ carries the thread of a bar $[a,b]$ across the whole interval $[i,j]$
exactly when the bar is alive throughout, that is $a \le i$ and $j \le b$; each
such bar contributes one to the rank, and no others contribute. So

$$
r_{ij} = \#\{\, \text{bars } [a,b] : a \le i \ \text{and}\ j \le b \,\}
       = \sum_{a \le i,\ b \ge j} m_{ab}.
$$

This is the **cumulative transform** $S$ of the array $\underline m$: $r_{ij}$
sums $m_{ab}$ over every interval $[a,b]$ containing $[i,j]$.

!!! theorem "Proposition 3.1 of the paper — the two records and their inversion"
    For any tuple with barcode multiplicities $\underline m$ and rank pattern
    $\underline r$,

    $$
    r_{ij} = \sum_{a \le i,\ b \ge j} m_{ab}
    \qquad\text{(cumulative transform)},
    $$

    and conversely

    $$
    m_{ij} = r_{ij} - r_{i,j+1} - r_{i-1,j} + r_{i-1,j+1}
    \qquad\text{(second difference)},
    $$

    with the convention that out-of-range entries are $0$. The two transforms are
    mutually inverse on arrays supported on $0 \le i \le j \le N$.

The second formula is the inclusion–exclusion that isolates the bars with
$a = i$ and $b = j$: among the bars containing $[i,j]$, subtract those containing
the longer intervals $[i, j{+}1]$ and $[i{-}1, j]$, then add back those
containing $[i{-}1, j{+}1]$ that were subtracted twice.

??? proof "Why the transforms invert (proof idea)"
    The cumulative transform $S$ is a double sum: over the lower index it sums
    $a$ from $0$ up to $i$, and over the upper index it sums $b$ from $j$ up to
    $N$. The second difference $T$ taking
    $r \mapsto r_{ij} - r_{i,j+1} - r_{i-1,j} + r_{i-1,j+1}$ factors as a
    difference in the lower index composed with a difference in the upper index.

    In one variable a difference inverts a cumulative sum by telescoping: if
    $r_i = \sum_{a \le i} m_a$ then $r_i - r_{i-1} = m_i$, using
    $m_a = 0$ for $a < 0$. The lower-index difference of $S$ collapses the
    lower-index sum to its top term, and the upper-index difference collapses the
    upper-index sum; applying both recovers $m_{ij}$. The boundary convention
    (out-of-range $= 0$) is exactly what makes the telescoping clean at the
    edges. The reverse composition $S \circ T = \mathrm{id}$ is the same
    telescoping run the other way.

??? info "Formalised in Lean — Core.RankPattern and Core.Gabriel"
    The abstract inversion (Proposition 3.1a) is an `Equiv` between supported
    arrays under the cumulative map `cumul` and the difference map `diff`:

        def diff (r : ℤ → ℤ → R) : ℤ → ℤ → R := diffRow (diffCol r)
        -- diff r i j = r i j - r i (j+1) - r (i-1) j + r (i-1) (j+1)

        noncomputable def cumul (N : ℤ) (m : ℤ → ℤ → R) : ℤ → ℤ → R := cumulRow (cumulCol N m)
        -- cumul N m i j = ∑_{k ≤ i} ∑_{j ≤ l ≤ N} m k l

        noncomputable def cumulDiffEquiv (N : ℤ) : SuppArray N R ≃ SuppArray N R

    `cumulDiffEquiv` packages `diff_cumul` and `cumul_diff` (the two telescoping
    identities) as a bijection on arrays supported off the index walls. The
    tuple-side statement (Proposition 3.1b) is that an arbitrary tuple's rank
    pattern is the cumulative count of its barcode multiplicities:

        theorem exists_barcode_rankPattern (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
            ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)),
              (∀ lam, birth lam ≤ death lam) ∧
              (∀ t, (Finset.univ.filter (fun lam ↦ birth lam ≤ t ∧ t ≤ death lam)).card = d t) ∧
              ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
                rankPattern d A i j hij
                  = (Finset.univ.filter (fun lam ↦ birth lam ≤ i ∧ j ≤ death lam)).card

    Read literally: there is a barcode whose alive-bar count at each vertex is
    $d_t$ (the Kostant constraint) and whose count of bars containing $[i,j]$ is
    $r_{ij}$ — the cumulative-transform direction, with no change of basis.

## 4.4 Uniqueness of the Gabriel decomposition

The second formula has an immediate consequence for Chapter 3. The
multiplicities $m_{ij}$ are obtained from the rank pattern $r_{ij}$ by a fixed
formula; the rank pattern is an invariant of the tuple; so the multiplicities are
an invariant of the tuple. The Gabriel decomposition is unique.

!!! theorem "Uniqueness of the Gabriel multiplicities"
    The barcode multiplicities of a tuple are determined by its rank pattern,
    through $m_{ij} = r_{ij} - r_{i,j+1} - r_{i-1,j} + r_{i-1,j+1}$. Two tuples
    with the same rank pattern have the same Gabriel multiplicities.

This completes Gabriel's theorem: Chapter 3 supplied a decomposition, and the
difference formula shows it is the only one. The uniqueness costs nothing beyond
the inversion already proved — no separate argument about indecomposables is
needed.

??? info "Formalised in Lean — Core.Gabriel.rankPattern_eq_cumul_barMult"

        theorem rankPattern_eq_cumul_barMult (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d) :
            ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)),
              Supported (N : ℤ) (barMult M birth death) ∧
              diff (cumul (N : ℤ) (barMult M birth death)) = barMult M birth death ∧
              ∀ (i j : Fin (N + 1)) (hij : i ≤ j),
                (rankPattern d A i j hij : ℤ)
                  = cumul (N : ℤ) (barMult M birth death) (i : ℤ) (j : ℤ)

    The bar-multiplicity array `barMult` satisfies `diff (cumul barMult) =
    barMult` (the inversion `diff_cumul`) and its cumulative form is the rank
    pattern, so `barMult = diff (rankPattern A)` — the multiplicities are a
    function of the rank pattern alone.

## 4.5 The running example, in both records

!!! example "Example 4.3 — Rank pattern and Kostant partition of the $(2,2,2)$ tuple"
    The rank-one tuple $A = \left(\begin{smallmatrix} 1 & 0 \\ 0 & 0
    \end{smallmatrix}\right)$, $B = \left(\begin{smallmatrix} 0 & 0 \\ 0 & 1
    \end{smallmatrix}\right)$ has interval compositions of ranks

    $$
    r =
    \begin{pmatrix}
    r_{00} & r_{01} & r_{02} \\
           & r_{11} & r_{12} \\
           &        & r_{22}
    \end{pmatrix}
    =
    \begin{pmatrix}
    2 & 1 & 0 \\
      & 2 & 1 \\
      &   & 2
    \end{pmatrix},
    $$

    where $r_{01} = \operatorname{rank} A = 1$, $r_{12} = \operatorname{rank} B =
    1$, $r_{02} = \operatorname{rank} BA = 0$, and the diagonal is $\underline d =
    (2,2,2)$. Applying the second-difference formula (out-of-range entries $0$):

    $$
    m_{00} = r_{00} - r_{01} = 1, \quad
    m_{01} = r_{01} - r_{02} = 1, \quad
    m_{02} = r_{02} = 0,
    $$

    $$
    m_{11} = r_{11} - r_{12} - r_{01} + r_{02} = 0, \quad
    m_{12} = r_{12} - r_{02} = 1, \quad
    m_{22} = r_{22} - r_{12} = 1.
    $$

    So $\underline m$ has $m_{00} = m_{01} = m_{12} = m_{22} = 1$ and the rest
    $0$ — the multiplicities of $M_{00} \oplus M_{01} \oplus M_{12} \oplus
    M_{22}$ found by tracing threads in Example 3.3. The Kostant condition holds:
    each vertex is covered by exactly two of these bars. (This is the
    inclusion–exclusion of the Lean non-vacuity witness `mWitness`.)

!!! question "Checkpoint"
    Use the cumulative transform to recover $r_{12}$ from the multiplicities
    $m_{00} = m_{01} = m_{12} = m_{22} = 1$ above.

??? tip "Solution"
    $r_{12} = \sum_{a \le 1,\ b \ge 2} m_{ab}$ counts the bars with $a \le 1$ and
    $b \ge 2$. Among $[0,0], [0,1], [1,2], [2,2]$ only $[1,2]$ qualifies ($a = 1
    \le 1$ and $b = 2 \ge 2$), so $r_{12} = 1$, matching the array.

## Sources and cross-references

The rank pattern, the Kostant partition, and the inclusion–exclusion inversion
are Section 3 of the paper (Proposition 3.1) and Section 3 of the
[high-level overview](../paper-digest/high-level-overview.md). The abstract
inversion is formalised in `DLNFibre.Core.RankPattern` (`cumulDiffEquiv`), the
tuple-side cumulative-transform direction and the uniqueness consequence in
`DLNFibre.Core.Gabriel` (`exists_barcode_rankPattern`,
`rankPattern_eq_cumul_barMult`), and the constructed-direct-sum side in
`DLNFibre.Core.IntervalModule` (`rankPattern_intervalDirectSum_eq_cumul`).

The next chapter assembles these into the classification: the rank pattern is a
**complete** invariant, so it determines the orbit, and the orbits are in
bijection with the realizable rank patterns — equivalently the Kostant
partitions of $\underline d$.
