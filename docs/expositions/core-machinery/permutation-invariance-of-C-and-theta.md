---
title: "Permutation Invariance of C and θ"
status: draft
source: exposition
topics: [core-machinery, permutation-invariance, corollary-5.10, poincare-series, q-series, theorem-5.5]
created: "2026-06-22"
updated: "2026-06-22"
---

# Permutation Invariance of C and θ

Fix a dimension vector $\underline d = (d_0,\dots,d_N)$ and a product rank $r$. The rank-$\le r$
locus $\overline{\Sigma}{}^r_{\underline d}$ — the tuples whose full composition $A_N\cdots A_1$ has
rank at most $r$ — has a codimension $C$ and a number $\theta$ of top-dimensional irreducible
components. The classification
([Chapter 5](05-the-classification-orbits-and-kostant-partitions.md)) makes both combinatorial: each
is read off the finite set of Kostant partitions of $\underline d$. This chapter proves Corollary
5.10 of the paper: $C$ and $\theta$ depend only on the **multiset** $\{d_0,\dots,d_N\}$, so permuting
the entries of $\underline d$ leaves them unchanged.

The statement is not the obvious one. The number of orbits is not permutation invariant; the whole
distribution of orbit codimensions is not permutation invariant; the total number of irreducible
components is not permutation invariant. Only the two extremal quantities — the smallest codimension
$C$ and the count $\theta$ of orbits achieving it — are. The proof here is self-contained, using none
of the equivariant cohomology the paper invokes.

The story is short:

1. $C$ and $\theta$ are the lowest-degree data of one generating function $Q^r_{\underline d}(q)$.
2. That generating function is not symmetric orbit-by-orbit — there is no Kostant-partition bijection
   to move the data across a permutation.
3. A symmetric closed form for $Q^r_{\underline d}$ (Theorem 5.5) makes the invariance one line.
4. The closed form is an inversion of one classical identity (Theorem 5.6, the "fivegon"), reproved
   here from scratch.

## 1. The combinatorial $C$ and $\theta$

The orbits whose full composition has rank exactly $r$ are indexed by the **Kostant partitions**
$m \in M^+_{\underline d, r}$: multiplicity arrays $m_{ij} \ge 0$ over intervals $0 \le i \le j \le N$
with

$$
d_k = \sum_{i \le k \le j} m_{ij} \quad\text{for every } k,
\qquad\text{and corner } m_{0N} = r.
$$

Each $m$ records how many interval modules $M_{ij}$ (a one-dimensional line living on vertices
$i,\dots,j$) occur in the orbit's normal form; the corner $m_{0N}$ counts the lines spanning all of
$0,\dots,N$, which is the rank of the full composition. The closure of the orbit named by $m$ is an
irreducible piece of $\overline{\Sigma}{}^r_{\underline d}$, of codimension

$$
\operatorname{codimForm}(m) \;=\; \sum_{1 \le i \le u \le j \le v \le N} m_{i-1,\,j-1}\, m_{u,v}.
$$

This is the $\operatorname{Ext}$-pairing form of the classification — the dimension of
$\operatorname{Ext}^1$ between the interval modules, which is the codimension of the orbit.

!!! definition "The combinatorial invariants"
    $$
    C \;=\; \operatorname{cCodim}(\underline d, r) \;=\; \min_{m \in M^+_{\underline d, r}}
    \operatorname{codimForm}(m),
    \qquad
    \theta \;=\; \operatorname{numTop}(\underline d, r) \;=\;
    \#\{\, m : \operatorname{codimForm}(m) = C \,\}.
    $$

    $C$ is the codimension of $\overline{\Sigma}{}^r_{\underline d}$ — the smallest orbit codimension
    — and $\theta$ counts the orbits that achieve it, the top-dimensional components.

For example, take $\underline d = (2,2,2)$ at $r = 0$ (the zero-product locus $A_2 A_1 = 0$). There
are six Kostant partitions, with codimensions $\{3,4,4,5,5,8\}$; the minimum $3$ is attained once, so
$C = 3$ and $\theta = 1$. Raising the rank to $r = 1$ gives $C = 1$ and $\theta = 2$ — the same as the
zero-product locus of $\underline d = (1,1,1)$, where $a_2 a_1 = 0$ splits into the two hyperplanes
$\{a_1 = 0\}$ and $\{a_2 = 0\}$.

??? info "Formalised in Lean — Core.CTheta"

        noncomputable def cCodim (d : Fin (N + 1) → ℕ) (r : ℕ)
            (h : (kostantPartitions d r).Nonempty) : ℤ :=
          (kostantPartitions d r).inf' h (fun m ↦ codimForm N (extendℤ m))

        noncomputable def numTop (d : Fin (N + 1) → ℕ) (r : ℕ)
            (h : (kostantPartitions d r).Nonempty) : ℕ :=
          ((kostantPartitions d r).filter (fun m ↦ codimForm N (extendℤ m) = cCodim d r h)).card

        theorem cCodim_d222_zero : cCodim d222 0 _ = 3   -- numTop_d222_zero : … = 1
        theorem cCodim_d222_one  : cCodim d222 1 _ = 1   -- numTop_d222_one  : … = 2

    `kostantPartitions d r` is the finite set of Kostant arrays; `codimForm` is the
    $\operatorname{Ext}$ form above. The $(2,2,2)$ values are checked by axiom-clean kernel `decide`.
    Sorry-free.

## 2. The Poincaré series, and why a bijection cannot work

The two invariants are the lowest-degree data of a single generating function. Let
$P_s = \prod_{k=1}^s (1-q^k)^{-1}$ be the partition factor and $P_m = \prod_{i \le j} P_{m_{ij}}$.

!!! definition "The Poincaré series of the locus"
    $$
    Q^r_{\underline d}(q) \;=\; \sum_{m \in M^+_{\underline d, r}}
    q^{\operatorname{codimForm}(m)}\, P_m.
    $$

Each $P_m$ has constant term $1$ and non-negative coefficients, so the lowest power of $q$ in
$Q^r_{\underline d}$ is $C$ and its coefficient there is $\theta$ — no cancellation can occur.

!!! lemma "Reading $(C,\theta)$ off the series"
    $$
    Q^r_{\underline d}(q) \;=\; \theta\, q^{C} \;+\; (\text{higher order}).
    $$

    Two dimension vectors with equal Poincaré series therefore have equal $C$ and equal $\theta$.

This reduces the goal to one identity: $Q^r_{\sigma \underline d} = Q^r_{\underline d}$. One would
like to prove it by a bijection $M^+_{\underline d, r} \to M^+_{\sigma \underline d, r}$ preserving
$\operatorname{codimForm}$. No such bijection exists — the two Kostant sets usually differ in size.

Consider the multiset $\{2,2,3\}$ at $r = 0$. Its three orderings give:

| Ordering of $\{2,2,3\}$ | Orbits $\lvert M^+_{\underline d,0}\rvert$ | Codimension multiset | $(C,\theta)$ |
|---|---|---|---|
| $(2,2,3)$ | $6$ | $4,4,6,6,7,10$ | $(4,2)$ |
| $(2,3,2)$ | $8$ | $4,4,5,6,6,8,8,12$ | $(4,2)$ |
| $(3,2,2)$ | $6$ | $4,4,6,6,7,10$ | $(4,2)$ |

The orbit count is $6$, $8$, $6$ — not invariant. The full codimension multiset is not invariant
either: the middle ordering has eight orbits against the others' six. Only the bottom of each multiset
agrees: every ordering begins $4,4,\dots$, giving $C = 4$ and $\theta = 2$. So the invariance is a
coincidence of the extremal data, not a correspondence of orbits, and the only available handle is
the generating function $Q^r_{\underline d}$ itself.

## 3. The symmetric closed form

The generating function has a closed form in which the dependence on $\underline d$ is manifestly
through the multiset alone.

!!! theorem "Theorem 5.5 of the paper (Poincaré series formula)" {: #thm-5-5}
    With $\operatorname{alt}_s = (-1)^s\, q^{\binom{s}{2}}\, P_s$ and $\mu = \min_i d_i$,

    $$
    Q^r_{\underline d}(q) \;=\; P_r \sum_{s=0}^{\mu - r} \operatorname{alt}_s
    \prod_{i=0}^{N} P_{\,d_i - r - s}.
    $$

    The only $\underline d$-dependent factor is $\prod_i P_{d_i - r - s}$, a product over the entries,
    hence a function of the multiset $\{d_i\}$ alone.

Everything else is multiset data: $P_r$ and each $\operatorname{alt}_s$ carry no $\underline d$, and
the summation range $0 \le s \le \mu - r$ depends on $\underline d$ only through $\mu = \min_i d_i$.
The invariance follows.

!!! corollary "Corollary 5.10 of the paper (permutation invariance)" {: #cor-5-10}
    For every permutation $\sigma$ and every $r \le \min_i d_i$,

    $$
    Q^r_{\sigma \underline d} = Q^r_{\underline d},
    \qquad\text{hence}\qquad
    C(\sigma \underline d, r) = C(\underline d, r),
    \quad \theta(\sigma \underline d, r) = \theta(\underline d, r).
    $$

This is the $(C,\theta) = (4,2)$ coincidence of the table above, now accounted for: across the three
orderings of $\{2,2,3\}$ the orbits and their codimensions rearrange, but the symmetric form fixes
the series, and with it the bottom degree and its coefficient.

??? proof "From the closed form to the invariance"
    Apply Theorem 5.5 to $\sigma \underline d$. The prefactor $P_r$ and each $\operatorname{alt}_s$
    carry no $\underline d$; the range $0,\dots,\min_i d_i - r$ is unchanged because $\min$ is
    symmetric; and $\prod_i P_{(\sigma \underline d)_i - r - s} = \prod_i P_{d_i - r - s}$ since the
    product is reindexed by $\sigma$. So $Q^r_{\sigma \underline d} = Q^r_{\underline d}$ term by
    term, and the lemma of §2 transfers the equality to $C$ and $\theta$.

??? info "Formalised in Lean — Core.QSeriesThm55, Core.CThetaPermInvariance"

        theorem thm55 (d : Fin (N + 1) → ℕ) (r : ℕ) (hr : ∀ k, r ≤ d k) :
            Qseries d r
              = P r * ∑ s ∈ Finset.range (minDim d - r + 1), altP s * Pmult (dminus d (r + s))

        theorem cCodim_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ)
            (hr : ∀ k, r ≤ d k) (h h') : cCodim (d ∘ σ) r h = cCodim d r h'
        theorem numTop_comp_perm (σ : Equiv.Perm (Fin (N + 1))) (d : Fin (N + 1) → ℕ) (r : ℕ)
            (hr : ∀ k, r ≤ d k) (h h') : numTop (d ∘ σ) r h = numTop d r h'

    `altP s = (-1)^s · X^(s*(s-1)/2) · P s` is $\operatorname{alt}_s$; `Pmult (dminus d c)` is
    $\prod_i P_{d_i - c}$. `Qseries_comp_perm` derives $Q^r_{\sigma\underline d} = Q^r_{\underline d}$
    from `thm55` and the symmetry of `Pmult`; the extraction bridge then gives `cCodim_comp_perm` /
    `numTop_comp_perm`. The hypothesis `hr` is $r \le \min_i d_i$, the range where $(C,\theta)$ are
    defined. No Kostant-set bijection is used. Sorry-free and axiom-clean
    `[propext, Classical.choice, Quot.sound]`.

## 4. The closed form rests on one identity

Theorem 5.5 is an inversion of a more basic identity: the **fivegon** (Theorem 5.6 of the paper,
originally Rimányi–Weber–Yong), which collapses the corner-summed Poincaré series to a pure product.

!!! theorem "Theorem 5.6 of the paper (the fivegon)"
    $$
    \sum_{m \in M^+_{\underline d}} q^{\operatorname{codimForm}(m)}\, P_m
    \;=\; \prod_{i=0}^{N} P_{d_i}.
    $$

    Summing $Q^r_{\underline d}$ over all corners $r$ gives the product $\prod_i P_{d_i}$.

The right-hand side is symmetric, but a symmetric sum need not have symmetric summands, so the fivegon
alone does not give per-$r$ invariance. The work of Theorem 5.5 is to invert the fivegon corner by
corner. Two ingredients do it:

- a **corner shift** $Q^s_{\underline d} = P_s \cdot Q^0_{\underline d - s}$ (peeling the
  full-length lines off the corner), which turns the fivegon into
  $\prod_i P_{d_i} = \sum_s P_s\, Q^0_{\underline d - s}$ — a triangular system in the corner;
- an **inverse-Pochhammer orthogonality** that solves that system:

    $$
    \sum_{k=0}^{u} \operatorname{alt}_k\, P_{u-k} \;=\; [\,u = 0\,].
    $$

The orthogonality is the only classical $q$-series input, and it needs no $q$-binomial machinery: it
is a one-variable induction on $u$ from the single recurrence $P_m\,(1-q^m) = P_{m-1}$.

??? proof "The inversion (sketch)"
    Substituting the corner shift into the fivegon gives
    $\prod_i P_{d_i} = \sum_s P_s\, Q^0_{\underline d - s}$. Form
    $\sum_s \operatorname{alt}_s \prod_i P_{d_i - s}$, expand each $\prod_i P_{d_i - s}$ by the same
    relation, reindex the double sum by $u = s + t$, and collapse the inner sum with the orthogonality
    $\sum_k \operatorname{alt}_k P_{u-k} = [u=0]$. Only $Q^0_{\underline d}$ survives — Theorem 5.5 at
    $r = 0$; the corner shift at $\underline d - r$ gives general $r$.

??? info "Formalised in Lean — Core.QSeriesFivegon, Core.QSeriesShift, Core.QSeriesOrth"

        theorem fivegon (d : Fin (N + 1) → ℕ) : fivegonSum d = Pmult d
        theorem sum_Qseries_eq_Pmult (d) :
            ∑ r ∈ Finset.range (d 0 + 1), Qseries d r = Pmult d
        def orthSum (u : ℕ) : ℤ⟦X⟧ := ∑ k ∈ Finset.range (u + 1), altP k * P (u - k)
        theorem orth (u : ℕ) : orthSum u = if u = 0 then 1 else 0

    `fivegon` is Theorem 5.6, reproved by a peeling induction on $N$: the last column transfers via the
    $N = 1$ Durfee identity (`durfee`) glued by an exponent split. `orth` is the orthogonality, a
    single-variable induction on the landed `P_mul_one_sub_succ`. All sorry-free and axiom-clean.

## 5. A zero-cited $q$-series engine

The paper proves Corollary 5.10 through the equivariant cohomology of the rank loci. The
formalisation does not: it builds the generating-function machinery directly. Mathlib v4.29 has no
$q$-Pochhammer, $q$-binomial, or $q$-Vandermonde, so the whole engine — the factors $P_s$, $P_m$,
$Q^r_{\underline d}$; the $N=1$ Durfee identity; the corner shift; the inverse-Pochhammer
orthogonality — is built from `Finset` and `PowerSeries` primitives. The step that looked to need a
$q$-binomial library (the inversion) needs only the one-variable orthogonality induction. The
invariance is thus obtained by elementary means: a generating-function identity read for its
lowest-degree data.

## 6. The geometric reading

The combinatorial $\operatorname{cCodim}$ and $\operatorname{numTop}$ are tied to the variety by the
classification: over an algebraically closed field of characteristic zero,
$\operatorname{cCodim}(\underline d, r)$ is the codimension of $\overline{\Sigma}{}^r_{\underline d}$
and $\operatorname{numTop}(\underline d, r)$ is its number of top-dimensional irreducible components.
The permutation invariance therefore transfers to these genuine geometric invariants.

!!! corollary "Geometric permutation invariance"
    The codimension of $\overline{\Sigma}{}^r_{\underline d}$ and its number of top-dimensional
    irreducible components depend only on the multiset $\{d_i\}$.

??? info "Formalised in Lean — Core.CThetaGeometricPerm"

        theorem geomCodim_comp_perm [IsAlgClosed k] [CharZero k]
            (σ : Equiv.Perm (Fin (N + 1))) (d) (r) (hr : ∀ j, r ≤ d j) (h h') :
            (codimRepCanonical (productRankLocusLE (d ∘ σ) r)).toNat
              = (codimRepCanonical (productRankLocusLE d r)).toNat

        theorem ncard_topComponents_comp_perm [IsAlgClosed k] [CharZero k]
            (σ) (d) (r) (hr : ∀ j, r ≤ d j) (h h') :
            (topComponents (d ∘ σ) r h).ncard = (topComponents d r h').ncard

    Both are unconditional, composing the geometric bridges
    (`codimRepCanonical_productRankLocusLE_eq_cCodim`, `numTop_eq_ncard_topComponents`) with the
    combinatorial `cCodim_comp_perm` / `numTop_comp_perm`. Here `productRankLocusLE d r` is the closed
    rank-$\le r$ locus $\overline{\Sigma}{}^r$.

!!! warning "Scope of the claim"
    These results name the **combinatorial and geometric** invariants $C$ and $\theta$. They are not a
    statement about the real log-canonical threshold. The reading $\operatorname{rlct} = \tfrac12
    \cdot \operatorname{codim}$ rests on a separate analytic bound and stays **cited** (Aoyagi /
    Watanabe); nothing in this chain is named `rlct`.

## Sources and cross-references

This is Section 5 of the paper (the Poincaré-series formula and Corollary 5.10), with Theorem 5.6 the
Rimányi–Weber–Yong fivegon. It builds on the classification
([Chapter 5](05-the-classification-orbits-and-kostant-partitions.md)) and on the $(C,\theta)$
invariants surveyed in [the high-level overview](../paper-digest/high-level-overview.md) (Section 7).
The formal counterparts are `DLNFibre.Core.CTheta` (the combinatorial $(C,\theta)$),
`Core.QSeries` / `QSeriesExtraction` (the series and the $(C,\theta)$ extraction),
`QSeriesFivegon` / `QSeriesShift` / `QSeriesOrth` / `QSeriesThm55` (the fivegon and Theorem 5.5),
`CThetaPermInvariance` (Corollary 5.10), and `CThetaGeometricPerm` (the geometric reading). The
$\operatorname{rlct}$ payoff is cited to Aoyagi / Watanabe and is not part of this chain.
