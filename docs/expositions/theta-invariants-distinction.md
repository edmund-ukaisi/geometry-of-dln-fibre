---
title: "Three Invariants Called θ: Components, Pole Order, and the Log-Log Coefficient"
status: draft
source: exposition
topics: [core-machinery, singular-learning-theory, rlcm, components, aoyagi, deep-linear-networks]
created: "2026-06-26T00:00:00"
updated: "2026-06-26T00:00:00"
---

# Three Invariants Called θ: Components, Pole Order, and the Log-Log Coefficient

For a deep linear network with true weight $B$, three integers are attached to the fibre
$\operatorname{mult}^{-1}(B)$ of the multiplication map, and all three have been written $\theta$ at
one point or another:

1. the number of top-dimensional irreducible components of $\operatorname{mult}^{-1}(B)$;
2. the real log-canonical multiplicity (rlcm) — the order of the largest pole of the loss
   function's zeta function, equivalently the singular-learning-theory multiplicity that governs
   the $\log\log n$ term of the free energy;
3. the coefficient of $\log\log n$ itself, which is the rlcm minus one.

These are three different invariants. The first two — the component count and the rlcm — coincide
when a single integer parameter $\lvert\delta\rvert$ is at most $1$, and separate once
$\lvert\delta\rvert \ge 2$; the third is always the rlcm minus one. The smallest network where all
three take distinct values is the five-layer network of constant width $2$ with true rank $0$: there
the component count is $6$, the rlcm is $5$, and the log-log coefficient is $4$.

The reason to separate them carefully is that the literature reads more unified than it is. The
component count is Lehalleur–Rimányi's $\theta$ (their $k$); the rlcm is Aoyagi's order, which Aoyagi
also writes $\theta$; and Lehalleur–Rimányi's *printed* rlcm formula is in fact the third quantity,
the log-log coefficient — it is off by one from the rlcm as those authors themselves define it. The
codimension and the $\operatorname{rlct} = \tfrac12\operatorname{codim}$ result are not touched by any
of this; the discrepancy lives entirely in the secondary multiplicity.

The story is short:

1. Set up the shifted widths $M^{(s)} = H^{(s)} - r$, the active set, and the integers
   $\ell$, $a$, $\lvert\delta\rvert$.
2. Define the three invariants and say what each one measures.
3. Give the closed forms and tabulate $(3,3,3)$ and $(2,2,2,2,2)$.
4. Separate the two precise findings: Aoyagi's order is correct; the printed Lehalleur–Rimányi
   formula is the log-log coefficient.
5. Explain the conceptual root: a component count is not a pole order, with the exact local example
   $F = xy(x-y)$.

!!! warning "Notation: two papers, one symbol θ"
    Lehalleur–Rimányi write $\theta$ (and $k$) for the **number of top-dimensional irreducible
    components**. Aoyagi writes $\theta$ for the **order of the largest pole** (the rlcm). These are
    different integers. Throughout this note $\theta$ means the component count, matching the
    repository's $\theta$ / `cTheta` / `numTop`; the pole order is written $\operatorname{rlcm}$.

## 1. Shifted widths, the active set, and the integers ℓ, a, |δ|  {: #setup}

A deep linear network of depth $N$ has layer widths $\underline d = (d_0,\dots,d_N)$. Its parameters
are the tuples $(A_1,\dots,A_N)$ of composable matrices $A_s : k^{d_{s-1}} \to k^{d_s}$, and the
function it computes is the product

$$
\operatorname{mult}(A_1,\dots,A_N) = A_N \cdots A_1.
$$

Fix a target $B$ of rank $r$ with $0 \le r \le \min_s d_s$; this is the realisable case, where
$B \in \operatorname{Im}(\operatorname{mult})$. The object of interest is the fibre
$\operatorname{mult}^{-1}(B)$ — the set of weight tuples that compute exactly $B$.

The invariants below depend on $\underline d$ and $r$ only through a few derived integers. We
introduce them in Aoyagi's reduced-and-sorted form, since the rlcm is stated there.

!!! definition "Shifted widths and the active set"
    The **shifted (reduced) widths** are

    $$
    M^{(s)} = H^{(s)} - r = d_{N+1-s} - r,
    $$

    one per layer (Aoyagi indexes the widths $H^{(s)}$ in the reverse order to Lehalleur–Rimányi's
    $d_i$; the shift by $r$ is Aoyagi's Definition 3). The **active set** $\mathcal{M}$ is a
    sub-multiset of the shifted widths, obtained by discarding the widths that are too large to bind
    — formally, a width $M^{(s)}$ is dropped when it exceeds the sum of all the others, and otherwise
    kept (Aoyagi's two summation inequalities). Set

    $$
    \ell = \operatorname{Card}(\mathcal{M}) - 1,
    \qquad
    \tilde S = \sum_{i \in \mathcal{M}} M^{(i)},
    \qquad
    M = \lceil \tilde S / \ell \rceil,
    $$

    and

    $$
    a = \tilde S - (M-1)\ell, \qquad a \in \{1,\dots,\ell\}.
    $$

    The integer $a$ is the residue of $\tilde S$ modulo $\ell$, normalised to lie in $1,\dots,\ell$.

Lehalleur–Rimányi's number of "relevant" dimensions is Aoyagi's $\ell$; we write $m = \ell$ for it,
matching the $m$ in their component-count binomial. The active set then has
$\operatorname{Card}(\mathcal{M}) = m + 1$ widths. The component count is read off one further integer.

!!! definition "The deficiency |δ|"
    With $m = \ell$ (Lehalleur–Rimányi's count of relevant dimensions), set

    $$
    \delta = \tilde S - m\left\lfloor \frac{\tilde S}{m} + \frac12 \right\rfloor,
    \qquad
    \lvert\delta\rvert = \bigl\lvert \tilde S - m\cdot\operatorname{round}(\tilde S/m) \bigr\rvert.
    $$

    So $\lvert\delta\rvert$ is the distance from $\tilde S$ to the nearest multiple of $m$. It
    measures how far the relevant widths are from being perfectly balanced: $\lvert\delta\rvert = 0$
    exactly when $m \mid \tilde S$.

The integer $\lvert\delta\rvert$ is the single dial that controls whether the three invariants agree.
It and the residue $a$ are computed from the same $\tilde S$ and the same $m = \ell$: $\lvert\delta\rvert$
is the distance from $\tilde S$ to the nearest multiple of $m$, while $a$ is $\tilde S$'s residue
modulo $m$ normalised to $\{1,\dots,m\}$. For the constant-width networks below, $(\ell, a)$ and
$\lvert\delta\rvert$ are computed together in §3.

??? note "Where the binomial comes from"
    The component count is a closest-lattice-point computation: the top-dimensional components of the
    rank-$r$ locus correspond to the lattice points nearest a fixed real point in $m$ coordinates,
    and that count is a binomial $\binom{m}{\lvert\delta\rvert}$ (Lehalleur–Rimányi, equation
    (number-of-top-components), `:1665`, with $m$ their count of relevant dimensions). The rlcm comes
    instead from Aoyagi's resolution of singularities, whose combinatorics are governed by the same
    $\ell = m$ but through the residue $a$ rather than the deficiency $\lvert\delta\rvert$. The two
    computations share the same relevant widths but extract different arithmetic from them, which is
    the first sign that the resulting integers need not coincide.

## 2. The three invariants and what each measures  {: #three-invariants}

We now state the three integers and the precise sense in which each is defined.

!!! definition "Invariant 1 — number of top-dimensional components"
    $\theta$ is the number of irreducible components of $\operatorname{mult}^{-1}(B)$ of maximal
    dimension. Geometrically: the fibre is a union of finitely many irreducible pieces, and $\theta$
    counts how many of those pieces have the largest dimension (equivalently, the smallest
    codimension $C$). This is Lehalleur–Rimányi's $\theta$ and their $k$, and it is the integer the
    Lean development computes as `cTheta` / `numTop`.

!!! definition "Invariant 2 — real log-canonical multiplicity (rlcm)"
    Let $K^{\mathrm{DLN}}_B(A_*) = \lVert \operatorname{mult}(A_*) - B \rVert_2^2$ be the squared loss,
    so that $(K^{\mathrm{DLN}}_B)^{-1}(0) = \operatorname{mult}^{-1}(B)$. The local archimedean zeta
    function $\zeta(s) = \int_U \lvert K^{\mathrm{DLN}}_B \rvert^{s}\,\mathrm{dvol}$ extends to a
    meromorphic function whose largest pole is at $s = -\operatorname{rlct}$; the **rlcm** is the
    *order* of that pole (Lehalleur–Rimányi, `:1808`). By definition $\operatorname{rlcm} \in
    \mathbb{N}$ and $\operatorname{rlcm} \ge 1$ whenever the loss has a zero. In singular learning
    theory this order is the multiplicity that produces the $(\operatorname{rlcm}-1)\log\log n$ term
    in the asymptotic free energy. Aoyagi writes this quantity $\theta$ and reads it after resolution
    as a maximum cardinality of binding divisors (Aoyagi, Theorem 1, the order
    $\theta = \max_u \operatorname{Card}\{\,j : (h_j+1)/(2k_j) = \lambda\,\}$).

!!! definition "Invariant 3 — the log-log coefficient"
    The coefficient of $\log\log n$ in the free energy expansion is $\operatorname{rlcm} - 1$. It is
    a genuine and meaningful quantity — it is what one reads off the asymptotic learning curve — but
    it is one less than the pole order, not the pole order itself.

The three are tied to the codimension as follows: the codimension $C$ and the threshold
$\operatorname{rlct} = C/2$ (Lehalleur–Rimányi, Theorem on the Aoyagi rlct, `:1891`) are the same
across both papers and are not in question here. The three integers above are the *secondary* data
sitting beside $\operatorname{rlct}$, and it is only here that the conflation occurs.

## 3. Closed forms and two worked networks  {: #formulas}

The closed forms, in the notation of §1:

| invariant | closed form | what it measures |
|---|---|---|
| $\theta$ (components) | $\dbinom{m}{\lvert\delta\rvert}$ | # top-dimensional irreducible components of $\operatorname{mult}^{-1}(B)$ |
| $\operatorname{rlcm}$ (pole order) | $a(\ell-a)+1$ | order of the largest pole of $\zeta(s)$ (Watanabe multiplicity) |
| log-log coefficient | $a(\ell-a)$ | the $\log\log n$ exponent $= \operatorname{rlcm}-1$ |

The middle formula is Aoyagi's $\theta = a(\ell-a)+1$ (Theorem 2 and its equal-width corollary). The
bottom formula $a(\ell-a)$ equals Lehalleur–Rimányi's printed expression
$m^2\{\tilde S/m\}(1-\{\tilde S/m\})$, as their own proof shows via the ceiling/floor identity
$a(\ell-a)/\ell = m\{\tilde S/m\}(1-\{\tilde S/m\})$ (`:1924`); see §4.

We compute two constant-width networks. For a network of constant width $d$ and depth $N$ with rank
$r$, every shifted width equals $d-r$ and all are relevant, so the active set has $N+1$ widths,
$m = \ell = N$, and $\tilde S = (N+1)(d-r)$.

!!! example "Three-layer constant width: (3,3,3), r = 0 — components and rlcm coincide"
    Here $N = 2$, $d - r = 3$, so the active set is $\{3,3,3\}$, $m = \ell = 2$, $\tilde S = 9$. Then
    $M = \lceil 9/2 \rceil = 5$, giving $a = 9 - (5-1)\cdot 2 = 1$, and
    $\lvert\delta\rvert = \lvert 9 - 2\cdot\operatorname{round}(9/2)\rvert = \lvert 9 - 2\cdot 5\rvert = 1$
    (here $\operatorname{round}(9/2) = \lfloor 4.5 + \tfrac12\rfloor = 5$).

    - components: $\binom{m}{\lvert\delta\rvert} = \binom{2}{1} = 2$;
    - rlcm: $a(\ell-a)+1 = 1\cdot 1 + 1 = 2$;
    - log-log coefficient: $a(\ell-a) = 1$.

    Here $\lvert\delta\rvert = 1$. The component count and the rlcm coincide at $2$; only the printed
    log-log coefficient ($1$) sits below them. This is the regime $\lvert\delta\rvert \le 1$ where
    invariants 1 and 2 agree.

!!! example "Five-layer constant width: (2,2,2,2,2), r = 0 — all three differ"
    Here $N = 4$, $d - r = 2$, so the active set is $\{2,2,2,2,2\}$, $m = \ell = 4$,
    $\tilde S = 10$. Then $M = \lceil 10/4 \rceil = 3$, giving $a = 10 - (3-1)\cdot 4 = 2$, and
    $\lvert\delta\rvert = \lvert 10 - 4\cdot\operatorname{round}(10/4)\rvert = \lvert 10 - 4\cdot 3\rvert = 2$
    (here $\operatorname{round}(10/4) = \lfloor 2.5 + \tfrac12\rfloor = 3$).

    - components: $\binom{m}{\lvert\delta\rvert} = \binom{4}{2} = 6$;
    - rlcm: $a(\ell-a)+1 = 2\cdot 2 + 1 = 5$;
    - log-log coefficient: $a(\ell-a) = 2\cdot 2 = 4$.

    Three distinct integers — $6$, $5$, $4$ — for one network. With $\lvert\delta\rvert = 2$ this is
    the smallest network on which all three invariants separate, and it is the certificate's central
    witness.

The two examples sit on either side of the threshold $\lvert\delta\rvert = 1$.

| network | $\lvert\delta\rvert$ | components $\binom{m}{\lvert\delta\rvert}$ | rlcm $a(\ell-a)+1$ | log-log $a(\ell-a)$ |
|---|---|---|---|---|
| $(3,3,3)$, $r=0$ | $1$ | $2$ | $2$ | $1$ |
| $(2,2,2,2,2)$, $r=0$ | $2$ | $6$ | $5$ | $4$ |

At $\lvert\delta\rvert = 1$ the components and the rlcm agree ($2 = 2$); at $\lvert\delta\rvert = 2$
all three values separate. This is the general pattern: the component count and the rlcm coincide
exactly when $\lvert\delta\rvert \le 1$, and differ once $\lvert\delta\rvert \ge 2$.

??? note "Why the boundary is |δ| ≤ 1"
    At $\lvert\delta\rvert = 0$ the widths are balanced ($m \mid \tilde S$), so $a = m$ and the rlcm
    is $a(m-a)+1 = m\cdot 0 + 1 = 1$, while the component count is $\binom{m}{0} = 1$. At
    $\lvert\delta\rvert = 1$ the residue is $a \in \{1, m-1\}$, so the rlcm is $a(m-a)+1 = (m-1)+1 =
    m$, while the component count is $\binom{m}{1} = m$. So both invariants equal $1$ at
    $\lvert\delta\rvert = 0$ and $m$ at $\lvert\delta\rvert = 1$. For $\lvert\delta\rvert \ge 2$ the
    binomial $\binom{m}{\lvert\delta\rvert}$ outgrows the quadratic $a(m-a)+1$, and they part. A
    direct sweep finds no exception to "$\binom{m}{\lvert\delta\rvert} = a(m-a)+1$ iff
    $\lvert\delta\rvert \le 1$" across $1 \le m \le 11$ and $\tilde S \le 6m$
    (`threads/03-theta-h1-h2/scripts/order_vs_components.py`).

The integers $m = \ell = 4$, $\tilde S = 10$, $a = 2$, $\lvert\delta\rvert = 2$ for the witness, the
systematic relation $\operatorname{rlcm} = a(\ell-a)+1$, and the values $6, 5, 4$ are all reproduced
by the verification script (`threads/03-theta-h1-h2/scripts/order_vs_components.py`).

## 4. Two precise findings  {: #findings}

### Aoyagi's order is correct

Aoyagi's order $a(\ell-a)+1$ is the genuine pole order. Three independent checks support this.

- **Internal consistency.** Aoyagi's general order definition (Theorem 1: a maximum cardinality of
  divisors achieving the minimal ratio), the closed form of Theorem 2, and the equal-width Example
  (which gives $\theta = a(L-a)+1$) all return the same integer.
- **A positive integer at the balanced point.** When $\lvert\delta\rvert = 0$ the order is
  $a(\ell-a)+1 \ge 1$, as a pole order must be. The five-layer balanced case gives $5$, never $0$.
- **Cross-check against a peer-reviewed computation.** For three-layer networks the model is
  reduced-rank regression, whose multiplicity was computed independently by Aoyagi–Watanabe (2005).
  Aoyagi's $a(\ell-a)+1$ reproduces that classical parity-governed multiplicity exactly across all
  $1127$ three-layer cases tested (including $r > 0$ and unbalanced widths), with zero mismatches
  (`threads/03-theta-h1-h2/scripts/order_vs_components.py`).

### The printed Lehalleur–Rimányi rlcm formula is the log-log coefficient

Lehalleur–Rimányi's Theorem on the Aoyagi rlct prints

$$
\operatorname{rlcm}(K^{\mathrm{DLN}}_B) = m^2\left\{\frac{\tilde S}{m}\right\}\left(1 - \left\{\frac{\tilde S}{m}\right\}\right) = a(\ell-a),
$$

at `:1895`. By those authors' own definition at `:1808`, the rlcm is the order of a pole, hence an
integer $\ge 1$ wherever the loss vanishes. But the printed expression equals $0$ whenever
$\lvert\delta\rvert = 0$ (for instance any balanced constant-width network), which a pole order can
never be. So the printed formula is not the rlcm as defined; it is the rlcm minus one — the log-log
coefficient $a(\ell-a)$.

The likely mechanism is an arithmetic slip in assembling the formula, not a mathematical error in the
underlying computation. The relevant rule is the additivity of the rlcm under sums of non-negative
functions,

$$
\operatorname{rlcm}(F+G) = \operatorname{rlcm}(F) + \operatorname{rlcm}(G) - 1
$$

(Lehalleur–Rimányi, `:1847`), whose trailing $-1$ keeps a sum of $\ell+1$ unit-order pieces at order
$a(\ell-a)+1$ rather than $a(\ell-a)$. Dropping that $+1$ at the end of the assembly produces the
printed expression. Pinpointing the exact step where the $+1$ is lost (or confirming by
correspondence) is the one open sub-question; the conclusion that the printed formula is off by one
is settled by the definition-versus-formula contradiction alone.

!!! info "Scope of the discrepancy"
    The codimension formula and the equality $\operatorname{rlct} = \tfrac12\operatorname{codim}$ —
    the headline DLN result — are unaffected. The threshold $\operatorname{rlct} = \lambda$ agrees
    exactly between the two papers; the discrepancy is confined to the secondary multiplicity beside
    it. The Lean development formalises the **component count** $\theta = \binom{m}{\lvert\delta\rvert}$
    — the theorem that `numTop` of the fibre equals `cTheta` of $\underline d - r$, axiom-clean — and
    does not assert any rlcm formula; the rlcm $= a(\ell-a)+1$ is Aoyagi's result, cited at the
    singular-learning-theory level.

## 5. Why a component count is not a pole order  {: #conceptual-root}

The conceptual root of the conflation is that there is no general dictionary sending the number of
top-dimensional irreducible components of a zero locus to the order of the largest pole of its zeta
function. The two integers are computed by different machines: the component count is read off the
variety directly, while the pole order is read after a resolution of singularities, as the maximum
number of "binding" exceptional divisors meeting in a single chart at the minimal ratio. A resolution
can merge or split the original components, so the two counts are not forced to agree.

A single exact local example carries this. Take

$$
F = xy(x-y) \quad\text{on}\quad \mathbb{R}^2.
$$

Its zero locus $V(F)$ is three distinct lines through the origin — three irreducible components, all
passing through $0$. One blow-up at the origin resolves $F$, and the largest pole of
$\int \lvert F\rvert^s$ sits at $s = -2/3$ with order $1$. So $V(F)$ has three components through the
origin but the zeta function has a largest pole of order $1$: the component count is $3$ and the
pole order is $1$. No identity relates them.

Lehalleur–Rimányi state exactly this disclaimer for the DLN fibre: there is "no simple relationship"
between the rlcm $m^2\{\tilde S/m\}(1-\{\tilde S/m\})$ and the component count
$k = \binom{m}{\lvert\delta\rvert}$ (`:1934`). The reading "number of components $=$ pole order" is
therefore not a claim of either paper; it is an inference that the worked numbers refute, and the
five-layer network of §3 is the smallest counterexample inside the DLN family itself ($6 \ne 5$).

## Sources and cross-references

- Lehalleur–Rimányi (2024), `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex`:
  rlct $= \tfrac12\operatorname{codim}$ theorem `:1891`; rlcm definition `:1808`; printed rlcm formula
  `:1895`; rlcm additivity rule `:1847`; ceiling/floor identity `:1924`; "no simple relationship"
  remark `:1934`; component count $k = \binom{m}{\lvert\delta\rvert}$ `:1665`.
- Aoyagi (2023), `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/`:
  the order $\theta = \max_u \operatorname{Card}\{\,j : (h_j+1)/(2k_j) = \lambda\,\}$ (Theorem 1,
  p. 6); shifted widths $M^{(s)} = H^{(s)}-r$, the active set, and $\ell$, $a$ (Definition 3, p. 8);
  $\lambda$ and $\theta = a(\ell-a)+1$ (Theorem 2 and the equal-width Example, p. 9).
- Aoyagi–Watanabe (2005), reduced-rank-regression multiplicity — the peer-reviewed three-layer
  cross-check.
- Expedition `2026-06-25-theta-components`: the adjudication certificate
  `threads/03-theta-h1-h2/findings.md`, the verification script
  `threads/03-theta-h1-h2/scripts/order_vs_components.py` (systematic off-by-one over all
  $(m, \tilde S \bmod m)$; $1127$-case classical cross-check; the $\lvert\delta\rvert = 0$
  impossibility), and the resolved headline in `synthesis.md`.
- Related expositions: [[high-level-overview]] (the geometry of $C$ and $\theta$);
  [[permutation-invariance-of-C-and-theta]] (the component count $\theta$ and its formula).
