---
title: "Composable Matrix Chains and the Type-A Quiver Classification"
status: draft
source: exposition
topics: [core-machinery, quiver-representations, gabriel, rank-pattern, kostant, orbit-classification]
created: "2026-06-15"
updated: "2026-06-15"
---

# Composable Matrix Chains and the Type-A Quiver Classification

Multiply a chain of matrices and ask the most naive question: when is the
product zero?

For two scalars $a_1, a_2$ the answer is the one every schoolchild knows:
$a_2 a_1 = 0$ forces $a_1 = 0$ or $a_2 = 0$. The solution set is two lines
crossing at the origin. Now replace the scalars by $2 \times 2$ matrices $A, B$
and ask again when $BA = 0$. "One factor vanishes" is no longer the answer. The
set $\{BA = 0\}$ breaks into three pieces, and the largest is neither $\{A=0\}$
nor $\{B=0\}$: it is the family where $A$ and $B$ both have rank one, arranged so
that the image of $A$ lies in the kernel of $B$. That family is bigger — it has
dimension $5$ inside the $8$-dimensional space of pairs, against dimension $4$
for each of $\{A=0\}$ and $\{B=0\}$.

So the cheap question already has structure the schoolchild's answer misses.
"$BA = 0$" is not a condition on $A$ or on $B$ alone; it is a condition on how
the image of one sits inside the kernel of the other, and the dominant way to
arrange that is for both to degenerate together. As the matrices grow and the
chain lengthens, these incidences multiply, and counting them by hand becomes
hopeless. The purpose of this exposition is the machine that counts them: a
finite classification of chains of matrices up to change of basis, from which
the number and the sizes of these families can be read off.

We work over an arbitrary field $k$. The classification is network-free — it
mentions deep linear networks only as the reason anyone computed it; the loss
function and its singularity invariant come in a later part and are not used
here. The results are those of **Lehalleur and Rimányi (2024)**, Sections 2–3;
this is a self-contained account of them, and each central definition and
theorem is formalised in the Lean library `DLNFibre.Core` (the collapsible
"Formalised" notes give the declarations).

The road is short. We set up the space of chains and the loci we care about
(§1); we observe that coordinates are a distraction and reduce to a
classification up to a group of base changes (§2); we show every chain is a
stack of elementary one-dimensional threads (§3, Gabriel's theorem); we read the
stack in two ways — by visible ranks and by hidden thread-counts — and relate
them by inclusion–exclusion (§4); and we prove the visible data determines the
chain, which is the classification (§5). A single example, two $2\times2$
matrices, runs through all five.

## 1. The space of chains, and the families inside it

Fix the shapes. A **dimension vector** is a list of nonnegative integers
$\underline d = (d_0, d_1, \ldots, d_N)$, and a **composable tuple** with this
shape is a chain of linear maps

$$
k^{d_0} \xrightarrow{\ A_1\ } k^{d_1}
\xrightarrow{\ A_2\ } \cdots
\xrightarrow{\ A_N\ } k^{d_N},
$$

one matrix $A_i$ of size $d_i \times d_{i-1}$ per arrow. We write
$A_\ast = (A_1, \ldots, A_N)$ for the whole chain — the subscript $\ast$ is a
reminder that it is the list, not one matrix — and call the space of all of them
$\operatorname{Rep}_{\underline d}$. It is an affine space: a point is just a
choice of all the matrix entries, $\sum_i d_i d_{i-1}$ of them. Nothing
interesting lives in the space itself; the interest is in one map defined on it
and the subsets that map cuts out.

The map is **multiplication**, which reads off the composite of the chain:

$$
\operatorname{mult}(A_\ast) = A_N A_{N-1} \cdots A_1,
\qquad
\operatorname{mult} \colon \operatorname{Rep}_{\underline d}
\longrightarrow \operatorname{Mat}_{d_N, d_0}(k).
$$

Its entries are polynomials in the entries of the $A_i$, so the sets we now cut
out are algebraic. The **zero-product locus** is $\Sigma^0_{\underline d} =
\{A_\ast : \operatorname{mult}(A_\ast) = 0\}$; more generally the **product-rank
loci**

$$
\Sigma^{r}_{\underline d} = \{A_\ast : \operatorname{rank}(A_N \cdots A_1) = r\},
\qquad
\overline{\Sigma}^{\,r}_{\underline d} = \{A_\ast : \operatorname{rank}(A_N \cdots A_1) \le r\},
$$

and the **fibers** $\operatorname{mult}^{-1}(B) = \{A_\ast : A_N \cdots A_1 = B\}$
over a fixed target matrix $B$.

The bar in $\overline{\Sigma}^{\,r}$ is a closure: $\{\operatorname{rank} \le r\}$
is the Zariski-closed set the determinant-minors cut out, and it is the closure
of $\{\operatorname{rank} = r\}$. The closed part of that is elementary, and
worth seeing once, because it is the basic fact about how rank behaves in
families.

??? proof "Rank drops in the limit, but never jumps"
    The product $\operatorname{mult}(A_\ast)$ is a matrix of polynomials in the
    entries of $A_\ast$. For any matrix $M$, the condition
    $\operatorname{rank} M \ge s$ says some $s \times s$ minor is nonzero, and a
    minor is a polynomial. So $\{\operatorname{rank}\operatorname{mult} \ge s\}$
    is where one of finitely many polynomials is nonzero — a Zariski-open set,
    and its complement $\{\operatorname{rank} \le s-1\}$ is closed.

    The same minors say rank cannot jump up in a limit. Suppose a family
    $A_\ast(t)$ tends to $A_\ast(0)$ with product rank $\rho$ for every $t \ne 0$
    near $0$. If the limit had rank $\ge \rho+1$, some $(\rho{+}1)$-minor would be
    nonzero at $t=0$, hence nonzero for small $t \ne 0$ by continuity, forcing
    rank $\ge \rho+1$ there too — against rank $= \rho$. So the limit can only
    lose rank. (That $\{\operatorname{rank}=r\}$ is in fact *dense* in
    $\{\operatorname{rank} \le r\}$ — the other half of "closure" — is not
    elementary; it comes from the orbit-closure order, Lehalleur–Rimányi,
    Theorem 3.8, and we take it from there.)

The two numbers we want, for these loci, are the **codimension** $C$ of the
top-dimensional (largest) irreducible components and the **number** $\theta$ of
those top components. For two $2\times 2$ matrices we already saw $C = 3$ and
$\theta = 1$ (the one rank-one-image-in-kernel family). Computing $C$ and
$\theta$ in general is the destination of the later parts; this part builds the
classification they rest on, and does not compute them.

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
    interval compositions of §4, $A_j \cdots A_{i+1}$, are `Core.Submult.submult
    i j`, with `mult_eq_submult` identifying `mult` as the case $0 \to N$. The
    invariants $C, \theta$ are not yet formalised; they name the target.

## 2. Coordinates are a distraction

A chain of maps does not care what basis we write its spaces in. If we change
basis at each vertex by an invertible matrix $P_i$, the chain

$$
k^{d_0} \xrightarrow{\ A_1\ } \cdots \xrightarrow{\ A_N\ } k^{d_N}
$$

becomes the chain with maps $P_i A_i P_{i-1}^{-1}$ — the same maps seen through
new windows. Collect one invertible matrix per vertex into

$$
G_{\underline d} = \operatorname{GL}_{d_0} \times \operatorname{GL}_{d_1}
\times \cdots \times \operatorname{GL}_{d_N},
$$

the **base-change group**, acting on $\operatorname{Rep}_{\underline d}$ by

$$
(P \cdot A_\ast)_i = P_i \, A_i \, P_{i-1}^{-1}.
$$

Two chains in the same $G_{\underline d}$-orbit are the same chain in different
coordinates. The whole problem is to understand these orbits, because every
question we care about is a question about them.

It is worth naming the language, because it is standard and we will keep using
it. A directed graph — vertices and arrows — together with a vector space at
each vertex and a linear map along each arrow is called a **representation of a
quiver** ("quiver" being the word for the directed graph in this trade). Our
graph is the simplest connected one with a sense of direction: a single path

$$
0 \longrightarrow 1 \longrightarrow \cdots \longrightarrow N
$$

with every arrow pointing forward. A path graph on $N+1$ vertices is the Dynkin
diagram called $A_{N+1}$, and "all arrows the same way" is **equioriented**, so
our chains are the **representations of the equioriented type-$A$ quiver**. A
base change $P$ is exactly an isomorphism of such representations — an invertible
map at each vertex commuting with the arrows — so *orbit* and *isomorphism class*
are the same partition of $\operatorname{Rep}_{\underline d}$. This identification
is Lehalleur–Rimányi, Theorem 2.4; in our setup it is built into the definitions.

The one fact we extract now is that ranks survive the change of windows. The
composite of a base-changed chain, from vertex $i$ to vertex $j$, telescopes:

$$
(P_j A_j P_{j-1}^{-1})(P_{j-1} A_{j-1} P_{j-2}^{-1}) \cdots (P_{i+1} A_{i+1} P_i^{-1})
= P_j \,(A_j \cdots A_{i+1})\, P_i^{-1},
$$

every interior $P_m^{-1} P_m$ cancelling. Multiplying by invertible matrices on
either side leaves rank unchanged, so:

> **The rank of every interval composition $A_j \cdots A_{i+1}$ is constant on
> $G_{\underline d}$-orbits.** In particular the product rank
> $\operatorname{rank}\operatorname{mult}(A_\ast)$ is. Hence each locus
> $\Sigma^r_{\underline d}$ and $\overline\Sigma^{\,r}_{\underline d}$ is a union
> of whole orbits.

That last sentence is the first real gain: a locus defined by one polynomial
condition is assembled out of orbits. If the orbits are few, the union is a
finite, combinatorial object. They are few — that is the next section.

??? info "Formalised in Lean — the action (`Core.BaseChange`)"

        abbrev BaseChangeGroup (d : Fin (N + 1) → ℕ) : Type u :=
          ∀ v : Fin (N + 1), (Matrix (Fin (d v)) (Fin (d v)) k)ˣ

        def baseChange (P : BaseChangeGroup d) (A : Tuple d) : Tuple d :=
          fun i ↦ Units.val (P i.succ) * A i * Units.val ((P i.castSucc)⁻¹)

        theorem rankPattern_baseChange (P) (A) (i j) (hij : i ≤ j) :
            rankPattern d (baseChange P A) i j hij = rankPattern d A i j hij

    The telescoping identity is `submult_baseChange`; the rank consequence
    `rankPattern_baseChange` uses that a unit-determinant factor preserves
    `Matrix.rank`. (`rankPattern d A i j` is the rank of $A_j\cdots A_{i+1}$, §4.)

## 3. Every chain is a stack of threads

What is the simplest possible chain? A single one-dimensional thread that is
born at some vertex $i$, carried forward unchanged through the arrows, and dies
after some vertex $j$:

$$
0 \to \cdots \to 0 \to
\underset{i}{k} \xrightarrow{\,1\,} k \xrightarrow{\,1\,} \cdots
\xrightarrow{\,1\,} \underset{j}{k} \to 0 \to \cdots \to 0.
$$

It is one-dimensional on the interval $[i,j]$, zero outside, and the identity
along the interval. Call it the **interval module** $M_{ij}$. There is one for
each $0 \le i \le j \le N$. The longest, $M_{0N}$, is a single thread surviving
the entire chain; the shortest, $M_{ii}$, a single vector at vertex $i$ that the
next arrow kills.

Chains add by stacking — put two chains side by side and the maps become
block-diagonal. So from the interval modules we can build, for any choice of
multiplicities $m_{ij} \ge 0$, the block chain $\bigoplus_{i \le j}
M_{ij}^{\,m_{ij}}$. Gabriel's theorem, for our quiver, says these are *all* the
chains.

!!! theorem "Gabriel's theorem for the equioriented type $A$ (Lehalleur–Rimányi, Theorem 2.5)"
    Every chain is isomorphic to a stack of interval modules:

    $$
    A_\ast \;\cong\; \bigoplus_{0 \le i \le j \le N} M_{ij}^{\,m_{ij}}.
    $$

    Equivalently, every chain is base-change-equivalent to a block-diagonal one
    built from threads.

The picture this paints is a **barcode**: the chain is a stack of horizontal
bars, one bar $[i,j]$ for each thread, and at each vertex the bars alive there
(those with $i \le \text{vertex} \le j$) give a basis of that vertex's space. The
arrows shift each alive thread one step along its bar, or kill it at the end.

Take the running example — the rank-one pair $A = \left(\begin{smallmatrix} 1 & 0
\\ 0 & 0\end{smallmatrix}\right)$, $B = \left(\begin{smallmatrix} 0 & 0 \\ 0 &
1\end{smallmatrix}\right)$ with $BA = 0$ — and trace the standard basis through
the chain $k^2 \xrightarrow{A} k^2 \xrightarrow{B} k^2$:

```
            vertex 0      vertex 1      vertex 2
  e1 :        •─────────────•                        bar [0,1]   (M01)
  e2 :        •                                      bar [0,0]   (M00)
              (new at 1)    •─────────────•          bar [1,2]   (M12)
              (new at 2)                  •          bar [2,2]   (M22)
```

The first basis vector $e_1$ travels $0 \to 1$ ($A e_1 = e_1$) and then dies
($B e_1 = 0$): a bar $[0,1]$. The vector $e_2$ dies at once ($A e_2 = 0$): a bar
$[0,0]$. At vertex $1$, the direction $e_2$ is not reached from below but $B$
carries it to vertex $2$: a bar $[1,2]$. At vertex $2$, the direction $e_1$ is
not reached: a bar $[2,2]$. So

$$
(A, B) \;\cong\; M_{00} \oplus M_{01} \oplus M_{12} \oplus M_{22},
$$

four threads, and each vertex carries exactly two of them — the dimension check.

How is Gabriel's theorem proved? By peeling one thread at a time. Pick a vertex
where a thread can start and follow it as far forward as the arrows allow; its
span is an interval module, and — this is the work — it splits off as a direct
summand, leaving a chain of strictly smaller total dimension to which the same
argument applies. The single forward direction of the equioriented type $A$ is
exactly what lets the complement be chosen vertex by vertex in one pass; for a
general quiver no such thing is true, and Gabriel's theorem is a deeper
statement. Mathlib had no type-$A$ Gabriel theorem, so this existence half was
built from nothing, first for an abstract chain of vector spaces and then
transported to matrices.

??? info "Formalised in Lean — interval modules and Gabriel existence"
    The interval module and its block sums (`Core.IntervalModule`):

        def intervalModule (i j : Fin (N + 1)) : Tuple (intervalDim i j) :=
          fun t _ _ ↦ if intervalActive i j t then (1 : k) else 0

        noncomputable def intervalDirectSum :
            (L : List (Fin (N + 1) × Fin (N + 1))) → Tuple (foldDim L)
          | []      => zeroTuple
          | p :: ps => dirSum (intervalModule p.1 p.2) (intervalDirectSum ps)

    Existence (`Core.Barcode`, `Core.Gabriel`) packages a barcode as a finite
    family of bars — for each, a birth, a death, and a one-dimensional line that
    runs as a trajectory along its interval — whose lines at every vertex are
    independent and span:

        def HasBarcode (P : ∀ t, Submodule k (V t)) : Prop :=
          ∃ (M : ℕ) (birth death : Fin M → Fin (N + 1)) (line : Fin M → ∀ t, V t),
            (∀ lam, birth lam ≤ death lam) ∧ … ∧
            (∀ t, iSupIndep (fun lam => k ∙ line lam t)) ∧
            (∀ t, ⨆ lam, (k ∙ line lam t) = P t)

        theorem hasBarcode_tuple (d) (A : Tuple d) :
            HasBarcode (chainSpace k d) (chainEdge d A) (fun _ ↦ ⊤)

    `hasBarcode_of_isSubrep` is the existence half (total-dimension induction,
    one bar peeled per step); `hasBarcode_tuple` reads a matrix tuple as the
    chain of maps $x \mapsto A_i x$. Sorry-free and axiom-clean.

## 4. Reading the threads: ranks and counts

A barcode can be read two ways, and the two readings are related by the oldest
identity in combinatorics.

Read it head-on. Between vertices $i$ and $j$, how many independent signals
survive the trip? That is the rank of the composite $A_j \cdots A_{i+1}$; write
it $r_{ij}$, and set $r_{ii} = d_i$ (everything present at a vertex survives the
empty trip). The array $\underline r = (r_{ij})$ is the **rank pattern**. It is
visible: you compute it by multiplying matrices, and by §2 it does not depend on
coordinates.

Read it from the side. Just count the bars: let $m_{ij}$ be the number of
threads with exactly that birth and death — the multiplicity of $M_{ij}$. The
array $\underline m = (m_{ij})$ is the **multiplicity array**. Its entries are
hidden — they need the decomposition — but they obey one visible constraint:
the bars alive at vertex $k$ are a basis there, so $d_k = \sum_{i \le k \le j}
m_{ij}$. An array of nonnegative integers obeying this is a **Kostant
partition** of $\underline d$.

The two readings are the same data. A thread $[a,b]$ survives the trip from $i$
to $j$ exactly when it is alive on the whole interval — that is, $a \le i$ and
$j \le b$, the bar *contains* $[i,j]$:

```
              i           j
              |←—————————→|
  [a,b]:   •——————————————————•        a ≤ i and j ≤ b :  survives, counts
  [a',b']:        •—————•               does not cover [i,j] :  killed, does not count
```

Each surviving thread contributes exactly $1$ to the rank, and no other thread
contributes. So $r_{ij}$ is nothing but the number of bars containing $[i,j]$:

$$
r_{ij} = \#\{\,[a,b] : a \le i \ \text{and}\ b \ge j\,\}
       = \sum_{a \le i,\ b \ge j} m_{ab}.
$$

The rank pattern is the running total of the bar-counts over all intervals
containing $[i,j]$. To undo a running total you take a difference; in two
dimensions the difference of such a corner-sum is the four-term
inclusion–exclusion

$$
m_{ij} = r_{ij} - r_{i,\,j+1} - r_{i-1,\,j} + r_{i-1,\,j+1},
$$

with out-of-range entries read as $0$. (Among the bars containing $[i,j]$,
remove those that also contain the longer $[i,j{+}1]$ and $[i{-}1,j]$, then add
back the ones removed twice.) These two transforms — corner-sum and second
difference — are inverse to each other; that is the whole of
Lehalleur–Rimányi, Proposition 3.1, and there is nothing in it but counting.

!!! theorem "Proposition 3.1 (Lehalleur–Rimányi) — the two readings invert"
    On arrays supported in $0 \le i \le j \le N$, the corner-sum $\underline m
    \mapsto \underline r$ and the second difference $\underline r \mapsto
    \underline m$ are mutually inverse. In particular a tuple's rank pattern is
    the corner-sum of its barcode multiplicities, and the multiplicities are the
    second difference of the rank pattern.

Two things fall out. First, **uniqueness of the Gabriel decomposition**: the
multiplicities $m_{ij}$ are a fixed formula in the rank pattern, and the rank
pattern is determined by the chain, so the threads are determined by the chain.
The decomposition of §3 is the only one. (This is the uniqueness half of
Gabriel, and it cost nothing beyond the inversion.) Second, the running example
in numbers: from the ranks

$$
\underline r =
\begin{pmatrix} r_{00} & r_{01} & r_{02} \\ & r_{11} & r_{12} \\ & & r_{22}\end{pmatrix}
= \begin{pmatrix} 2 & 1 & 0 \\ & 2 & 1 \\ & & 2 \end{pmatrix}
$$

($\operatorname{rank} A = 1$, $\operatorname{rank} B = 1$, $\operatorname{rank}
BA = 0$, diagonal $\underline d$), the second difference gives $m_{00} = m_{01} =
m_{12} = m_{22} = 1$ and the rest $0$ — the four bars we traced by hand.

??? info "Formalised in Lean — the inversion and its consequences"
    The abstract inversion (`Core.RankPattern`):

        noncomputable def cumul (N : ℤ) (m : ℤ → ℤ → R) : ℤ → ℤ → R := …  -- ∑_{k≤i, j≤l≤N} m k l
        def diff (r : ℤ → ℤ → R) : ℤ → ℤ → R := …                        -- four-term second difference
        noncomputable def cumulDiffEquiv (N : ℤ) : SuppArray N R ≃ SuppArray N R

    The tuple side (`Core.Gabriel`): `exists_barcode_rankPattern` says a tuple's
    $r_{ij}$ counts the bars containing $[i,j]$ (with the Kostant constraint),
    and `rankPattern_eq_cumul_barMult` feeds this through `diff_cumul` to force
    the multiplicities $= \operatorname{diff}(\text{rank pattern})$ — uniqueness.

## 5. The visible determines the hidden

We can compute the rank pattern; we cannot see the threads without work. The
classification is the statement that the visible determines everything.

!!! theorem "The rank pattern is a complete invariant (Lehalleur–Rimányi, Corollary 2.9)"
    Two chains have the same rank pattern if and only if they lie in the same
    $G_{\underline d}$-orbit:

    $$
    \big(\forall\, i \le j,\ r_{ij}(A_\ast) = r_{ij}(B_\ast)\big)
    \iff
    \exists\, P \in G_{\underline d},\ P \cdot A_\ast = B_\ast.
    $$

One direction is §2 (orbits have equal ranks). The other is the substance, and
the proof is the barcode again. Equal rank patterns give, by the inversion of
§4, equal thread-counts; so $A_\ast$ and $B_\ast$ are stacks of the very same
threads. Pair the threads of one with the threads of the other having the same
birth and death; sending each thread-line to its partner, vertex by vertex,
defines an invertible map at each vertex, and because the arrows only shift
threads along their bars, these maps commute with the arrows. That is an
isomorphism of chains — a base change carrying $A_\ast$ to $B_\ast$.

Specialise the partner to the block-diagonal stack and you get a canonical
representative: every chain is base-change-equivalent to the literal stack of its
own threads, $\bigoplus M_{ij}^{\,m_{ij}}$ — its **normal form**. Each orbit
contains exactly one such block chain, named by its multiplicities.

So the three descriptions coincide. An orbit, an isomorphism class, a realizable
rank pattern, and a Kostant partition of $\underline d$ are four names for one
finite set, and the dictionary between them is: orbit $\leftrightarrow$ its rank
pattern (the complete invariant) $\leftrightarrow$ its multiplicity array (the
inversion of §4). This is Lehalleur–Rimányi, Corollary 2.9.

??? note "A worked instance of the bijection: the six chains of shape $(2,2,2)$ with $BA = 0$"
    Fix $\underline d = (2,2,2)$ and ask for the orbits inside $\Sigma^0$, i.e.
    the Kostant partitions with no full thread $M_{02}$ (a full thread would make
    $r_{02} = \operatorname{rank} BA > 0$). Solving $d_k = \sum_{i \le k \le j}
    m_{ij}$ with $m_{02} = 0$ gives six, which we list by the rank corner
    $(r_{01}, r_{12})$ (and $r_{02} = 0$ throughout) and normal form:

    | $(r_{01}, r_{12})$ | normal form | the chain |
    |:---:|:---|:---|
    | $(0,0)$ | $M_{00}^2 \oplus M_{11}^2 \oplus M_{22}^2$ | $A = B = 0$ |
    | $(0,1)$ | $M_{00}^2 \oplus M_{11} \oplus M_{12} \oplus M_{22}$ | $A=0$, $\operatorname{rank} B = 1$ |
    | $(0,2)$ | $M_{00}^2 \oplus M_{12}^2$ | $A=0$, $\operatorname{rank} B = 2$ |
    | $(1,0)$ | $M_{00} \oplus M_{01} \oplus M_{11} \oplus M_{22}^2$ | $\operatorname{rank} A = 1$, $B=0$ |
    | $(1,1)$ | $M_{00} \oplus M_{01} \oplus M_{12} \oplus M_{22}$ | rank one each, $\operatorname{im} A = \ker B$ |
    | $(2,0)$ | $M_{01}^2 \oplus M_{22}^2$ | $\operatorname{rank} A = 2$, $B=0$ |

    Each orbit *is* its rank corner — the bijection in the flesh. The fifth row
    is the running example. The closures of the three orbits with an
    entrywise-maximal rank corner — $(0,2)$, $(2,0)$, $(1,1)$ — are the three
    components of $\Sigma^0_{(2,2,2)}$ from the opening; the other three sit
    inside them ($(0,1) \le (0,2)$, $(1,0) \le (2,0)$, $(0,0)$ below all). The
    $(1,1)$ component is the largest, of codimension $3$, so $C = 3$ and
    $\theta = 1$.

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
    multiplicities via `diff_cumul` → a relabelling of bars → a `Basis.equiv`
    intertwiner → the base change); `orbitKostantEquiv` packages the bijection
    orbits $\leftrightarrow$ realizable rank patterns by the first isomorphism
    theorem. Sorry-free and axiom-clean.

## 6. What the classification is for

We can now say plainly what the machine does: for a fixed shape $\underline d$,
the chains of matrices, up to change of basis, are the Kostant partitions of
$\underline d$; each is a stack of threads; and a chain is pinned down by the
ranks of its interval compositions, which you can compute by multiplying
matrices. The rank loci of §1 are the unions of orbits selected by the value of
the corner rank $r_{0N}$.

What is left is to *measure* the orbits — and that is the next part, not this
one. The size of an orbit closure comes from its normal slice, the space
$\operatorname{Ext}(M, M)$ of self-extensions (Lehalleur–Rimányi, Corollary 3.5,
after Voigt); which closures are components comes from the orbit-closure order
(their Theorem 3.8); and from these the codimension $C$ and the count $\theta$
admit three computations — a Poincaré series, a quadratic integer program, and a
closest-lattice-point formula — and feed the singularity invariant of the deep
linear network loss (their Theorem 8.6). Each of those builds directly on the
classification proved here; none is formalised yet, and where they are used above
they are cited, not claimed.

## Formalisation

Every definition and theorem in this account is formalised in Lean 4 + Mathlib,
in `DLNFibre.Core`, sorry-free and axiom-clean:

| Section | Lean module(s) |
|:---|:---|
| 1. chains, multiplication, loci | `Core.Setup`, `Core.Submult` |
| 2. base-change group, rank-invariance | `Core.BaseChange` |
| 3. interval modules, Gabriel existence | `Core.IntervalModule`, `Core.Barcode`, `Core.Gabriel` |
| 4. rank pattern $\leftrightarrow$ Kostant, inversion | `Core.RankPattern`, `Core.Gabriel` |
| 5. complete invariant, normal form, bijection | `Core.Orbit`, `Core.OrbitKostant` |

Cited to Lehalleur–Rimányi and not formalised: the orbit-closure order
(Theorem 3.8), the $\operatorname{Ext}$ codimension (Corollary 3.5), the
computations of $(C,\theta)$ (Sections 5–7), and the real-log-canonical-threshold
identity (Theorem 8.6). See [`ROADMAP.md`](../../../ROADMAP.md).

## Sources

S. Pepin Lehalleur and R. Rimányi, *Geometry of the fibers of the multiplication
map of deep linear neural networks* (2024); source at
`paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`. A map of the whole
paper, including the parts beyond this classification, is the
[high-level overview](../paper-digest/high-level-overview.md).
