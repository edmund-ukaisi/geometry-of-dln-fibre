# Thread 07 — Gabriel decomposition design (pen-and-paper)

**Type:** pen-and-paper (design-space scout). **No Lean written.** **No `lake build` run** (formaliser
editing `lean/` concurrently). Exact algebra only; sympy used to *certify* the reduction, never as a result.

**Job.** A FORMALISATION-READY proof strategy for the type-A (equioriented `A_N`) Gabriel decomposition on
the `Tuple d`-as-representation encoding:

> every `M : Tuple d` is isomorphic, via a `G_d = ∏_i GL_{d_i}` base change, to a direct sum of interval
> modules `⊕_{0≤i≤j≤N} M_{ij}^{⊕ m_{ij}}`, the multiplicities `m_{ij}` unique; equivalently, the **rank
> pattern `r_{ij}` is a complete, base-change-invariant isomorphism invariant**, and `m = diff(r)`.

This pins Thm 2.4 (`thm:easy`, orbits = iso classes), Thm 2.5 (`thm:type_A_indecomp`, Gabriel / interval
decomposition), Cor 2.9 (`cor:gabriel`, orbits ↔ Kostant), and the orbit-side half of Prop 3.1
(`prop:mr_comparison`) — onto the existing `Setup`/`RankPattern` API. The operator chose **FULL BUILD (A)**.

A decorrelated Codex consult (`codex/normalform-{prompt,answer}.md`, `gpt-5.x` xhigh, frame-in /
hypothesis-out) was fired on the cleanest normal-form route; its recommendation (peel-one-interval, total-
dimension induction) is adopted and is independently certified below.

---

## 0. TL;DR (the call)

- **Encoding:** build on `Tuple d` (concrete matrices). Do **not** route through Mathlib's quiver/category
  layer (recon: thin). But state the *existence* half as an abstract **chain of `LinearMap`s between
  finite-dim `k`-vector spaces**, prove the barcode-basis theorem there, and transport to `Tuple d` by
  change-of-basis matrices at the end. This keeps the crux proof in Mathlib's `LinearMap.ker`/`range`/`comap`
  language (cheap) and isolates all `Fin`/`Matrix` cast pain to one transport lemma.
- **Normal-form skeleton (existence):** total-dimension induction, **peeling one interval module `M_{sj}`
  per step** via a backward-preimage splitting (`U_{t-1} = f_t⁻¹(U_t)`). 4 steps; §2.
- **Uniqueness:** essentially **free** given existence + the *already-formalised* `cumulDiffEquiv`. Compute
  `rankPattern(⊕ M_{ij}^m) = cumul m` (block-rank additivity), invoke base-change invariance of the rank
  pattern, then `m = diff(rankPattern M)` by the existing inversion. §3.
- **Refined ladder:** 4b interval modules + direct sums + `rankPattern(⊕)=cumul m`; 4c base-change invariance
  of rank pattern; **4d the barcode-basis existence theorem (the crux)**; 4e orbits=iso classes ⟹ Cor 2.9.
  Hardest single step: **4d, the indexed backward preimage construction + the four-subquotient splitting**. §4.
- **Cite, not prove:** general Krull–Schmidt / general Gabriel; Mathlib subspace-complement existence
  (`Submodule.exists_isCompl`) and `finrank` additivity for `IsCompl`. Everything type-A-specific is PROVED. §4.

---

## 1. Encoding recommendation (rung detail for 4b–4c)

### 1.1 Representation = `Tuple d` (keep it), but prove the crux on abstract chains

`Setup.Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k` already *is* the paper's
`Rep_d = ∏ Mat_{d_i,d_{i-1}}`. The recon found Mathlib's quiver-representation layer thin (no type-A Gabriel,
no interval modules), so building the engine on `Tuple` is both necessary and cleaner. **Recommendation:**

- Keep `Tuple d` as the public object (loci/fibres/`mult` already live there).
- For the **existence** theorem (the crux), work with a **chain of linear maps**
  `V_0 --f_1--> V_1 --… --f_N--> V_N` between finite-dim `k`-vector spaces (`Fin (N+1) → Type` family of
  `Module k`). This is where the proof wants to live: kernels, images, preimages, complements are
  `Submodule` operations with mature Mathlib API. A `Tuple d` *is* such a chain with `V_i = Fin (d i) → k`;
  convert via `Matrix.toLin'`/`Matrix.mulVecLin`.
- Transport the abstract result back to `Tuple` with **one** change-of-basis lemma per vertex
  (`P_i := Q_i⁻¹`, `Q_i` = the barcode basis as columns); `g.A_i = P_i A_i P_{i-1}⁻¹`. All dependent-`Fin`
  cast pain is localised here, not in the induction.

This is the standard "prove the theorem, then read it off in coordinates" move and matches the thread-06
`submult` lesson (push casts to one bridge lemma).

### 1.2 Interval module `M_{ij}` as a `Tuple` (rung 4b)

`M_{ij}` (for `0 ≤ i ≤ j ≤ N`) is the chain `k` on vertices `i..j` with identity maps, `0` elsewhere.
Concretely as a `Tuple` over the dimension vector `e_{ij}` with `e_{ij}(k) = if i ≤ k ≤ j then 1 else 0`:

```
(M_{ij})_t  : Matrix (Fin e(t+1)) (Fin e(t)) k
            = 1   (the 1×1 identity)   if  i ≤ t  ∧  t+1 ≤ j      -- both ends inside [i,j]
            = 0   (the 0×_ , _×0, or 1×1 zero block)   otherwise
```

i.e. the map at edge `t → t+1` is the `1×1` identity exactly when both `t` and `t+1` lie in `[i,j]`, else a
zero block (often `0×0`, `0×1`, or `1×0` by the dimension vector). The clean Lean def is by
`if i ≤ t ∧ t < j then 1 else 0` after the dimensions are fixed — a one-liner; the partial-permutation
0/1-matrix structure of the paper's lace representatives falls out for free.

### 1.3 Direct sum of `Tuple`s (rung 4b)

For tuples `A : Tuple d` and `B : Tuple d'`, the direct sum `A ⊕ B : Tuple (d + d')` is the block-diagonal
tuple `(A ⊕ B)_t = Matrix.fromBlocks (A_t) 0 0 (B_t)` (after a `Fin (a+b) ≃ Fin a ⊕ Fin b` reindex). A finite
direct sum `⊕_{ij} M_{ij}^{m_{ij}}` is the block-diagonal tuple over the dimension vector
`cumulDiag(m)(k) = ∑_{i≤k≤j} m_{ij}` (the Kostant dimension constraint — `= d_k` exactly when `m ⊢ d`).
Mathlib lever: `Matrix.fromBlocks`, block-diagonal rank additivity `rank (blockDiag X Y) = rank X + rank Y`
(standard; INFERENCE on exact name).

### 1.4 Isomorphism / base change (rung 4c)

A `G_d`-base change is `g = (P_0,…,P_N) ∈ ∏ GL_{d_i}` acting by
`(g · A)_i = P_i A_i P_{i-1}⁻¹` (paper §2.2; matches `mult` equivariance in `Setup`). Encode `g` as
`P : ∀ i : Fin (N+1), (Matrix (Fin (d i)) (Fin (d i)) k)ˣ` (unit matrices = `GL`). Define the action, prove
it is a group action (`one_smul`, `mul_smul`), and that it preserves every `submult` composite up to boundary
conjugation: `submult (g·A) i j = P_j * submult A i j * P_i⁻¹`. **This is the engine of 4c.**

---

## 2. The normal-form / completeness crux (rung 4d) — the proof skeleton

**Route (adopted, = Codex's recommendation, hybrid of "peel one interval" (b) + "kernel/image" (d)).**
Total-dimension induction, peeling **one interval module as a direct summand per step**. Strictly cleaner
than peeling a vertex (no two-sided reconciliation across a vertex) or one-pass column reduction (which
*fails*: see §2.4).

### 2.1 The strengthened inductive statement (barcode basis)

State and prove, for **fixed `N`**, by strong induction on the **total dimension**
`D(V_*) = ∑_{t=0}^N finrank_k V_t`:

> **(Barcode-basis theorem.)** For every chain `V_0 --f_1--> … --f_N--> V_N` of finite-dim `k`-vector
> spaces there is a finite label set `Λ`, birth/death maps `b, e : Λ → {0,…,N}` with `b(λ) ≤ e(λ)`, and
> for each vertex `t` a basis of `V_t` indexed by `Λ_t := { λ | b(λ) ≤ t ≤ e(λ) }`, such that on each edge
> `f_t : V_{t-1} → V_t`:
> ```
>   f_t (v_{t-1,λ}) = v_{t,λ}   if  b(λ) ≤ t-1  and  t ≤ e(λ)     (λ "alive across edge t")
>   f_t (v_{t-1,λ}) = 0         if  e(λ) = t-1                    (λ "dies at t-1")
> ```

This basis exhibits the chain as `⊕_λ M_{b(λ),e(λ)}`. In coordinates, with `Q_t` = the matrix whose columns
are this basis of `V_t`, `Q_t⁻¹ A_t Q_{t-1}` is the interval block normal form; the base change is
`P_t = Q_t⁻¹`. **Why strengthen:** the bare existence statement does not give an induction hypothesis you can
apply to a complement; the barcode-basis form does.

### 2.2 The inductive step (the crux)

`D(V_*) = 0`: trivial (empty `Λ`). Otherwise:

1. **Pick a starting vector.** Let `s` be the **least** vertex with `V_s ≠ 0`; pick `v_s ≠ 0`.
2. **Forward trajectory.** `v_t := f_t f_{t-1} ⋯ f_{s+1}(v_s)` for `t ≥ s`. Let `j` be the **largest** index
   with `v_j ≠ 0`. Then `v_t ≠ 0` for `s ≤ t ≤ j`, and (if `j < N`) `f_{j+1}(v_j) = 0`. The chain
   `(k·v_t)_{s≤t≤j}` is a copy of the interval module `M_{sj}`.
3. **Backward complement (the load-bearing move).** Choose any complement `V_j = k·v_j ⊕ U_j`. For
   `t = j, j-1, …, s+1` set `U_{t-1} := f_t⁻¹(U_t)` (`Submodule.comap`). For `t > j` set `U_t := V_t`; for
   `t < s`, `V_t = 0`.
4. **The splitting FACT (the one lemma to prove).**
   > If `f : V → W`, `f v = w ≠ 0`, and `W = k·w ⊕ U`, then `V = k·v ⊕ f⁻¹(U)`.
   >
   > *Proof.* (⊕-trivial) `c·v ∈ f⁻¹(U) ⟹ c·w ∈ U ⟹ c = 0`. (⊕-spanning) for `x`, write
   > `f x = c·w + u` with `u ∈ U`; then `x = c·v + (x − c·v)` and `f(x − c·v) = u ∈ U`. ∎
   Applied along the chain (downward from `t=j` to `t=s`, using `f_t(v_{t-1}) = v_t`) this yields
   `V_t = k·v_t ⊕ U_t` for `s ≤ t ≤ j`, and `V_t = U_t` otherwise.
5. **`U_*` is a subrepresentation.** `f_t(U_{t-1}) ⊆ U_t` by construction (`U_{t-1} = f_t⁻¹(U_t)` for the
   active edges; trivial on the dead/full edges). So `U_*` is a chain of strictly smaller total dimension
   (`D(U_*) = D(V_*) − (j − s + 1) < D(V_*)`).
6. **Recurse + assemble.** Apply the IH to `U_*`; add one fresh label `λ₀` with `b(λ₀) = s`, `e(λ₀) = j`,
   and basis vectors `v_t` on `[s,j]`. Done.

**The single hardest formal step:** step 3+4 — the *indexed backward construction* `U_{t-1} = f_t⁻¹(U_t)`
together with proving each `V_t = k·v_t ⊕ U_t`. It is elementary linear algebra; the friction is the
`Fin`/inequality bookkeeping of "active vs dead edge" indices and threading the `IsCompl` proofs down the
chain. Everything else is `finrank` arithmetic and reindexing.

### 2.3 Certification (sympy, exact)

- `codex/`-route step, end-to-end on **120** nonzero random exact tuples (`N ∈ {2,3}`, `d_i ∈ 0..3`):
  the splitting `V_t = k·v_t ⊕ U_t` holds along `[s,j]` **and** `U_*` is a genuine subrepresentation
  (`f_t(U_{t-1}) ⊆ U_t`) — every trial. → step 2.2 is sound.
- Global theorem shape, **200** random tuples: `m := diff(rankPattern A)` is **always** a Kostant partition
  of `d` (all `m_{ij} ≥ 0`, and `∑_{i≤k≤j} m_{ij} = d_k`), and the explicit interval direct-sum tuple has
  rank pattern **exactly** `rankPattern A` (`= cumul m`). → existence + completeness shape confirmed.
- Peel localisation, **300** trials each: `m_{00} = d_0 − rank A_1 = dim ker A_1`, `m_{NN} = d_N − rank A_N =
  dim coker A_N`; row `0` / column `N` of `m` are one-dimensional second differences of the corresponding
  edge rows/cols of `r`. (Cross-check that the inversion is the right one.)

These are *guides + certificates of the design*, not the Lean proof.

### 2.4 Discarded routes (recorded so they are not re-tried)

- **(a) Peel last map `A_N` / one-pass left-multiply column reduction — FAILS as a one-pass.** Once the
  source basis of `A_t` is frozen by the previous step, left-multiplication alone (changing only the target
  basis) **cannot** reduce `A_t` to a partial permutation in general — the proof must change bases at *both*
  endpoints. (Certified: a left-mult-only sweep is insufficient.) Peeling a *vertex* with two-sided changes
  works but forces reconciling two reductions across the shared vertex — heavier than 2.2.
- **(c) Smith / staircase normal form as the proof driver** — produces the right output but imports
  algorithmic matrix bookkeeping (pivot orders, row/col ops) with no payoff over the basis-free 2.2.
- **(d) full kernel/image filtration / coefficient-quiver** — computes the barcode elegantly but the
  quotient-filtration bookkeeping is strictly heavier than the single-summand peel.

---

## 3. Uniqueness, and how it plugs into the existing API (rung 4c→4d→Prop 3.1b)

Uniqueness is **essentially free** once existence is in hand, because the abstract inversion is *already
formalised* (`RankPattern.cumulDiffEquiv`, `diff_cumul`/`cumul_diff`). The chain:

1. **`rankPattern(⊕_{ab} M_{ab}^{m_{ab}}) = cumul m`** (rung 4b, the tie to Prop 3.1a). The composite
   `submult (⊕ M^m) i j = A_j⋯A_{i+1}` is block-diagonal with one `1×1` identity block per interval summand
   `M_{ab}` that *spans `[i,j]`*, i.e. with `a ≤ i ≤ j ≤ b`, and `0` otherwise. By block-rank additivity its
   rank is `∑_{a ≤ i ≤ j ≤ b} m_{ab} = cumul N m i j` (the *exact* `Setup.submult`-side statement of
   `RankPattern.cumul_apply`). On the diagonal `r_{ii} = ∑_{a≤i≤b} m_{ab} = d_i` (Kostant constraint). This
   is **Prop 3.1b** for the normal form. PROVE (block-rank additivity).
2. **Rank pattern is base-change invariant** (rung 4c). `submult (g·A) i j = P_j (submult A i j) P_i⁻¹`, and
   `rank (P C Q) = rank C` for invertible `P, Q`. Hence `rankPattern (g·A) = rankPattern A`.
3. **Completeness + uniqueness.** Existence (§2) gives `g` with `g·A = ⊕ M_{ij}^{m_{ij}}` for some `m`. By (2)
   `rankPattern A = rankPattern(⊕ M^m)`, and by (1) `= cumul m`. Both `rankPattern A` and `m` are supported
   (rank pattern: `Supported` off the `i<0`,`j>N` walls; `m`: a Kostant array). The *already-proved*
   `diff_cumul` then gives `m = diff (rankPattern A)` — **forced**, hence **unique**. Two tuples with the same
   rank pattern have the same `m`, hence isomorphic normal forms, hence are isomorphic / same `G_d`-orbit.

So the new content is **(1) + (2) + existence (§2)**; the inversion that turns "rank pattern determines `m`"
into "the bijection" is **reused verbatim** from `RankPattern`. The `Supported`/`SuppArray` plumbing already
matches: a rank pattern over `0 ≤ i ≤ j ≤ N` extended by `0` off the array is exactly a `SuppArray N ℤ`.

**Matrix-side bridge needed (rung 4a, thread 06, in flight):** all of this is stated through `submult d A i j
= A_j⋯A_{i+1}` and `rankPattern d A i j = (submult d A i j).rank`. 4b–4e **depend on 4a landing** (or on the
abstract-chain `submult` analogue). Flag: if 4a stalls on the variable-lower-bound cast, the abstract-chain
encoding (§1.1) sidesteps it — define the composite as `LinearMap` composition over `Fin`-intervals, no cast.

---

## 4. Refined rung ladder (4b–4e) — statements, deps, reachability, hardest step, Prove/Cite

Re-sequenced from the working ladder; **4b and 4c are independent and can run in parallel**; both feed 4d;
4d + Thm 2.4 feed 4e. All depend on **4a** (`submult`/`rankPattern`, thread 06) — or its abstract-chain form.

### 4b — Interval modules, direct sums, and `rankPattern(⊕ M^m) = cumul m`
- **Statement.** Define `M_{ij} : Tuple e_{ij}` (§1.2) and `directSum`/block-diagonal of tuples (§1.3). Prove
  `rankPattern (⊕_{ij} M_{ij}^{m_{ij}}) i j = cumul N (m̄) i j` where `m̄` is `m` as an integer array
  (`= ∑_{a≤i≤j≤b} m_{ab}`), and the diagonal recovers `cumulDiag m`.
- **Deps:** 4a (`submult`/`rankPattern`) + `RankPattern.cumul`. **Reachability:** reachable now (block matrices
  + rank additivity). **Hardest step:** the `Fin (a+b) ≃ Fin a ⊕ Fin b` reindex making `submult` of a block-
  diagonal tuple visibly block-diagonal (so `rank` splits). **Prove/Cite:** PROVE; **CITE/USE** Mathlib
  `Matrix.fromBlocks` + block-diagonal rank additivity.

### 4c — Representation isomorphism / `G_d` base change; rank pattern invariant
- **Statement.** Define the `G_d = ∏ GLᵢ` action on `Tuple d` (§1.4); it is a group action; `submult (g·A) i j
  = P_j (submult A i j) P_i⁻¹`; therefore `rankPattern (g·A) = rankPattern A` (base-change invariance).
- **Deps:** 4a. **Reachability:** reachable now. **Hardest step:** the telescoping
  `submult (g·A) i j = P_j (submult A i j) P_i⁻¹` (the inner `P`’s cancel along the product — an induction on
  the composite mirroring `Setup.multPrefix_succ`). **Prove/Cite:** PROVE; **CITE/USE** `rank` invariance
  under multiplication by units (`Matrix.rank` of `P*C*Q` — confirm exact Mathlib name).

### 4d — Barcode-basis existence theorem (THE CRUX) ⟹ rank pattern a complete invariant
- **Statement.** §2.1 (abstract chain) + the transport to `Tuple` (§1.1): every `A : Tuple d` satisfies
  `∃ g : G_d, ∃ m : Kostant d, g · A = ⊕_{ij} M_{ij}^{m_{ij}}`, and (with 4b+4c+the existing inversion)
  `m = diff (rankPattern A)` — so `rankPattern` is a **complete** base-change invariant.
- **Deps:** 4b, 4c, `RankPattern.diff_cumul`. **Reachability:** real work — the largest new piece, but
  bounded (finite-dim linear algebra, no category theory). **Hardest step (whole-thread):** the indexed
  backward preimage construction `U_{t-1} = f_t⁻¹(U_t)` + the `IsCompl` splitting threaded down the chain
  (§2.2 step 3+4). **Prove/Cite:** PROVE (the splitting FACT, the induction, the transport); **CITE/USE**
  Mathlib `Submodule.exists_isCompl` (complement existence over a field) and `finrank` additivity for
  `IsCompl` (`Submodule.finrank_add_finrank_of_isCompl`-style — INFERENCE on exact name).

### 4e — Orbits = iso classes (Thm 2.4) ⟹ orbits ↔ Kostant (Cor 2.9)
- **Statement.** Thm 2.4: `A ≅ B` (as chains) ↔ `∃ g, g·A = B` (same `G_d`-orbit). Then Cor 2.9: the map
  `m ↦ O_m := { A | A ≅ ⊕ M_{ij}^{m_{ij}} }` is a bijection `Kostant d ≃ (G_d-orbits of Tuple d) ≃ (iso
  classes)`, with inverse `A ↦ diff (rankPattern A)`.
- **Deps:** 4d (+ 4c for the orbit half). **Reachability:** corollary-level once 4d lands. **Hardest step:**
  packaging "iso class ↔ orbit" — in this concrete encoding `A ≅ B` *is defined* as `∃ g, g·A = B`, so Thm 2.4
  is true by **definition** of the chain-iso unfolded into matrices (the content is that a chain iso `φ_i`
  is a tuple of invertible matrices = an element of `G_d`). PROVE (short). **Prove/Cite:** PROVE; the
  bijection is then `cumulDiffEquiv` restricted to the Kostant/orbit-realisable arrays.

### Prove-vs-Cite summary
| Item | Call | Justification (formalisation cost) |
|---|---|---|
| Splitting FACT + barcode induction (4d) | **PROVE** | short, type-A-specific, no category theory; the reusable asset |
| `rankPattern(⊕ M^m) = cumul m` (4b) | **PROVE** | block-rank additivity, immediate |
| Rank-pattern base-change invariance (4c) | **PROVE** | telescoping conjugation + `rank` unit-invariance |
| Completeness via `diff`/`cumul` (4d/4e) | **PROVE (reuse)** | reuses `cumulDiffEquiv` verbatim — near-free |
| Thm 2.4 orbits=iso (4e) | **PROVE** | true by definition once iso is unfolded to matrices |
| Subspace complement existence | **CITE Mathlib** | `Submodule.exists_isCompl`; do not reprove |
| `finrank` additivity for `IsCompl` | **CITE Mathlib** | routine library material |
| `rank (P C Q) = rank C`, `P,Q` units | **CITE Mathlib** | routine; confirm exact name |
| General Krull–Schmidt | **DO NOT FORMALISE** | uniqueness here is free from the rank-pattern inversion |
| General Gabriel (all Dynkin) | **DO NOT FORMALISE** | only type-A needed; the peel proof *is* type-A Gabriel |
| Smith / staircase normal form | **DO NOT DRIVE BY** | algorithmic bookkeeping with no payoff over §2.2 |

---

## 5. Worked examples (exact)

### 5.1 `d = (1,1,1)` — the four orbits (= 4 Kostant partitions), and `Σ⁰` as a union of three

A tuple is `(a₁, a₂)` scalars; `r₀₁ = rank a₁`, `r₁₂ = rank a₂`, `r₀₂ = rank(a₂a₁)`. `m = diff(r)`:

| tuple | `(r₀₁,r₀₂,r₁₂)` | Kostant `m` | interval module |
|---|---|---|---|
| `a₁=0, a₂=0` | `(0,0,0)` | `m₀₀=m₁₁=m₂₂=1` | `M₀₀⊕M₁₁⊕M₂₂` |
| `a₁=1, a₂=0` | `(1,0,0)` | `m₀₁=m₂₂=1` | `M₀₁⊕M₂₂` |
| `a₁=0, a₂=1` | `(0,0,1)` | `m₀₀=m₁₂=1` | `M₀₀⊕M₁₂` |
| `a₁=1, a₂=1` | `(1,1,1)` | `m₀₂=1` | `M₀₂` |

`r ↔ m` is a bijection on these four (each `m` is the second difference of its `r`, round-tripping under
`cumul`). The zero-product locus `Σ⁰ = {a₂a₁=0}` = the three orbits with `r₀₂ = 0`
(`M₀₀⊕M₁₁⊕M₂₂`, `M₀₁⊕M₂₂`, `M₀₀⊕M₁₂`); only `M₀₂` (`a₁=a₂=1`) has `r₀₂=1`. This recovers the digest's
"two coordinate axes" picture refined by the quiver: `{a₁=0}` splits as the two orbits `M₀₀⊕M₁₁⊕M₂₂` and
`M₀₀⊕M₁₂`, `{a₂=0}` as `M₀₀⊕M₁₁⊕M₂₂` and `M₀₁⊕M₂₂`, sharing the origin orbit.

### 5.2 `d = (2,2,2)` — the six Kostant partitions ↔ six rank patterns

Indices `0..2`; off-diagonal triple `(r₀₁, r₀₂, r₁₂)` (diagonal always `(2,2,2)`). Verified `diff(cumul m)=m`:

| Kostant `m` (paper's six) | `(r₀₁,r₀₂,r₁₂)` |
|---|---|
| `2M₀₀⊕2M₁₁⊕2M₂₂` | `(0,0,0)` |
| `M₀₀⊕M₀₁⊕M₁₁⊕2M₂₂` | `(1,0,0)` |
| `2M₀₀⊕M₁₁⊕M₁₂⊕M₂₂` | `(0,0,1)` |
| `2M₀₁⊕2M₂₂` | `(2,0,0)` |
| `2M₀₀⊕2M₁₂` | `(0,0,2)` |
| `M₀₀⊕M₀₁⊕M₁₂⊕M₂₂` | `(1,0,1)` |

The five with `r₀₂ = 0` are the orbits in `Σ⁰_{(2,2,2)} = {BA = 0}`; full-rank-product orbits would need
`m₀₂ > 0` (absent in pure `(2,2,2)` zero-product). The **§6/Ex 4.3 "interesting" component**
`det A = det B = 0, BA=0` with `rank A = rank B = 1` is the orbit `M₀₀⊕M₀₁⊕M₁₂⊕M₂₂` (rank pattern `(1,0,1)`):
explicit witness `A₁ = diag(1,0)`, `A₂ = diag(0,1)` gives `A₂A₁ = 0`, `rank A₁ = rank A₂ = 1`, recovered
Kostant `M₀₀+M₀₁+M₁₂+M₂₂` — exactly partition P6. (Certified by sympy with exact integers.)

This is the same `(2,2,2)` witness already in `RankPattern.lean` (the last of the six partitions,
`m₀₀=m₀₁=m₁₂=m₂₂=1`, rank pattern diagonal `(2,2,2)`, off-diagonal `r₀₁=1,r₀₂=0,r₁₂=1`) — so the existing
non-vacuity witness and this worked example are the **same orbit**, tying 4d/4e back to the landed 4a/3.1a
witness.

---

## 6. Close

- **Firmest result.** The peel-one-interval barcode-basis induction (§2) is the cleanest formalisation-ready
  existence proof; its crux step (backward preimage split + `U_*` subrep) is certified on 120 random exact
  tuples; the global `r ↔ m` bijection shape on 200; uniqueness reduces to the *already-formalised*
  `cumulDiffEquiv`. Encoding: `Tuple d` public, abstract `LinearMap` chain for the crux, one transport lemma.
- **Most likely thing to break it.** (i) The `Fin`-interval / "active-vs-dead edge" index bookkeeping in
  step 2.2.3–4 (the named hardest step) — mitigated by proving on abstract chains, not matrices. (ii) Exact
  Mathlib lemma names for complement existence, `IsCompl` `finrank` additivity, and `rank` unit-invariance
  (flagged INFERENCE; cheap to confirm with `scripts/lean-search` before 4c/4d). (iii) Dependence on **4a**
  (`submult`, thread 06): if its variable-lower-bound cast stalls, the abstract-chain composite (LinearMap
  composition over `Fin`-intervals) sidesteps it.
- **Next construction / consult that would settle the open part.** Pin the three Mathlib levers
  (`Submodule.exists_isCompl`, `finrank_add_finrank_of_isCompl`-name, `Matrix.rank` unit-invariance) with
  `example` contracts *before* 4d opens; and have 4b prove `rankPattern(⊕ M^m) = cumul m` first, since it is
  the cheapest of the four and immediately exercises the 4a `submult` API end-to-end.

---

*Codex consult artefact: `codex/normalform-prompt.md` + `codex/normalform-answer.md` (decorrelated, frame-in/
hypothesis-out; recommendation independently certified by the §2.3 sympy checks).*
