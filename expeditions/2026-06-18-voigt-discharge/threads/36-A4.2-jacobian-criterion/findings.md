# Thread 36 (A4.2) — char-0 Jacobian criterion for `trdeg(image μ_M^*) ≤ finrank(range δ⁰)`

**Seat.** pen-and-paper, AG half, de-risking the irreducible nugget of L2b★ (route c). **No Lean.**
Output: a proof certificate + a Mathlib-targetable decomposition for the formaliser. Exact-algebra
checks over ℚ and over the symbolic fraction field; decorrelated Codex (`xhigh`) consult in `codex/`.

## The exact A4 obligation (route c, A0 already landed)

A0 (`varietyDim_eq_ringKrullDim_range_orbitPullback`, landed) gives
`varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`. The remaining route-c obligation is

> `(ringKrullDim (orbitPullback M).range).unbotD 0  ≤  finrank k (LinearMap.range (deformationδ M M))`.

A4.1 (`ringKrullDim(range) = trdeg(range)`, cheap, thread 33) reduces this to the **CRUX**:

> **A4.2 ⊕ A4.3.** In char 0: `trdeg_k(image μ_M^*) ≤ generic-rank of Jacobian(μ_M^*)`, and that
> generic Jacobian rank `= finrank_k(range δ⁰) = finrank(LinearMap.range (deformationδ M M))`.

Objects (exact, from `Core/OrbitVariety.lean`, `Core/DeformationExt.lean`):
- `μ_M : G_d → Rep`, `P ↦ P•M`, i.e. `(P_{i+1} M_i P_i⁻¹)_i`. Pullback `μ_M^* = aeval (genericOrbitCoord M)`
  sends `X⟨i,r,c⟩ ↦ (r,c)`-entry of `Pgen_{i+1} M_i Pgen_i⁻¹ ∈ 𝒪(G_d) = groupRing d` (a localization
  of `k[GroupCoord d]` away from `groupDenom`, a domain). `image μ_M^* = (orbitPullback M).range =
  k[genericOrbitCoord M]`, a f.g. `k`-domain.
- `δ⁰ = deformationδ M M : C⁰ → C¹`, `φ ↦ (φ_{i.succ} M_i − M_i φ_{i.castSucc})_i`, where
  `C⁰ = ∏_v Mat(d_v)` (`= Lie G`, diagonal case `e = d`) and `C¹ = ∏_i Mat(d_{i+1}×d_i)` (`= Rep`).
  `finrank(range δ⁰) = dim O_M = dim G − dim Stab` (rank–nullity, landed).

---

## 1 · The criterion + its proof (the `≤` direction we need)

**Setup.** `k` a field, `char k = 0`. `B` a f.g. `k`-domain that is a **localization of a polynomial
ring** `B = S⁻¹ k[x_1,…,x_M]` (so `Ω_{B/k}` is `B`-free with basis `{dx_j}`, and `d b = Σ_j (∂b/∂x_j) dx_j`).
`f_1,…,f_n ∈ B`; `A = k[f_1,…,f_n] ⊆ B`; `K = Frac B`, `F = Frac A = k(f_i) ⊆ K`. The Jacobian is
`J = (∂f_i/∂x_j) ∈ Mat_{n×M}(B)`; its **generic rank** is `rank_K J`. (Our `B = groupRing d`, `M = #GroupCoord`,
`f_i = genericOrbitCoord M` over the `RepCoord` index, all met: `groupRing` is exactly `Localization.Away
(groupDenom)` of `k[GroupCoord]`.)

**Claim (criterion, `≤` direction — the one A4 needs).**
`trdeg_k(A) ≤ rank_K J`. (Full equality holds too, but the AG-half of `hVoigt` needs only `≤`.)

**Proof.**
1. *Differentials are the Jacobian columns (char-free).* `Ω_{K/k} ≅ K ⊗_B Ω_{B/k} ≅ ⊕_j K·dx_j`, so in
   `Ω_{K/k}`, `df_i = Σ_j (∂f_i/∂x_j) dx_j`. Hence the `K`-rank of `{df_i}_i ⊆ Ω_{K/k}` equals `rank_K J`.
2. *Pick a maximal alg-independent subfamily* `f_{i_1},…,f_{i_r}` of `{f_i}`; `r = trdeg_k F = trdeg_k A`,
   and `E := k(f_{i_1},…,f_{i_r})` is purely transcendental, with `F/E` (hence `K/E`) algebraic.
3. *The differentials of the chosen subfamily stay independent (char-0 step).* `Ω_{E/k}` is `E`-free with
   basis `{df_{i_a}}` (purely transcendental). Because `char k = 0`, `K/E` is **separably generated**, so
   the natural map `K ⊗_E Ω_{E/k} → Ω_{K/k}` is **injective**. Therefore `{df_{i_1},…,df_{i_r}}` remain
   `K`-linearly independent in `Ω_{K/k}`. Hence `r ≤ rank_K{df_i} = rank_K J`, i.e.
   **`trdeg_k(A) ≤ generic-rank J`.** ∎

**Equality (recorded, NOT needed for `hVoigt`).** The reverse `rank_K J ≤ r`: each `f_j` (`j` outside the
chosen set) satisfies a minimal `p(T) ∈ E[T]` with `p'(f_j) ≠ 0` (char 0); differentiating `p(f_j)=0` gives
`p'(f_j) df_j ∈ E`-span`{df_{i_a}}`, so `df_j` is in the `K`-span of the chosen differentials. Thus
`rank_K J = r = trdeg`. This is Codex's "Upper bound"; **A4 does not consume it**.

**Char-0 is essential at step 3, and ONLY there.** Step 1 (differentials = Jacobian) is char-free. The
separable-generation / injectivity of `K ⊗_E Ω_E → Ω_K` is where char 0 (perfection ⇒ every f.g.
extension separably generated; every algebraic extension separable) is load-bearing. The canonical char-p
failure: `B = k[x]`, `f = xᵖ` gives `trdeg_k k[xᵖ] = 1` but `df = p x^{p-1} dx = 0`, so generic rank `= 0 < 1`.
Frobenius kills the differential; the criterion is **false** in char p.

**Direction pinned.** A4 needs `trdeg ≤ rank` (the **lower bound** on `rank` by `trdeg`), proved by the
**injectivity** half (`K ⊗_E Ω_E → Ω_K` injective). It is *not* the trivial landed inclusion
`range δ⁰ ⊆ ker(jacobian of the determinantal generators)` — that inclusion lives on the **L2a cotangent
side** (a *different* differential, of the defining ideal of `Z_M`, not of the orbit map `μ_M`), and does
**not** discharge A4.

Cleanest Mathlib-target form: `KaehlerDifferential.mvPolynomialBasis` (the `{dx_j}` basis) +
`mvPolynomialBasis_repr_apply` (coords = `pderiv`) for step 1; `Algebra.trdeg` / `IsTranscendenceBasis` /
`exists_isTranscendenceBasis` for step 2; the **absent** separable-extension `Ω`-injectivity for step 3.

---

## 2 · The soundness crux (A1's red-team flag) — constant rank under the `G`-action

**The trap (real).** "differential rank at a chosen point `a` ≥ image dimension" is **FALSE**: `f = t²`
has `trdeg k[t²] = 1` but `df/dt|₀ = 0`, pointwise rank 0 at the origin. The honest invariant is the
**generic** rank (over `Frac`), which for `t²` is `rank_K(2t) = 1 = trdeg`. A build that bounds `trdeg` by
the *identity-point* differential rank **without** the constant-rank step is unsound.

**The rescue — homogeneity gives constant rank.** `μ_M(QP) = Q•μ_M(P)` and `Q•(−) = ρ(Q)` is a **linear
automorphism** of `Rep`. With `L_Q(P) = QP`, `μ_M ∘ L_Q = ρ(Q) ∘ μ_M`; differentiating at `P`:

> `dμ_{QP} ∘ d(L_Q)_P = ρ(Q) ∘ dμ_P`.

Both `d(L_Q)_P` (left-translation, a linear iso) and `ρ(Q)` (a linear iso of `Rep`) are invertible, so
`rank(dμ_{QP}) = rank(dμ_P)`; taking `Q = RP⁻¹` makes `rank(dμ_P)` **independent of `P`**. This step is
**char-free** — pure equivariance + invertibility.

**Identity rank = generic rank = `finrank(range δ⁰)`.** Left-trivializing `TG` and differentiating
`μ_M ∘ L_P = ρ(P) ∘ μ_M` at `e`: `dμ_P ∘ d(L_P)_e = ρ(P) ∘ dμ_e`, so at the generic point `η` the
differential matrix is `ρ(η)·dμ_e` (post-composed with an iso), giving
`generic-rank(dμ_M) = rank_k(dμ_e : Lie G → Rep)`. And `dμ_e = δ⁰` exactly:

> **`dμ_M|_e = deformationδ M M`** — `d/dt[(I+tφ_{i+1}) M_i (I+tφ_i)⁻¹]|₀ = φ_{i+1} M_i − M_i φ_i`.

Verified **exactly and symbolically** (`exact_dmu_at_e.py`): the `O(t)` coefficient equals the commutator
`φ_{i+1} M_i − M_i φ_i` *identically*, including for a **free-symbol generic `M`** — so the identification
is **structural**, true for every tuple, not a (2,2,2) coincidence. Hence
`generic-rank(dμ_M) = rank(δ⁰) = finrank(range δ⁰)`, converting A4.2's "generic Jacobian rank" into the
concrete linear-algebra quantity.

**Where char-0 sits vs where homogeneity suffices (the split).**
- `trdeg = generic Jacobian rank` — **char-0 essential** (separability; Frobenius breaks it).
- `generic rank = rank at e` (constant rank) — **homogeneity alone, char-free**. It even holds in char p
  while the trdeg link fails: `𝔾_m ↷ 𝔸¹, t·x = xᵖ` has constant differential rank 0 but image dim 1.
- `generic rank = dim image = trdeg` (the bridge that *equates* generic differential rank with `trdeg`,
  i.e. **generic smoothness** of the dominant map `G → Ō_M`) — **char-0 essential** (separability of the
  generic fibre). In our formulation this is folded into step 3 of §1; the `≤` we need is exactly the
  char-0 injectivity.

So char-0 enters **only** through the Kähler/separability content of §1 step 3; the entire `dμ_e = δ⁰` +
constant-rank machinery (A4.3) is char-free, resting on the `G`-action and the explicit commutator.

---

## 3 · Mathlib-targetable decomposition + honest size

The route-c file ladder (thread 33) is **A4.1–A4.4 on top of landed A0**. This thread sharpens A4.2/A4.3:

**A4.2 — `Core/JacobianAlgIndependence.lean` (the HARDEST).** Target lemma:

    -- char 0, B = localization of MvPolynomial, f : Fin n → B
    trdeg_k (Algebra.adjoin k (Set.range f)) ≤ rank_K (jacobian-of f)     -- the `≤` we need

  Consumes (Mathlib, present): `KaehlerDifferential.mvPolynomialBasis`, `mvPolynomialBasis_repr_apply`
  (`pderiv` link), `KaehlerDifferential.finite`, `Algebra.trdeg`/`IsTranscendenceBasis`/`exists_isTranscendenceBasis`,
  `PerfectField.ofCharZero`, `trdeg_le_of_injective`. **Must build:** §1's step 3 — for a char-0
  separably-generated `K/E`, the map `K ⊗_E Ω_{E/k} → Ω_{K/k}` is **injective**, hence a maximal
  alg-independent subfamily's differentials stay `K`-independent. **Honest size: this is NOT a single
  wrapper lemma** — it is a small package of field-extension Kähler theory:
    (i) `Ω_{k(t_1..t_r)/k}` free with basis `{dt_a}` (purely transcendental);
    (ii) for `L/E` **separable algebraic**, `L ⊗_E Ω_{E/k} ≃ Ω_{L/k}` (the `D(α) = −D(p)(α)/p'(α)` extension,
         `p'(α) ≠ 0` = separability);
    (iii) separably-generated ⇒ injectivity (tower / colimit);
    (iv) the finite-family bridge `AlgebraicIndependent k f → LinearIndependent K (fun i ↦ d (f i))` and
         its rank corollary.

**A4.3 — `Core/OrbitDifferentialRank.lean` (second-hardest; holds the soundness).** Two lemmas:

    -- (concrete, char-free, STRUCTURAL — verified for generic M)
    "jacobian of genericOrbitCoord M at the identity group point = deformationδ M M"
    -- (constant rank, char-free, homogeneity)
    "rank (jacobian of genericOrbitCoord M at η) = rank (deformationδ M M)"
    ⟹  generic-rank(Jacobian μ_M^*) = finrank k (LinearMap.range (deformationδ M M))

  Consumes (landed): `deformationδ`/`deformationδ_apply`, `genericOrbitCoord`, `genericUnit`/`genericUnitInv`,
  `eval_genericMat`, `groupPoint`, `evalGroupRing` (+ its `genericUnit`/`genericFactor`/`genericUnitInv`
  evaluation lemmas). **Must build:** the `pderiv`-of-`genericOrbitCoord` = commutator identity (the
  `Pgen_i⁻¹` factor differentiates to `−φ_i`; mechanical but fiddly — the inverse's derivative needs
  `d(P⁻¹) = −P⁻¹ dP P⁻¹` specialized at `e`), and the constant-rank `G`-translation transport.

**A4.1 — `Core/AffineNoetherRank.lean` (easy).** `ringKrullDim(range) = trdeg(range)`, from landed
`ringKrullDim_quotient_eq_noetherRank` + Mathlib `trdeg_of_isDomain`/`trdeg_add_eq`/`trdeg_eq_zero`. Low risk.

**A4.4 — `Core/OrbitImageDimensionBound.lean` (glue).** Chain A4.1 (`= trdeg`), A4.2 (`trdeg ≤ generic rank`),
A4.3 (`generic rank = finrank range δ⁰`) + A0 → `varietyDim Z_M ≤ finrank(range δ⁰)`. Low risk.

**Honest module count: still 4 files (A4.1–A4.4)**, but **the difficulty is concentrated in A4.2 and is
under-counted by "1 module"** — A4.2 is internally a ~4-sublemma package of f.g.-field-extension Kähler
theory. Codex independently sized the A4.2+A4.3 mathematics at **~8 distinct lemmas**, the hardest being
the (i)–(iv) package above. **Single hardest sub-lemma:** (ii), the separable-algebraic extension
differential iso `L ⊗_E Ω_{E/k} ≃ Ω_{L/k}` (and its injectivity corollary (iii)) — the brick Mathlib lacks
and the one that re-derives field-extension `Ω` theory.

**KILL-CONDITION (thread 33's flag) — DID IT FIRE? Partially YES, as a calibration, not a refutation.**
The flag: "A4.2 may secretly re-derive the absent `rank Ω = trdeg` structure theory; if so, the 4→more
inflation is real." **Verdict:** the `≤`-direction we need does **not** require the *full* field theorem
`dim_L Ω_{L/k} = trdeg_k L` (Codex agrees: "does not logically require" it). But it **does** require its
*core half* — `Ω` of a rational function field (i) + separable-extension injectivity (ii)–(iii). So A4.2 is
**not** the absent full structure theorem, but it is **more than a wrapper**: it pulls a real (≈4-lemma)
slice of f.g.-field-extension differential theory. The "4 modules" file count is honest; the **effort** is
not uniformly distributed — A4.2 dominates. **Calibration of the estimate, not a kill** of route c (still
strictly cheaper than route A, which needs the *full* `rank Ω = trdeg` plus a second global bridge).
Recommend the formaliser treat A4.2 as the de-risking gate and check whether Mathlib's
`AlgebraicIndependent`/`Algebra.IsSeparable`/`KaehlerDifferential` give (ii) more cheaply than from scratch.

---

## 4 · (2,2,2) verification (EXACT) — all four quantities agree, rank constant in `P`

Two orbits at `d = (2,2,2)` (`exact_222_check.py`, `exact_trdeg_independent.py`, `exact_dmu_at_e.py`).
**All ranks EXACT** — over ℚ (rational arithmetic) for `δ⁰`, over the symbolic fraction field
`ℚ(GroupCoord)` for the generic Jacobian (NOT a numpy float rank at a tolerance):

| quantity | (1,1)-orbit | zero-product |
|---|---|---|
| (a) `finrank_ℚ(range δ⁰)` [exact over ℚ] | **5** | **4** |
| `dim O_M = dim G − dim Stab` (= 12 − 7 / 12 − 8) | **5** | **4** |
| `orbitLinearCodim = dim C¹ − rank` (= 8 − rank) | 3 | 4 |
| (b) generic Jacobian rank of `μ_M^*` [exact over ℚ(GroupCoord)] | **5** | **4** |
| (c) `rank dμ_e = rank δ⁰` (`dμ_e = δ⁰` exact symbolic, incl. generic `M`) | **5** | **4** |
| (d) `trdeg(image)` via **independent** image-of-a-curve dim test (no Jacobian-criterion code) | **5** | **4** |

- **(d) is decorrelated.** The image-variety dimension is the exact-ℚ rank of the `O(t)` coefficients of
  `μ_M(P⁰ + tV)` at **three independent random rational base points** `P⁰ ≠ e` — a different code path that
  never touches the symbolic-Jacobian code. It lands 5 / 4 at every base point. (Computed at generic
  `P⁰ ≠ e` and still equal to the identity-point rank — the constant-rank phenomenon, **exhibited**.)
- **Constant rank confirmed exactly:** `rank(dμ_P)` evaluated at **4 distinct exact-rational group points
  per orbit (including `e`)** is `[5,5,5,5]` / `[4,4,4,4]`. (The earlier thread-30 float checks at tol
  `1e-4` agreed; these supersede them with exact arithmetic.)
- **Cross-check vs thread 30:** `dim O_M = finrank(range δ⁰) = 5` (`(1,1)`) and `4` (zero-product) — matches.

So the route-c chain `varietyDim Z_M = trdeg(image) ≤ generic-rank(J) = finrank(range δ⁰)` is **an equality
chain at (2,2,2)** (5 and 4 throughout), and the `≤` is tight here — confirming A4.2's `≤` is the operative
bound and (with A4.3) lands the concrete RHS.

---

## Codex convergence / divergence (`codex/jacobian-criterion-{prompt,answer}.md`, xhigh)

**Convergence (full, on every load-bearing point):**
- Criterion proof: identical structure (Ω of localized polynomial ring → `df_i = Σ pderiv dx_j` → maximal
  alg-indep subfamily → injectivity of `K ⊗_E Ω_E → Ω_K` for the `≤`). Same char-0 placement (step 3 only)
  and same `xᵖ` Frobenius failure mechanism.
- Constant-rank lemma: identical (`dμ_{QP} ∘ dL_Q = ρ(Q) ∘ dμ_P`, both outer maps iso ⇒ rank independent of
  `P`; char-free), and the same `generic-rank = ρ(η)·dμ_e` left-trivialization conclusion.
- The char-0-essential-vs-homogeneity **split**: Codex independently flags `trdeg = generic rank` as the
  separability-sensitive fact and `generic rank = rank at e` as char-free, with the same `𝔾_m, t↦tᵖ` char-p
  example showing constant rank survives while the trdeg link dies.

**Divergence / what Codex added (folded in above):**
- **Sizing is harder than "1 module."** Codex sizes A4.2+A4.3 at **~8 distinct lemmas** (vs thread 33's
  "1 module, high risk"), the hardest being the (i)–(iv) field-extension Kähler package. I adopt Codex's
  read: the *file* count stays 4, but A4.2's internal lemma count is ~4 and that is where the effort is.
- **The "secret dependency" verdict (the kill-condition):** Codex's precise framing — `trdeg ≤ generic
  rank` "does not logically require" the *full* `dim_L Ω_{L/k} = trdeg_k L`, "but it does require the core
  half" (rational-function-field `Ω` + separable-extension injectivity). The partial-fire of thread 33's
  flag, recorded in §3.
- Codex's `G` smoothness caveat: "generic rank = rank at e" needs `G` smooth so `TG` is a vector bundle and
  `T_e G = Lie G` has the expected meaning. `G_d = ∏ GL_{d_v}` is smooth (open in affine space), so this is
  satisfied — a hypothesis the formaliser carries.

**No contradiction surfaced.** Codex confirmed the bound is **sound as framed** provided `rank δ⁰` is read
as the *generic* Jacobian rank (= identity rank by homogeneity), and named the same naive-formalisation
break I flagged: silently using *pointwise* rank where *generic* rank is needed.

---

## Bottom line (Close)

- **Firmest result (certificate).** In char 0, `trdeg_k(image μ_M^*) ≤ generic-rank(Jacobian μ_M^*)`
  (proof in §1, the injectivity half), and `generic-rank(Jacobian μ_M^*) = finrank_k(range δ⁰)` (proof in
  §2: `dμ_e = δ⁰` exact-symbolic-structural + homogeneity constant rank, char-free). Together with A0 + A4.1
  this discharges the AG-half `varietyDim Z_M ≤ finrank(range δ⁰)`. Exact (2,2,2) check: equality at 5 (the
  `(1,1)`-orbit) and 4 (zero-product), all four quantities agreeing, rank constant in `P`.
- **Scope, named honestly.** The *standard* char-0 "differentials detect algebraic independence" theorem
  (`trdeg = Jacobian rank` / generic smoothness of a dominant map), specialized + the homogeneity-constant-
  rank specialization for the orbit map. Char-0 essential **only** in the Kähler / separability step (§1
  step 3); the `dμ_e = δ⁰` + constant-rank content is char-free.
- **Most likely thing to break it (formalisation).** Silently bounding `trdeg` by the *identity-point*
  Jacobian rank without the constant-rank step (the `t↦t²` trap) — unsound. The constant-rank lemma (A4.3)
  is load-bearing. Second risk: A4.2's separable-extension `Ω`-injectivity (sub-lemma (ii)) being a
  from-scratch chunk of field-extension Kähler theory Mathlib lacks — the real cost concentration.
- **Simplification banked.** A4.2 needs only the `≤` direction (injectivity half), **not** the full
  `trdeg = rank` equality — the minimal-polynomial "upper bound" (Codex's reverse direction) is unused for
  `hVoigt`. Trim the A4.2 target to the `≤` lemma.
- **Next construction / consult that settles the open part.** Pin sub-lemma (ii) against Mathlib's *actual*
  `KaehlerDifferential` + `Algebra.IsSeparable` API (does Mathlib already have `Ω_{L/E} = 0` for `L/E`
  separable algebraic, or the base-change `L ⊗_E Ω_E → Ω_L` iso, in usable form?) — a focused Mathlib-API
  recon (a `scout`/thread-33-style grep, not a pen-and-paper task) decides whether A4.2 is a ~4-lemma build
  or pulls more. Recommend `REQUEST_SPAWN` of that recon before the A4.2 tide.

## Artefacts (this thread)
- `exact_222_check.py` — exact (a)/(b)/(c)/(d-via-Jacobian) + 4-point constant-rank check, both orbits.
- `exact_trdeg_independent.py` — **decorrelated** trdeg = image-variety-dim, image-of-a-curve test at
  random exact base points (no Jacobian-criterion code), lands 5 / 4.
- `exact_dmu_at_e.py` — exact symbolic `dμ_e = deformationδ M M`, incl. generic free-symbol `M` (structural).
- `codex/jacobian-criterion-{prompt,answer}.md` — decorrelated xhigh consult (frame+facts in, hypothesis out).
