# R1-UPPER carrier re-scope + peelZBlock scope — certificate (pen-and-paper, OBSTRUCTION seat)

**Thread `genm-r1carrier`** (branch `genm-r1carrier` off `expedition/aoyagi-full @0d4f97ea`). **NO Lean
build** — exact algebra (`peel_scope{,2,3,4}.py`, sympy 1.14, exact) + a decorrelated
`local-codex-consult` (xhigh, my verdict withheld: `codex/peel-scope-{prompt,answer}.md`). Two
deliverables: **(A)** the re-scoped chain-descending decoration carrier (Lean-ready shapes), **(B)** the
decisive BOUNDED-large-build vs GENUINE-research-grade adjudication of `peelZBlock`.

---

## HEADLINE (deliverable B is the headline — it is research-grade)

**`peelZBlock` is RESEARCH-GRADE, not a bounded banked-atom composition, at corank ≥ 2 with a genuine
product tail. The step that maps the anisotropic coupled corank block `‖C·Qp + Γ·Qb‖²` into the
isotropic `‖Δ‖² + W(z)` shape the banked regime atoms require is the principalisation / log-resolution
of the maximal-minor (Cauchy–Binet / Plücker) ideal `I₂(A_{1,b}·A₂)` of a matrix PRODUCT. This is a
resolution-of-singularities theorem the measure-CoV atoms do NOT reach and Mathlib lacks. R1-UPPER is
therefore a genuine build-vs-CITE operator call, NOT a "big-but-buildable" sub-expedition — for the
corank-≥2 product regime. It IS bounded/banked in the complementary regime (corank 1, or a free
single-matrix tail).**

Three decorrelated lines agree, independently: (i) my exact algebra (Cauchy–Binet Gram-det = `pᵀGp`;
a dense-torus rank-drop witness that no coordinate blow-up can see); (ii) decorrelated Codex xhigh
(verdict withheld) returned **RESEARCH-GRADE** and named the same theorem; (iii) the repeated
carrier-insufficiency history (separable-form divergence → SJDecoration-can't-peel `sjbuild4`) is exactly
what a genuine (non-composable) gap looks like. The pure route does **not** escape this — it *relocates*
the product-minor geometry into a larger ideal (my C6, Codex Q1, both independent).

**Scope boundary (name the theorem by its true scope).** The gap is precise, not blanket:

| regime | verdict | why |
|---|---|---|
| corank 1 (any depth) | **BOUNDED (toric)** | rank-drop locus `{Qb=0}={row∈left-ker A₂}` is `{row=0}` for full-rank `A₂` — a COORDINATE subspace, toric-resolvable (`C9a`, exact). |
| free single-matrix tail (depth ≤ 3, e.g. `(3,3,4)`) | **BOUNDED via ESCAPE (banked)** | bounded NOT because `det(Qb Qbᵀ)` is toric (it is NOT — `C11`: the free 2×4 Gram-det also has a dense-torus rank-drop), but because the tail is one FREE matrix so `Qp ⊥ Qb` are INDEPENDENT and the banked `SchurCore`/`routeMBoxThresholdFinite_rrp` closes it by a two-matrix-core argument that needs no det principalisation. |
| **corank ≥ 2 AND shared product tail (≥ 2 tail factors, depth ≥ 4)** | **RESEARCH-GRADE** | `{rank(A_{1,b}·A₂) ≤ 1}` has rank-drop points in the DENSE TORUS (`C7`, exact); AND `Qp, Qb` SHARE the deeper product `Z`, so the SchurCore decoupling escape is unavailable — the product-minor principalisation is unavoidable. |

Smallest research-grade instance: **`(3,3,3,4) t=1`, corank `2×2`, tail `A₁·A₂` (`2×3 · 3×4`).** (The
mission's "(3,3,4) t=(1,0,0) corank-2" reads literally as the depth-3 FREE-tail case, which is the
*bounded* `SchurCore` case; the genuine STEP-0 corank-2 *product* anchor is `(3,3,3,4) t=(1,0,0)`, per
`genm-sjnative/step0-derisk.md`. I adjudicate the product anchor and pin the boundary explicitly so the
distinction is not lost.)

---

## (A) The chain-descending decoration carrier (Lean-ready re-scope)

**The banked `SJDecoration M` (`RouteMSJDecorated.lean`) is structurally unable to peel** (`sjbuild4`,
verified concretely): its `(Z, mZ, ctx, dom)` are FIXED, its threshold `carrierThreshold M = ½·minAdm M`
is parameterised by the FULL chain `M`, and its only ops (`radialAttach`, `rowMix`) are pointwise-loss
identities that never (i) map a `z`-block of `Z` into fresh `u`, (ii) integrate out a freed corank
block, or (iii) descend the base chain. The re-scope makes the **remaining chain a first-class index**
so the threshold, the peel step, the base and the consumer are each statable at the right generality.

The re-scope is deliberately a *statement-level* re-architecture: it makes the peel STATABLE and isolates
the research-grade content to one named brick inside `peelZBlock` (§B). It does not make the peel
buildable — that is the operator call.

### 1. The carrier, indexed by the remaining chain

```lean
/-- The chain-descending decoration.  Indexed by the STILL-UNPEELED remaining chain `remChain`
    (arity `Lrem+1`, which DECREASES under a peel).  `Z` is the deeper/active parameter space of
    `remChain`'s tail (the product `A₂·…·A_{Lrem}`); a peel SHRINKS both `remChain` (via `redChain`)
    and `Z` (one fewer layer).  The generator carrier + accumulated Jacobian are as in the banked
    `SJDecoration`, but the fixed-`M` threshold is replaced by a `remChain`-parameterised one. -/
structure ChainDecoration {Lrem : ℕ} (remChain : Fin (Lrem + 1) → ℕ) : Type 1 where
  d       : ℕ                          -- # accumulated exceptional coordinates (radials peeled)
  jac     : Fin d → ℕ                  -- accumulated resolution-Jacobian exponents `h`
  ζ ν ι   : Type
  fν      : Fintype ν
  fι      : Fintype ι
  carrier : SJLinGenState ζ ν ι d      -- shared-divisor support + linear residual (banked)
  Z       : Type                       -- deeper params of `remChain`'s tail (SHRINKS per peel)
  mZ      : MeasureSpace Z
  ctx     : Z → ζ × (ν → ℝ)
  dom     : Set Z

/-- The chain-descending threshold: HALF the minimal admissible codim of the REMAINING chain.
    (This is the field the banked `SJDecoration` could not descend — its threshold was `½·minAdm M`
    for the fixed full `M`.  Equals the outer-cert `Θ(M,π)` under `remChain = remChain(M,π)`.) -/
noncomputable def chainThreshold {Lrem} (remChain : Fin (Lrem + 1) → ℕ) : ℝ :=
  (minAdm remChain : ℝ) / 2

noncomputable def ChainDecoration.decLoss {Lrem} {remChain : Fin (Lrem+1) → ℕ}
    (D : ChainDecoration remChain) (u : Fin D.d → ℝ) (z : D.Z) : ℝ :=
  letI := D.fν; letI := D.fι; D.carrier.loss u (D.ctx z).1 (D.ctx z).2

noncomputable def ChainDecoration.integral {Lrem} {remChain : Fin (Lrem+1) → ℕ}
    (D : ChainDecoration remChain) (c' : ℝ) : ℝ≥0∞ :=
  letI := D.mZ
  ∫⁻ z in D.dom, ∫⁻ u in unitBox D.d,
    ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c'))
```

### 2. The `remChain`-parameterised finiteness predicate

```lean
/-- Below the REMAINING-chain threshold, the accumulated Jacobian monomial times the carrier loss to
    the `−c'` integrates finitely.  The re-scoped `DecoratedBoxThresholdFinite'` (threshold
    `½·minAdm(remChain)`, NOT `½·minAdm M`). -/
def ChainDecoratedFinite {Lrem} {remChain : Fin (Lrem+1) → ℕ} (D : ChainDecoration remChain) : Prop :=
  ∀ c' : NNReal, (c' : ℝ) < chainThreshold remChain → D.integral (c' : ℝ) < ⊤
```

### 3. The Z-block-peel operation (the data transform + the research-grade brick, named)

```lean
/-- One native R-BLOWUP peel at the leading layer, cut `u ≤ min(remChain 0)(remChain 1)`, block
    `pq = peelCharge remChain u`.  Produces a decoration on the STRICTLY-SHORTER `redChain u remChain`.
    Structure (CLEAR-FIRST ordering, per `step0-derisk`):
      (a) clear-first scalar Schur elimination        — banked `SJDecoration.rowMix` (constant support)
      (b) attach the fresh fully-shared radial `u₀`   — banked `SJDecoration.radialAttach`
          (`d ↦ d+1`, `jac ↦ Fin.cons (pq−1) jac`, records `u₀` shared by all generators)
      (c) additive Schur block split (pivot ⊕ corank) — banked `SJLinGenState.loss_blockSplit`
      (d) ★ ANISOTROPY REMOVAL: `Γ·Qb ↦ Δ` isotropic  — the RESEARCH-GRADE brick (§B); NOT banked
      (e) integrate out the freed corank block `Δ`    — banked regime atom A/B
          (`matBox_corank_residual_absZ_le` if `c' > pq/2` & core `>0`;
           `matBox_corank_dominates_absZ_lt_top` if `c' < pq/2` & core `≥0`)
      (f) descend `Z` (drop the consumed layer), yielding `Z' `, `ctx'`, `dom'` on `redChain u remChain`.
    Steps (a)(b)(c)(e)(f) are banked/plumbing; (d) is the un-banked resolution content. -/
noncomputable def ChainDecoration.peelZBlock {Lrem} {remChain : Fin (Lrem+1+1+1) → ℕ}
    (D : ChainDecoration remChain) (u : ℕ) (hu : u ≤ min (remChain 0) (remChain 1)) :
    ChainDecoration (redChain u remChain) := /- (a)…(f); (d) is `principaliseCorankProduct` -/ sorry
```

### 4. The peel step (well-founded on chain arity)

```lean
/-- `ChainDecoratedFinite (remChain) ⟸ ChainDecoratedFinite (redChain u remChain)` — the SOUNDNESS of
    one peel.  Uses the banked threshold shift `half_minAdm_sub_half_peelCharge_le`:
    `c' < ½·minAdm remChain ⟹ c' − ½·peelCharge < ½·minAdm (redChain u remChain)`.  Its PROOF consumes
    `peelZBlock` step (d) — the product-minor principalisation — so this theorem is the point at which
    the research-grade content is discharged (or cited). -/
theorem chainDecorated_peel_step {Lrem} (remChain : Fin (Lrem+1+1+1) → ℕ)
    (D : ChainDecoration remChain) (u : ℕ) (hu : u ≤ min (remChain 0) (remChain 1))
    (ih : ChainDecoratedFinite (D.peelZBlock u hu)) :
    ChainDecoratedFinite D := sorry

/-- The threshold-shift soundness (banked cast; combinatorial, NOT the analytic content). -/
theorem chainThreshold_shift {Lrem} (remChain : Fin (Lrem+1+1+1) → ℕ) (u : ℕ)
    (hu : u ≤ min (remChain 0) (remChain 1)) :
    chainThreshold remChain - (peelCharge remChain u : ℝ)/2 ≤ chainThreshold (redChain u remChain) := by
  unfold chainThreshold; exact half_minAdm_sub_half_peelCharge_le remChain u hu
```

### 5. The base (remChain collapsed → the S2-free terminal)

```lean
/-- At a collapsed chain (arity-0 `Fin 1`, or a two-width leaf, or fully resolved so the carrier is a
    z-INDEPENDENT monomial sum), the decorated integral is the S2-free monomial terminal:
    `sjLoss_terminal_lintegral_lt_top` (finiteness below `monomialThreshold`) fed by the just-banked
    S2-free `iInf_axisRatio_le_monomialThreshold` (`⨅ axisRatio ≤ monomialThreshold`), so
    `½·minAdm(remChain) ≤ ⨅ axisRatio ≤ monomialThreshold` closes it.  (The first `≤` is the
    recursion-coupled combinatorial fact tying `sharedDivisorExp`/`jac` to `remChain`.) -/
theorem chainDecorated_base {Lrem} (remChain : Fin (Lrem+1) → ℕ) (D : ChainDecoration remChain)
    (hbase : Lrem = 0 ∨ isTerminalLeaf D) :
    ChainDecoratedFinite D := sorry
```

### 6. The recursion + the π=∅ consumer (`RouteMBoxThresholdFinite M` recovery)

```lean
/-- The trivial decoration at `remChain = M` (no peels): `d=0`, carrier `= ofMatrix` at the product,
    `Z = Params M`, `dom = paramsBoxM M 1`.  `ChainDecoratedFinite (trivial M) ↔ RouteMBoxThresholdFinite M`
    LITERALLY (thresholds `½·minAdm M` coincide; integrals coincide — the banked
    `trivial_integral_eq` / `decoratedBoxThresholdFinite_trivial_iff`, lifted). -/
noncomputable def ChainDecoration.trivial {L} (M : Fin (L+1) → ℕ) : ChainDecoration M := sorry

theorem chainDecorated_of_wf {Lrem} (remChain : Fin (Lrem+1) → ℕ) (D : ChainDecoration remChain) :
    ChainDecoratedFinite D := sorry           -- strong induction on `Lrem`: base §5, step §4 via §3

theorem routeMBoxThresholdFinite_of_chainDecorated {L} (M : Fin (L+1) → ℕ) :
    ChainDecoratedFinite (ChainDecoration.trivial M) → RouteMBoxThresholdFinite M := sorry
```

**What the re-scope buys (and does not).** It makes the peel step, the base, and the consumer all
statable at the correct generality — the banked `SJDecoration` could not state any of them because its
threshold and `Z` were pinned to the full `M`. It localises the entire analytic difficulty to one named
sub-op, `peelZBlock` step (d) / the proof of `chainDecorated_peel_step`. It does NOT reduce that sub-op
to banked atoms — §B shows it cannot be so reduced.

---

## (B) BOUNDED vs RESEARCH-GRADE — the decisive adjudication (exact, on `(3,3,3,4) t=1` corank-2)

### The precise obstruction

The banked regime atoms require the corank block ISOTROPIC on an ADDITIVE nonneg core:
`∫_Z ∫_{Δ∈box}(‖Δ‖² + W z)^{−c'}`. The carrier, after the Schur block split, has the corank block
ANISOTROPIC and COUPLED: `‖C·Qp + Γ·Qb‖²`, `Γ` a `p×q` chart matrix, `Qb = A_{1,b}·A₂·…` the non-pivot
rows of the tail PRODUCT. Mapping one shape to the other removes the right factor `Qb`. The Gram CoV
`Γ ↦ Γ·Qb` has Jacobian `det(Qb Qbᵀ)^{−p/2}`, `det(Qb Qbᵀ) = ‖∧^q Qb‖²` = sum of squares of the maximal
minors (Plücker coords) of the product. Making that a normal-crossing `monomial × unit` on a finite
chart cover is a principalisation of the product-minor ideal.

### The exact algebra (mine — `peel_scope{,2,3,4}.py`, sympy exact)

At `M=(3,3,3,4)`, `t=1` (`p=q=2`), tail `Z = A₁·A₂` (`A₁` 3×3, `A₂` 3×4), `Qb = A_{1,b}·A₂` (`2×3 · 3×4`
= 2×4 product):

- **C1 (Cauchy–Binet, CONFIRMED).** The 2×2 minors of `Qb` are bilinear in the minors of the factors:
  `minor_ij(Qb) = Σ_{k<l} p_{kl}·minor_{kl,ij}(A₂)`, `p = ∧²A_{1,b}` (3-vector). Each is a genuine
  12-monomial form, gcd of the six = 1.
- **C2 (the Gram-det structure, CONFIRMED).** `det(Qb Qbᵀ) = pᵀ·G·p` with `G = ∧²(A₂)·∧²(A₂)ᵀ` a 3×3
  Gram of `A₂`'s minors — a QUADRATIC FORM in the Plücker coords of `A_{1,b}` whose matrix is itself a
  Gram of `A₂`. Both `p` and `G` vary ⟹ a coupled (shared-`Z`) resolution.
- **C3 (not monomial, exact).** `det(Qb Qbᵀ)` expands to **450 monomials**, is irreducible, and the gcd
  of its terms is **1** — it is NOT `monomial × unit` in the original coordinates.
- **C6 (resolving `A₂` alone is insufficient, exact).** In a rank-revealing chart for `A₂`,
  `det(Qb Qbᵀ)` still has 168 terms, gcd `= 1` — the coupling to `p = ∧²A_{1,b}` survives; the joint
  (product) principalisation is unavoidable.
- **C7 (the decisive toric-insufficiency witness, exact).** `{rank Qb ≤ 1}` has a point in the DENSE
  TORUS: with `A_{1,b} = [[1,1,1],[1,2,3]]`, `A₂ = [[3,4,5,5],[−4,−6,−6,−8],[2,3,3,4]]` (ALL entries
  nonzero), `A_{1,b}·A₂ = [[1,1,2,1],[1,1,2,1]]` (rank 1, all 2×2 minors vanish, all entries nonzero).
  A rank-drop point where no coordinate vanishes is **invisible to every coordinate/toric blow-up
  center**, so a coordinate single-radial sequence cannot make `det(Qb Qbᵀ)` normal-crossing. A
  **non-coordinate (determinantal / Plücker) center is forced.**
- **C9 (scope boundary, exact).** corank 1 → `{Qb=0}={row=0}` coordinate → BOUNDED; free single-matrix
  tail → banked `SchurCore`/`rrp` → BOUNDED; corank ≥ 2 + product tail → C7 → RESEARCH-GRADE.
- **C10 (the verdict-flipping probe, RUN — verdict HOLDS).** "Deepest-layer-first": resolve `A₂` to a
  monomial normal form `U·D·V` BEFORE freeing the corank block. Then `Qb = A'·D·V`, `A' = A_{1,b}·U`
  (generic 2×3), and `det(Qb Qbᵀ) ≍ Σ_{k<l}(d_k d_l)²·p_{kl}(A')²` with `p_{kl}` the 2×2 minors of the
  RESIDUAL 2×3 block `A'`. `I₂(A')` STILL has a dense-torus zero (`A'=[[1,1,1],[1,1,1]]`), so a
  non-coordinate center is STILL forced. Re-ordering the peel does NOT rescue boundedness — the escape
  I flagged as the cheapest verdict-flipper is closed.
- **C11 (why the free case is bounded, precisely).** The free corank-2 Gram-det is ALSO determinantal
  (dense-torus zero, `Y=[[1,1,1,1],[1,1,1,1]]`), so the free case is NOT bounded via toric
  principalisation. It is bounded because `Qp ⊥ Qb` (independent free row-blocks at depth ≤ 3) enables
  the banked `SchurCore` two-matrix-core route. The product case loses exactly this: `Qp, Qb` share `Z`.
- **C5 (shared-ledger necessity, exact toric-RLCT LP).** The shared exceptional divisor halves the
  value (shared : fresh = 1 : 2 in the LP's `lct` normalisation, i.e. the true `½ : 1`) — a naive
  fresh-per-factor toric resolution UNDERCOUNTS. The correct value needs the SAME divisor in `Qp` and
  `Qb`, i.e. the joint product resolution — which is exactly the research-grade brick.

### The verdict — RESEARCH-GRADE (the precise cite-gap)

**`peelZBlock` step (d) — the anisotropy removal `‖C·Qp + Γ·Qb‖² → ‖Δ‖² + W z` for a corank-≥2 product
tail — is NOT a bounded composition of `radialAttach` + `rowMix` + a finite chart cover + the regime
atoms. It requires a genuinely-new principalisation / log-resolution result the measure-CoV atoms do not
contain and Mathlib lacks.**

**What must be built or CITED (name it exactly):** *embedded principalisation / log-resolution, with
normal crossings relative to the already-created exceptional divisors, of the maximal-minor
(Cauchy–Binet / Plücker) ideal `I_q(A_{1,b}·A₂·…·A_{Lrem−1})` of a matrix PRODUCT* — equivalently, the
simultaneous monomialisation of `det(Qb Qbᵀ) = ‖∧^q Qb‖²` jointly with the projected core, tracking the
shared-divisor support at corank ≥ 2. In ordinary mathematics this is covered by char-0 Hironaka /
Bierstone–Milman embedded resolution, but that is a genuine resolution theorem, not a composition of the
banked atoms; the SPECIFIC product-minor principalisation is new substantial infrastructure to formalise.

**The pure route does not rescue it.** The pure route (keep `Γ` a chart coordinate, blow up its radial
in the box, resolve `Qb` via the deeper layers) avoids WRITING `det(Qb Qbᵀ)` explicitly — but the box
`Γ`-integral's residual then depends on resolving the SAME rank-drop locus `{rank Qb ≤ 1}`, whose
determinantal geometry (C7) is untouched by the relocation. My C6 (resolving `A₂` alone leaves the
coupling to `∧²A_{1,b}`) and Codex Q1 ("the same product-minor geometry relocated into a larger ideal")
independently confirm: the pure route relocates, it does not escape. The earlier `pure-vs-atom-adj`
verdict-A ("bounded chart lemma") correctly killed the *atom's full-space over-count artifact*, but its
residual "reach normal crossing" caveat IS this research-grade brick — the caveat was the mountain.

**Why not "bounded but very large."** The distinction is sharp and it is not size. `radialAttach` and
`rowMix` are toric/coordinate operations (they change monomial support and mix generators at constant
support); a finite cover of coordinate charts is toric. C7 exhibits a rank-drop point OUTSIDE every
coordinate stratum. No finite toric/coordinate construction reaches it. The missing step changes the
KIND of blow-up (coordinate → determinantal), not the count. That is the boundary between
"big-but-buildable" and "needs a new theorem."

---

## The decorrelated Codex read (xhigh, my verdict withheld — full agreement, independent)

Codex (`codex/peel-scope-answer.md`), given the frame + the facts but NOT my leaning, returned:

- **Q1 — genuinely new.** "`rowMix` and `radialAttach` … do not contain a parameter-dependent
  right-linear change `Γ ↦ Δ = Γ Qb` nor the Jacobian `det(Qb Qbᵀ)^{−p/2}` … The missing piece is an
  anisotropic corank-block Morse/integration lemma with variable right factor, including rank
  stratification and principalisation/log-resolution of the Gram/minor ideal of `Qb`." And, unprompted:
  "The 'pure route' … does not escape this … the same product-minor geometry relocated into a larger
  ideal."
- **Q2 — non-coordinate center forced.** By Cauchy–Binet `I₂(BC)` is "a bilinear Plücker/Cauchy–Binet
  ideal in minors of the factors," not monomial; `V(I₂(BC))` has "rank-drop points in the dense torus
  … invisible to coordinate-subspace centers." Codex supplied the concrete dense-torus witness I
  verified exactly in C7.
- **Q3 — RESEARCH-GRADE.** Required theorem: "principalisation/log-resolution, with normal crossings
  relative to existing exceptional divisors, of the maximal-minor ideal `I₂(A_{1,b}A₂)` of a matrix
  product … a genuine resolution theorem, not a composition of the banked measure atoms … formalising
  the specific product-minor principalisation in a Mathlib setting would be new substantial
  infrastructure."
- **Q4 — the discriminator** (saturate `I₂(BC)` by the entry product; non-unit ⟺ torus rank-drop) — the
  check I ran (C7/C8).

**Agreement/divergence, reported honestly.** FULL agreement, decorrelated: Codex's independent verdict
is RESEARCH-GRADE, it named the same theorem, and it independently produced the same dense-torus
mechanism and the pure-route-relocates point. No divergence to suppress. This is a decorrelated
convergence, not a rubber stamp — Codex was not told my leaning and reasoned from the Cauchy–Binet
structure itself.

---

## OPERATOR-facing summary (sharpening discuss-at-close #58)

**R1-UPPER is a genuine build-vs-CITE operator call, not a big-but-buildable sub-expedition — in the
corank-≥2 product-tail regime.** The decorated recursion's carrier can be re-scoped cleanly (deliverable
A: a `remChain`-indexed `ChainDecoration` with a `peelZBlock` peel step, well-founded on chain arity,
recovering `RouteMBoxThresholdFinite M` at `π=∅`), and that re-scope isolates the whole difficulty to one
named sub-op. But that sub-op — turning the anisotropic coupled corank block into the isotropic shape the
banked regime atoms consume — is, for corank ≥ 2 with a genuine product tail, the embedded
principalisation of the Cauchy–Binet/Plücker minor ideal of a matrix product: a resolution-of-
singularities theorem, not a composition of the banked atoms, and Mathlib-lacking. Exact algebra (a
dense-torus rank-drop witness no coordinate blow-up can see) and a decorrelated xhigh Codex agree
independently; the repeated carrier-insufficiency (`sjbuild4` and predecessors) is the signature of a
non-composable gap, not of missing labour. The honest options are: (1) CITE — keep `sjJointResolution` /
`RouteMBoxThresholdFinite` as a cited analytic input (Aoyagi's exact DLN computation already supplies the
VALUE; the RLCT payoff already CITES `rlct = ½·codim`), scoping the Lean library to the bounded regimes;
or (2) BUILD — commit a multi-module resolution-of-singularities sub-expedition (product-minor
principalisation + shared-support ledger + weighted monomial endpoint), the largest single undertaking in
the roadmap. The bounded regimes (corank 1, free single-matrix tail / depth ≤ 3) are buildable now and
are worth banking regardless of the call.

---

## Closing (obstruction seat)

- **Firmest result (the obstruction + its exact scope).** `peelZBlock`'s anisotropy-removal step is
  research-grade for corank ≥ 2 with a genuine product tail (≥ 2 tail factors, depth ≥ 4); it is the
  embedded principalisation of the product-minor ideal `I_q(A_{1,b}·…)`. Exact witness (C7): a
  dense-torus rank-drop point of `{rank(A_{1,b}·A₂) ≤ 1}`, invisible to coordinate blow-ups. Bounded in
  the complementary regime (corank 1, free single-matrix tail). Decorrelated Codex agrees, independent.
- **Most likely to break it (probed and closed).** The one escape was a DLN-specific ordering — resolve
  the deepest layer first so each `Qb` is a monomial times an already-resolved unit, hoping the minors
  then principalise torically. I RAN it (C10): resolving `A₂` first leaves `det(Qb Qbᵀ) ≍ Σ(d_kd_l)²·
  p_{kl}(A')²`, and the residual 2×3 minor ideal `I₂(A')` STILL has a dense-torus rank-drop, so the
  non-coordinate center persists. The verdict does not flip. The only remaining (thin) hope is a
  DLN-global structural fact — some constraint forcing the tail products onto a locus where the minor
  ideal degenerates to coordinate — which I did not find and which no prior thread has exhibited.
- **Next construction / consult to settle the open part.** Two decorrelated confirmations remain cheap:
  (i) Codex's Q4 saturation `(I₂(A_{1,b}·A₂) : (∏ entries)^∞)` to a full Gröbner witness (I gave the
  explicit torus point; the saturation would certify the whole torus component is a genuine
  non-coordinate resolution center); (ii) a `verify`-style check that Aoyagi's own published DLN
  resolution (worked-tex `§ssec:blowup`) uses a determinantal / rank-flag blow-up center at corank ≥ 2
  (not a coordinate center) — if it does, that IS the theorem to CITE and closes the question. Absent a
  DLN-global degeneration, CITE is the honest call for the corank-≥2 product regime; the bounded regimes
  are worth building now regardless.
