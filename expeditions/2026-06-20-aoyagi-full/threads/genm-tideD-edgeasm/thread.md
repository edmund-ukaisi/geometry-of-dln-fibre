# genm-tideD-edgeasm — the matrix→scalar corank-one EDGE assembly (D)

**Seat:** formaliser (tide). **Picks up:** dbuild's staged EDGE-ASSEMBLY handoff (the last big analytic build
in (D)). **Base:** `origin/expedition/genm-tideD-joint @51ae6b361` (dbuild's staged kit + null-disposal +
cellRank bridge). **Consultants:** satred (b=1-FreeBilinear peel + banked-radial classification), edgebrick
(C-non-degeneracy + uniform δ-slack), arch1build (the `hcell(edge i)` interface), dbuild (the 6-lemma kit).

## Target

`edge_coupledBox_lt_top`: for the GENERIC tight-edge cell `i` of the coupled per-cell dispatch
(`cellRankIndex i = deepTailMin M` AND `deepTailMin M < a+b`, `a=M₀−u, b=M₁−u, u=t+j`),
`∫_cell coupledBoxIntegrand M u c' p < ⊤` for `(M₀−u)(M₁−u)/2 < c' < ½·minAdm M`. Drops into
`coupledBox_lt_top_of_cells`'s `hcell` at the edge cells (arch1build's assembly).

**Structural lock (arch1build):** `deepTailMin < a+b ⟹ a+b = deepTailMin+1` EXACTLY (rankgen) — so the
generic edge cell is **corank-ONE** (only ranks `b`, `b−1` critical), the **`j=0`** entry shell. Deficient
cells (`cellRank i < deepTailMin`) are null (dbuild's `coupledBox_deficientCell_null`); interior in-regime
(`a+b ≤ deepTailMin`) go to couplerad/schurrec. This brick owns the ONE co-null edge cell.

## Honest status — the scalar engine LANDED; the full brick is a multi-lemma mountain (mapped)

The full `edge_coupledBox_lt_top` is a coupled 3-level integral (`∫_p ∫_x ∫_Γ`) whose finiteness needs a
chain of hard measure-theoretic change-of-variables (matrix-space C-shift CoV, polar, the fresh `u=rs`
coupling, δ-fold, IH assembly) — **NOT** a one-tide deliverable. This tide banks the **reusable scalar
engine** (the genuinely-new radial atoms of satred's route, sorry-free, clean-three) + the **validated
interface**, and maps the remainder precisely.

### LANDED (sorry-free, clean-three `[propext, Classical.choice, Quot.sound]`)

`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeScalar.lean` (network-free, on dbuild's kit + Mathlib
JapaneseBracket):
- `scaledRadial1D_eq` — `∫⁻ t, (w+t²)^{−p} = w^{1/2−p}·∫⁻ s, (1+s²)^{−p}` (the `w`-scaling of dbuild's
  `radial1D`, via `Real.map_volume_mul_left`; the `w^{1/2−p}` pivot-energy dependence).
- `scaledRadial1D_lt_top` — its finiteness (`w>0, p>1/2`).
- `japaneseBracket_euclid_lt_top` — `∫_{ℝ^a}(1+‖x‖²)^{−p} < ⊤` (`a<2p`; the `a`-generalisation of
  dbuild's `radial1D`, via Mathlib `integrable_rpow_neg_one_add_norm_sq`).
- `scaledRadialEuclid_eq` — `∫_{ℝ^a}(w+‖x‖²)^{−p} = w^{a/2−p}·∫_{ℝ^a}(1+‖s‖²)^{−p}` (the `w`-scaling via
  `map_addHaar_smul`; the `w^{a/2−p}` pivot-energy dependence for the general-`a` corank leaf — satred's
  STEP-4 JapaneseBracket radial `∫u^{a−1}(w+u²)^{−p} = w^{a/2−p}·B` after polar).
- `scaledRadialEuclid_lt_top` — its finiteness (`w>0, a<2p`).

### VALIDATED interface (NOT committed — has a `sorry`, kept as the pinned target)

`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJEdgeAssembly.lean` — the `edge_coupledBox_lt_top` signature
compiles green (interface exact-fits arch1build's `hcell(edge i)`); body is `sorry`. Exact signature in the
statement card. Left uncommitted (zero-sorry gate). Continue here.

## The remaining mountain — precise decomposition (for the next tide)

satred's route (b=1 first; verified 12/12), with banked/reachable vs HARD tagged:

| Step | Content | Status |
|---|---|---|
| R1 | b=1: corank term `frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q_b=A_cor·Zf` a single row → `Γ·Q_b = γ⊗Q_b` (outer product) | banked (`RouteMSJFreeBilinear.rmatMul_corank_one`, `frobSq_outer`) |
| R2 | C-shift CoV: `mulVec_of_surjective` (v=Q̃ₚ·η), Jacobian `‖v‖^{−a}` bounded off null `{v=0}`; a×t matrix-space CoV | **HARD** (matrix CoV, module diamond; edgebrick consulting) |
| R3 | b≥2: `(b−1)`-row minor chart, bounded Gram-det Jac `det(Q_R Q_Rᵀ)^{−1/2}` (satred) | HARD but bounded (b=1 skips) |
| P1 | polar on Γ (γ) → `r^{a−1}` radial | banked (`RouteMSJSphereBlowup`, `RouteMSJRadialPolar` — edge-safe) |
| P2 | polar/coupling on A_cor (z) → `‖z‖^{−a}` → the log; the FRESH `u=rs` CoV | **MEDIUM-NEW** (satred: the one genuinely-new CoV; region-split at `‖z‖=√w`) |
| P3 | the JapaneseBracket radial `∫u^{a−1}(w+u²)^{−p} = w^{a/2−p}·B` | **LANDED this tide** (`scaledRadialEuclid_eq`) |
| L1 | σ-log `∫s^{−1}ds = log(1/τ)` | banked (dbuild `sigmaLog_integral`) |
| L2 | δ-fold `1+log(1/τ) ≤ (1+1/δ)τ^{−δ}` | banked (dbuild `one_add_sigmaLog_le_rpow`) |
| L3 | 2D-leaf δ-bound `H_p(w) ≤ C_δ·w^{−(p−a/2+δ)}` (region-split, P2+L1+L2+P3) | MEDIUM |
| W1 | `w=frobSq(P·Q̃ₚ)` constant over the fragile (γ,z,C) integration | satred-verified (algebraic) |
| W2 | w-integral = arity−1 IH box integral at exponent `c'−ab/2+δ`, finite by `hIH (redChain u' M)` since `< ½·minAdm(redChain u')` (strict-`<` openness) | **MEDIUM-HARD** (minAdm-recursion exponent bookkeeping; stratum→cut per D-cert v3: s=0→redChain u @ c'−ab/2, s=1→u'=u+1) |

**Net remaining new content:** R2 (C-shift matrix CoV) and W2 (w-integral = IH, minAdm recursion) are the
genuinely-hard pieces; P2/L3 (coupling→log→δ-bound) is medium; R3 is bounded. The HARD CAVEAT (edgebrick,
satred): build the δ-slack **UNIFORMLY**; never "C removes the log" (FALSE at C=0/v→0) — the C-non-degeneracy
supplies the CoV shift, the δ-slack fallback (open IH exponent range) carries `v→0`.

## Traps (do NOT route through — satred/edgebrick, confirmed)
- `corankBlock_morsePeel_setLE` (Γ→univ ⟹ divergent `det(Q_bQ_bᵀ)^{−a/2}`, log-diverges AT the edge).
- the polar angular `J` (sphere identity = same divergence).
- `RadialResidualPower` (the dead full-space route — the det-trap).
- pointwise-in-`z` / global corank-Gram (`a+b≤M₂`) — factored artifacts.
- claiming a finite-constant exact `ab/2` peel or a multiplicity `m` — claim the VALUE `½·minAdm`.

## Lesson banked
`lintegral_smul_measure` yields `k • ∫f` (smul, not `*`) and `lintegral_map`/`map_addHaar_smul` put the
mapped-measure integral on the LEFT — so the scaling-CoV equation comes out `k • ∫f = …` REVERSED from the
naive expectation. Convert `•`→`*` with `smul_eq_mul` and use `hlm.symm`; build the cancellation via
`congrArg (k * ·)` not `rw [hlm]` (the latter's pattern-matching on `EuclideanSpace` integrands is brittle
vs the `ℝ` case). Cost ~6 build cycles on `scaledRadialEuclid_eq`.
