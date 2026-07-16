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
| R2 | C-shift: bound `∫_C (w+‖C·v+σΓη‖²)^{−c'} dC` by the UNIFORM δ-slack (NOT a transversality-everywhere proof); `mulVec_of_surjective` gives the shift DIRECTION only | **MEDIUM** (shifted singular-integral CoV, atoms in hand; NOT hard — see § "R2" below) |
| R3 | b≥2: `(b−1)`-row minor chart, bounded Gram-det Jac `det(Q_R Q_Rᵀ)^{−1/2}` (satred) | HARD but bounded (b=1 skips) |
| P1 | polar on Γ (γ) → `r^{a−1}` radial | banked (`RouteMSJSphereBlowup`, `RouteMSJRadialPolar` — edge-safe) |
| P2 | polar/coupling on A_cor (z) → `‖z‖^{−a}` → the log; the FRESH `u=rs` CoV | **MEDIUM-NEW** (satred: the one genuinely-new CoV; region-split at `‖z‖=√w`) |
| P3 | the JapaneseBracket radial `∫u^{a−1}(w+u²)^{−p} = w^{a/2−p}·B` | **LANDED this tide** (`scaledRadialEuclid_eq`) |
| L1 | σ-log `∫s^{−1}ds = log(1/τ)` | banked (dbuild `sigmaLog_integral`) |
| L2 | δ-fold `1+log(1/τ) ≤ (1+1/δ)τ^{−δ}` | banked (dbuild `one_add_sigmaLog_le_rpow`) |
| L3 | 2D-leaf δ-bound `H_p(w) ≤ C_δ·w^{−(p−a/2+δ)}` (region-split, P2+L1+L2+P3) | MEDIUM |
| W1 | `w=frobSq(P·Q̃ₚ)` constant over the fragile (γ,z,C) integration | satred-verified (algebraic) |
| W2 | w-integral = **SINGLE** arity−1 IH call on `redChain u M` at exponent `c'−ab/2+δ` (see § "W2 — the edge is single-chain" below) | **MEDIUM** (one IH call + one banked cut-soundness lemma) |

**Net remaining new content (satred de-risk):** with R2 framed as the uniform δ-slack singular-integral
bound (below), there is **NO genuinely-hard piece left** — R2, P2, L3, W2 are all **medium** with the atoms
in hand (P3 landed; L1/L2/W2-lemma/P1 banked). The wall-risk on R2 is de-risked: do NOT prove
C-transversality everywhere (that IS the wall, and it's FALSE at `v=0`/`C=0`); assemble the localized
singular integral via the uniform δ-slack. The HARD CAVEAT (edgebrick, satred): build the δ-slack
**UNIFORMLY**; never "C removes the log" — the C-non-degeneracy supplies the shift DIRECTION only, the
δ-slack (open IH exponent range) carries `v=0` by the SAME estimate (not a separate case).

## W2 — the edge is SINGLE-CHAIN (satred correction, verified 0/377 edge cells fail)

**CORRECTION to an earlier framing.** At the EDGE (k=1, THIS build target) W2 is **single-chain — do NOT
build the u'-cut multi-chain.** The "s=1→u'=u+1" is the DEEP-corank (k≥2) mechanism, NOT the edge. At the
edge, the s=0 and s=1 sectors BOTH reduce to the SAME chain `redChain u M` at the SAME exponent `c'−ab/2`;
the s=0/s=1 codim tie (both `= ab`) is just the LOG multiplicity on that one reduction — not a second chart.

**The exact edge W2 (satred, verified):**
- corank charge (from the `{Γ=0}` polar `s^{ab−1}` → FreeBilinear/`u=rs`) `= ab/2`; reduce to
  `redChain u M` at exponent `c'−ab/2`;
- the s=0/s=1 tie → LOG on that same reduction; δ-fold `c'−ab/2 → c'−ab/2+δ` (`sigmaLog` +
  `one_add_log_inv_le_rpow`);
- **finiteness bookkeeping (the W2 lemma):** `c'−ab/2+δ < ½·minAdm(redChain u M)` for `c' < ½·minAdm M`
  BECAUSE of the banked cut-soundness `minAdm M ≤ ab + minAdm(redChain u M)` =
  **`minAdm_le_peelCharge_add_redChain` (`RouteMSJResolution:204`)** (so
  `ab/2 + ½·minAdm(redChain u M) ≥ ½·minAdm M`; the `δ` goes into the OPEN IH range).
- So W2 = ONE arity−1 IH call on `redChain u M` at `c'−ab/2+δ` + the banked cut-soundness lemma.
  **No min-over-strata, no `u'=u+1`, no multi-chain.**

Verified: (3,2,2,2)@u=1 (a=2,b=1): redChain=(1,2,2), corner thr `= ab/2 + ½minAdm(redChain) = 1+1 = 2 ≥
½minAdm(M)=1.5` ✓ (over-covers, fine). Why single-chain at the edge but not deep k≥2: at the edge the
sector-codim min `= ab` (the s=0/s=1 tie), so the single-chain charge is exactly `ab/2`; at k≥2 the min
shifts to a deeper stratum (`< ab`), the single-chain charge `< ab/2` undershoots, and THERE the u'-cut
multi-chain (`redChain (u+s) M`) is needed. **This build is the EDGE ⟹ single-chain.** (If the coverage ever
routes a k≥2 cut here, that's a different W2 — ping satred.) This is corneradj's original edge Step E; only
its "J finite" claim was wrong (the log is real, δ-slack absorbs it).

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
vs the `ℝ` case). Cost ~6 build cycles on `scaledRadialEuclid_eq`. (Worth banking in
`lean/CLAUDE.md` Mathlib-gotchas at integration — left to the controller to avoid a mid-flight shared-doc
conflict; dbuild also filed it in its consultant notes.)

## Continuation recipe — P2 and R2 atom-wiring (dbuild, deepest context; verified)

**P2 (u=rs coupling → log), the concrete wiring.** At FIXED `s`, sub `u = rs` (r the fragile radius),
`dr = du/s`, `r^{a−1} = (u/s)^{a−1}`:
- the `s`-integral factor is `∫ s^{a−1}·s^{−a} ds = ∫ s^{−1} ds = sigmaLog = log(1/τ)` over the radial
  cutoff `[τ,1]` (dbuild's `sigmaLog_integral`);
- the `u`-integral is exactly `scaledRadialEuclid` (the `u^{a−1}` weight after polar) `= w^{a/2−p}·B`
  (**LANDED**, `scaledRadialEuclid_eq`).
So `H = [log(1/τ)]·[w^{a/2−p}·B]`. Then do NOT keep the bare log — fold via
`one_add_sigmaLog_le_rpow` (`1 + ∫_τ^1 σ⁻¹ ≤ (1+1/δ)τ^{−δ}`): `H ≤ w^{a/2−p}·B·(1+1/δ)·τ^{−δ}`. `τ` is the
radial cutoff scale; carry `τ^{−δ}` into the exponent (`c' → c'+δ`), and the IH's OPEN range
`c'−ab/2+δ < ½·minAdm(redChain)` absorbs it. (dbuild: `u=rs` arithmetic verified 12/12 for `a=1,2,3`.)

**R2 (C-shift, `mulVec_of_surjective`), the concrete wiring.** The surjectivity is NOT measure-preserving.
The CoV `C ↦ ξ := C·v` pushes `∫_C f(‖C·v‖²) dC` to `∫_ξ f(‖ξ‖²)·ρ(ξ) dξ` with `ρ` the pushforward
density — **BOUNDED** (a linear surjection `ℝ^{a×u} → ℝ^a` of a box; the kernel fibres give a bounded
density on the image, a box-image containing a neighbourhood of `0`). CARE: need (i) the bounded-density
bound, (ii) the image contains `0` (so the `w`-shift + `‖ξ‖²` radial — i.e. `scaledRadialEuclid` — applies).
The uniform-δ-slack is precisely because `ρ` does NOT vanish at `ξ=0` yet `v→0` (C small) still needs the
δ-fold — **never** a pointwise C-lower-bound. (dbuild has the density-bound lemma shape on request; edgebrick
on call to pin the `‖v‖^{−a}`/`{v=0}`-null against the concrete Lean integral.)

**R2 framing that keeps it MEDIUM, not a wall (satred de-risk).** Do NOT attempt a
"C-transversality-holds-everywhere" lemma — that is the wall AND is FALSE at `v=0` (`w∈ker Q̃ₚ`) and at
`C=0`. Instead bound the C-integral `∫_C (w+‖C·v+σΓη‖²)^{−c'} dC` DIRECTLY by the UNIFORM estimate
`(1+log(1/τ)) ≤ C_δ·τ^{−δ}` with `τ² ≍ w+‖η_C‖²` (dbuild's `one_add_log_inv_le_rpow`/`one_add_sigmaLog_le_rpow`),
which holds **regardless of `v`** — `mulVec_of_surjective` (`v = Q̃ₚ·w ≠ 0`) supplies the shift DIRECTION
generically, and the `v=0` sub-locus is covered by the **same** δ-slack (not a separate case). Framed this
way R2 is a shifted localized-singular-integral CoV with all atoms in hand (`mulVec_of_surjective` +
`sigmaLog` + `one_add_log_inv_le_rpow` + `scaledRadialEuclid`), per-exponent — **medium, not hard**. (satred
on call to pin the exact C-shift CoV + the `∫_C` bound if the assembly snags.)
