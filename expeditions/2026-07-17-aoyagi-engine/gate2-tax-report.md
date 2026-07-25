# Gate-2 tax report — the corank-2 Encoding-I `hideal` measurement

**Branch:** `expedition/aoyagi-engine-gate2` (off `expedition/aoyagi-engine-PROTO` @ `05c35eb8a`).
**Module:** `lean/DLNFibre/Core/Aoyagi/Corank2HidealProto.lean` (115 LoC, sorry-free, axiom-clean).
**Build:** `scripts/lb DLNFibre.Core.Aoyagi.Corank2HidealProto` green; `#print axioms` (force-elaborated,
olean deleted + rebuilt) on all four load-bearing theorems = `[propext, Classical.choice, Quot.sound]`.
Uncommitted (per role boundary — the controller integrates); files live in the worktree for re-derivation.

**Verdict: YELLOW.** The *measured object* (the block-elim ideal step, L-A) renders **GREEN** — no hidden
Mathlib ideal-membership tax. But the gate's stated *deliverable* (the two `Chart.hideal` fields) is **not
that object**: a `Chart.hideal` field is a WHOLE-RESOLUTION object (the terminal monomialisation
`⟨(∏C)∘g⟩ = ⟨diag b⟩`), not a one-step object. One corank-2 block-elim cannot produce it — this is a
STOP + scope finding (brief §5), and it refines rather than blocks the go decision. Details below.

---

## The finding, stated first (the scope re-frame)

The brief asks for two `Chart.hideal` fields, and describes the bridge as "instantiate `diag1Delta` at
`monomialFam bexp`". **That instantiation is only valid if the residual after one clear is already
monomial — which, for a genuinely corank-2 witness, it never is** (guardrail 3 forbids a diagonal `Δ`).
Concretely, on the `(3,3,4) t=(1,0)` minimiser:

- One block-elim gives `⟨(∏C)∘g⟩ = ⟨peeled⟩`, `peeled = diag(1,Δ)·(Q₂⁻¹C₂)`. Its entries are `T` (row 0)
  and `Δ·S` (rows 1,2) — **polynomials, not monomials** (`Δ = C₂₂ − C₂₁·C₁₂` is a full coupled 2×2).
- `monomialFam bexp` is by definition pure monomials `b₁,…,b_M`. `⟨peeled⟩ = ⟨monomialFam bexp⟩` is
  **FALSE** at the peeled stage — a coupled polynomial like `m₁₁ − c₁₂ₐc₂₁ₐ` is not in the ideal generated
  by pure coordinate monomials. (Confirmed against the Gröbner-verified ground truth: the diagonal
  monomials `b = (E, E·α·v, E·α·v·δ·w)` in `g-coupled-334-diagb.py` arise from the RADIAL resolution of
  `‖T‖²`/`‖ΔS‖²` + the JOIN, *after* the block-elim — the certificate `corank2-cert/certificate.md §78-82`
  itself scopes this "R1 depth-recursion" OUT of the block-elim step.)

So the literal `hideal` field for a genuine corank-2 witness needs the **whole (S,J) recursion**:
block-elim (this atom) at each step, PLUS the blow-up `u`-factor ledger that accumulates `diag(b)`, PLUS
the layer rollovers, PLUS the terminal — i.e. the full coupled-B build for the instance, not one step.
**A single corank-2 step is not a `Chart` field; the field is a resolution-scale object.** The gate as
worded conflates the step-measurement with the full build.

**Corroborating evidence from the wired monument** (`DLN/Aoyagi/MonumentAssembly.lean`): the actual
assembly reaches its terminal per-chart `hideal` via `PrincipalInv (…) (monoOf (atlas.bexp c)) …` — the
**principal single-monomial** form (`M' = 1`, one generator `monoOf`), which needs *principality*
(`⟨diag b⟩ = ⟨b₁⟩`, explicitly OUT OF SCOPE per brief §5). And that whole fold
(`leaf_stepInv_of_path'`) is currently `sorry`. So the codebase's own route to a corank-2 `hideal` goes
*through* the out-of-scope collapse, and is unproven.

---

## (a) Did the symbolic→concrete instantiation render cleanly? — YES, for the block-elim atom

Instantiating the `Corank2Proto` spine at the **real ambient function ring** `(Fin 21 → ℝ) → ℝ`
(`flatDim (3,3,4) = 21`) rendered with **no Mathlib fight**:

- `blockElim_step_fwd` / `blockElim_step_bwd` (both ideal directions, `⟨C₁·C₂⟩ = ⟨peeled⟩` at `n=21`):
  each is a one-line instantiation of `regionRepresents_P_peeled` / `regionRepresents_peeled_P`, with the
  cofactor-continuity obligation discharged by `(continuous_apply _).continuousOn`. **No ideal-membership
  machinery** (the whole point of the ideal route: `RegionRepresents` is explicit polynomial cofactors +
  a `Finset` reindex, never `Ideal.span`/`Ideal.mem` API). The `flat` (`Fin (p·c) ↔ Fin p × Fin c`)
  reindex tax was already paid inside `regionRepresents_of_matrix_mul` in `-PROTO` and did not resurface.
- `delta_offdiag_coupled`: witnesses the residual is a GENUINELY coupled 2×2 (off-diagonal
  `Δ₀₁ = m₁₂ − c₁₂ᵦ·c₂₁ₐ` carries a live bilinear coupling term; `= −1 ≠ 0` at an explicit point) — so this
  is the coupled minimiser, not the `(2,2,2,2)`-clean diagonal confound (compass F3). ~4-line proof once
  the matrix-entry / `Pi`-apply / `Fin`-literal-`if` reductions are pinned (a `by decide` on the `Fin 21`
  literal equality; otherwise `norm_num` alone stalls on it).

**What did NOT need to be measured (already cheap in `-PROTO`):** the `Q₁·C₁·Q₂ = diag(1,Δ)` symbolic
matrix identity, the unipotent-polynomial inverses, and the `RegionRepresents` bridge — all landed
sorry-free in `-PROTO` over a general comm ring. Promoting them to the concrete `n=21` ambient is free.

## (b) Line count + heaviest single obligation

- **115 LoC** total (module), of which the *new* content beyond re-instantiating `-PROTO` is ~25 LoC.
- **Heaviest obligation: none in the block-elim atom** — it is essentially free (the `-PROTO` bricks do
  the work). The heaviest *rendered* obligation was `delta_offdiag_coupled`'s matrix-entry reduction
  (`!![…]` at `(0,1)` composed with `Pi`-pointwise ring ops + a `Fin 21` `if`-literal), a documented
  low-grade cast/reduction tax, ~4 lines.
- **The `coreGen`/`mult` connection (part C):** `mult_334_eq_prefix` shows `mult (3,3,4)` IS the prefix
  layer product by `rfl`. **Tax note:** writing the RHS as the fully-multiplied `A₁·A₀` hits the
  *documented* dependent-width `HMul`-synthesis friction (`![3,3,4] (Fin.succ 1)` won't reduce for
  instance resolution) — the CLAUDE.md mitigations (`abbrev` dim-vector / literal width ascription) apply.
  Bounded, known, not a wall. Connecting the DLN `coreGen d e` family to the symbolic `C₁·C₂` spine is
  bounded plumbing (a flatten homeomorphism `e : ℝ²¹ ≃ₜ Tuple` + a transpose `A₁·A₀` vs `C₁·C₂`), which I
  did NOT fully build (it measures the smaller tax; the wall is elsewhere).

## (c) Guardrails

- **G1 (running coordinate block):** honoured — `Δ` is the genuine next-layer Schur complement (from
  `-PROTO`'s `Delta = C₂₂ − C₂₁·C₁₂`), never a divide-by-pivot residual. No substitution anywhere.
- **G2 (1×1 clears, no non-triangular block op):** honoured — the single pivot clear is `-PROTO`'s
  unipotent `Q₁,Q₂`; the coupling is carried in `Δ`, not row-mixed.
- **G3 (genuinely coupled `Δ`):** honoured + WITNESSED in Lean (`delta_offdiag_coupled`). This is the
  coupled corank-2 minimiser, not the diagonal confound.
- **G4 (both `RegionRepresents` directions):** honoured — both `blockElim_step_fwd/_bwd`, via the
  unipotent polynomial inverse. This gives the ideal EQUALITY for the *step*, but (per the finding) the
  step's RHS is `peeled`, not `monomialFam bexp`.
- **The b-exponent guardrail (G3-of-brief-§4, `bexp` from the `~t`-formula):** NOT exercised — `bexp`
  only enters at the terminal monomialisation, which this step does not reach. This is itself a signal:
  the `b`-chain is a *recursion-accumulated* object, unreachable from one step, confirming the finding.

## (d) Honest verdict — YELLOW (GREEN on the atom; the field is a full-build object)

**The gate's real question — "does the paper's one-line ideal argument render as concrete
`RegionRepresents` without a hidden Mathlib ideal-membership tax?" — is answered GREEN.** The block-elim
step instantiates at the real ambient with continuous polynomial cofactors and zero ideal-membership
machinery. There is no cast blow-up and no `Ideal.mem` fight; the explicit-cofactor `RegionRepresents`
encoding is exactly the friction-avoiding move it was designed to be.

**But the gate's stated deliverable — the two `Chart.hideal` fields — is NOT deliverable at
one-corank-2-step scope, and not because of a Mathlib wall:** a `hideal` field is the terminal
monomialisation `⟨(∏C)∘g⟩ = ⟨diag b⟩`, a whole-resolution object. Reaching it from the block-elim step
needs the full (S,J) recursion + the blow-up ledger + the terminal (the "bounded but large" reproduction
the render VERDICT names) — and, as currently architected, the principal collapse (out of scope, and
currently sorried). This is exactly the STOP condition in brief §5 ("if closing `hideal` seems to need
terminal principality / more than the step → STOP + report").

**Consequence for the go/no-go on the general-`d` swap:**
- *De-risked GREEN:* the block-elim atom (L-A) — the piece the re-architecture bet on to dissolve the
  degree-1/support-tracking apparatus. It carries no hidden Lean tax. Commit-worthy as an atom.
- *Correctly priced, NOT free:* the full coupled-B `hideal` is the *recursion + ledger + terminal*
  reproduction (per-step = this cheap atom, iterated ~5-6× for `(3,3,4)` with growing `g` compositions and
  dependent-width residuals) PLUS a terminal-monomialisation decision: either the uncollapsed `diag b` via
  the blow-up `u`-factor chain (needs the blow-up `RegionRepresents` links + the radial monomialisation of
  the peeled blocks — **not yet built in Lean, and the radial monomialises coupled blocks to single
  monomials, a per-block principality**), or the principal collapse (out of scope, sorried). The gate did
  not — and at one-step scope could not — measure this; it is the actual remaining build, and the actual
  place the "coupled corank≥2 monument" the expedition circled still lives.

**Recommendation:** treat this as a scope correction, not a green light. The re-architecture's *atom* is
sound and cheap (real result). But committing "the general-`d` swap" is committing the full (S,J)
recursion build, whose terminal still routes through the monomialisation of coupled blocks — the same
frontier, now precisely located at the step *after* the block-elim (the blow-up/radial ledger to `diag b`),
not dissolved by it. Price *that* (build one full corank-2 `hideal` field end-to-end for `(3,3,4)`,
including the blow-up→`diag b` links) before the swap, rather than inferring "bounded" from the atom alone.
