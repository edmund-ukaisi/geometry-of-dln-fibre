# genm-sjdescent — OBSTRUCTION FINDING (R1-UPPER `decorated_peel_step`)

**Thread `genm-sjdescent`** (formaliser, isolated worktree off `expedition/aoyagi-full @a7342a96`).
Mission: build the anisotropic-corank descent `decorated_peel_step` → recursion →
`RouteMBoxThresholdFinite M` → close `sjJointResolution` (`RouteMSJResolution.lean:803`), by composing
the banked pieces via the PURE spherical blow-up.

**Verdict: STOP + REPORT (mission-sanctioned).** No Lean written. The pinned SINGLE-STEP descent
target is **unsound as stated** on the rank-deficient-`Q_b` locus that is GENERIC (positive/full
measure) on the bottleneck charts. The finding is decorrelated (independent hand-analysis + Codex
xhigh + exact-algebra argument + numeric probe). It does **not** claim the paper theorem
(`rlct = ½·minAdm`) is false — it says the pinned Lean **lemma-shape** (`decorated_peel_step` as a clean
`M → redChain u M` transport at exponent shift `pq/2`) is the wrong decomposition and needs a re-scope
before more Lean is built on it.

## The pinned descent (what the mission asked to build)

On each pivot chart `(t, ρ, κ)`, after the banked block-reindex + Schur split
(`frobSq_schur_block_split`) + MP shear (`measurePreserving_shearSub`), the inner integral is

    ∫_{Γ ∈ box(a×b)} ( frobSq(A·Q̃) + frobSq(C·Q̃ + Γ·Q_b) )^{−c'} dΓ ,

`a := M₀−t`, `b := M₁−t`, `pq := a·b = peelCharge M t`, `Q̃ := Q_p + A⁻¹B·Q_b`, `Γ := D − C A⁻¹B`
(Schur complement, a free variable after the shear), `Q_b` the non-pivot rows of the tail product
`P = prod(tailChain M)(A')` (shape `b×n`, `n` the deeper reachable width). The pinned plan: blow up
`Γ = r·ω` (`lintegral_eq_polar`, Jacobian `r^{pq−1}`) and descend to the ISOTROPIC brick
`matBox_corank_residual_absZ_le` at the shifted exponent `c' − pq/2`, handing the deeper factor to the
strong IH at `redChain t M`.

## The obstruction (precise)

`matBox_corank_residual_absZ_le` is **isotropic**: the block `Δ` enters only through its OWN `frobSq(Δ)`,
uncoupled to the core `W`. The anisotropic term `frobSq(C·Q̃ + Γ·Q_b)` has that shape **only if**
`Γ ↦ Γ·Q_b` is (up to translation) an isometry-after-scaling — i.e. **only if `Q_b` has full row rank
`b`** (then `Δ := Γ·Q_b` is the CoV with Jacobian a power of `det(Q_b Q_bᵀ)^{1/2}` — the FORBIDDEN Gram
atom route). Let `s := rank Q_b`. Then:

- `Γ ↦ Γ·Q_b` (an `a×b` block to `a×n`) has rank `a·s` with **kernel dimension `a·(b−s)`**: each of the
  `a` rows of `Γ` maps into the `s`-dimensional row-space of `Q_b`.
- On the box, the integrand depends only on the `a·s` **active** coordinates; over those it is an
  `(a·s)`-dimensional isotropic Morse integral (→ `W^{−(c'−a·s/2)}` as `W → 0`), while the `a·(b−s)`
  **kernel** directions contribute only a bounded box factor `(2T)^{a(b−s)}` (no decay).
- Therefore the achievable exponent shift is **`a·s/2`, NOT `a·b/2`.** The spherical blow-up over the
  FULL sphere does not fix this: the `{ω : ω·Q_b = 0}` directions (nonempty exactly when `s < b`) carry
  no radial decay, so the `r`-integral gives no `r^{−2c'}` tail there — the same defect in polar form.

**Genericity (not a null-set technicality).** On a bottleneck chart with `b = M₁ − t > n` (deeper width
smaller than the extra input cols), `rank Q_b ≤ n < b` for ALL `A'` — rank-deficient on FULL measure
(these are the `≈750/5440` charts the `sjJointResolution` docstring already flags). Codex's extreme
counterexample `Q_b = 0, C·Q̃ = 0` gives inner integral `Vol(box)·W^{−c'}` — shift `0`, not `pq/2`.

## Why the existing pen-and-paper adjudication does not cover this

`.../genm-sjjoint-design/pure-vs-atom-adj.md` (verdict A: the pure route is FINITE, avoids the atom
`|z|^{−1}` wall) is **correct about finiteness** but uses a **scalar `p=q=1` caricature**
`F = α² + γ²(βs)²`. A scalar `Γ` (`b=1`) has no matrix kernel: "rank-deficient" collapses to the null
set `βs = 0`. The caricature therefore never exercises the `a·(b−s)`-dimensional kernel subspace, which
is where the exponent-shift (not finiteness) fails. So the pure route being finite for `c' < ½·minAdm`
(their toric-RLCT computation) is **consistent** with the single-step `pq/2` descent being unsound: the
total RLCT is right, but it is NOT reached by a clean per-boundary `pq/2` shift.

## Data (exact-algebra + numeric, decorrelated from Codex)

- **Analytic (clean):** for `a=1`, `Γ` is a row `γ ∈ ℝ^b`; `‖c₀ + γ·Q_b‖²` depends only on the
  `s`-dim `γ·Q_b`, so `∫_{box} (W + ‖c₀+γQ_b‖²)^{−c'} dγ = (2T)^{b−s}·[s-dim Morse](W) ~ W^{−(c'−s/2)}`.
  Shift `= s = a·s`, exactly. Generalises row-wise to `shift = a·s` for any `a`.
- **Numeric** (`codex/descent_shift_check.py`, Monte-Carlo): the cleanest low-dim case `a=1,b=3,n=1`
  (`rank Q_b = 1`) fits `shift ≈ 0.97 ≈ a·s = 1`, not `ab = 3`. (Higher-dim cases are MC-noisy — garbage
  fits over tiny `W` at `8`-dim — reported but not load-bearing; the analytic argument is the certificate.)
- **Combinatorial cross-check** `M = (2,4,1)`, chart `t=1`: `a=1, b=3, n=M₂=1`, so `s ≤ 1`. Pinned
  charge `ab = 3`; achievable `a·s = 1`. `minAdm(2,4,1) = 2` (binding cut `t=2`, block charge `0`);
  `redChain 1 M = (1,1)`, `minAdm = 1`. The `as`-corrected gate is EQUALITY: `2 = 1 + 1 = a·s +
  minAdm(redChain)` — hinting `minAdm`'s binding accounting is itself the RANK-CORRECTED (geometric-codim)
  quantity, while `peelCharge = ab` is a slack over-estimate.

## Recommendation (route to controller → pen-and-paper / scout, before more Lean)

1. **The pinned `decorated_peel_step` shape is dead.** A clean isolated step
   `DecoratedBoxThresholdFinite (over M) → DecoratedBoxThresholdFinite (over redChain u M)` at shift
   `pq/2` cannot be proven by composing the banked isotropic bricks — the shift is `a·s/2` and the
   `a(b−s)` kernel directions must be CARRIED (interleaved), not discharged at this boundary.
2. **The genuine sound primitive (Codex Q3): rank-stratified right-multiplication box descent.** On the
   measurable outer stratum `{rank Q_b = s}` with a fixed full-rank `s`-column pivot of `Q_b`: an MP
   linear chart splitting `Γ` into `a×s` active + `a×(b−s)` kernel parts (the RIGHT-factor analog of the
   banked `measurePreserving_shearSub`), then the banked full-rank inner lemma at `q = s` on the active
   part + bounded kernel volume, giving shift `a·s/2` (regime A `c'>as/2`) and a terminal branch
   (`c'<as/2`). This is genuinely-new, SOUND, and provable in isolation — but it exposes the rank branch
   and does NOT by itself reach the recursion.
3. **The open research question (pen-and-paper, decorrelated):** does the interleaved rank-stratified
   `a·s/2`-per-step descent, summed over the recursion tree, reach `½·minAdm`? The `(2,4,1)` equality
   above and `pure-vs-atom-adj.md`'s toric-RLCT `= ½·minAdm` suggest YES via a rank-corrected charge, but
   the Lean recursion carrier must track the kernel dimensions `a(b−s)` and the accounting must be redone
   with `a·s` (rank-corrected), NOT `ab`. This is a design re-scope, not a formalisation gap.

## Artefacts
- `codex/descent-gap-prompt.md`, `codex/descent-gap-answer.md` — the decorrelated consult (verdict:
  concern-correct; the `as/2`-not-`ab/2` deduction + counterexample).
- `codex/descent_shift_check.py` — the numeric probe.
- Cross-refs: `RouteMSJFreedPeel.lean` header ("unbuilt `(S,J)` double induction; strong IH insufficient
  as a black box at the binding cut, Hölder-infeasible") — the SAME wall, here diagnosed as the
  `as`-vs-`ab` shift mismatch; `.../genm-sjjoint-design/pure-vs-atom-adj.md` (finiteness OK, shift not
  probed).
