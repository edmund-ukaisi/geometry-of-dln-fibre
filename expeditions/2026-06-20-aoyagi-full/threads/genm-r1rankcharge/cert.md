# genm-r1rankcharge — CERTIFICATE: the rank-corrected `a·s` descent charge CLOSES

**Seat:** pen-and-paper (witness→obstruction, one dispatch). **Branch:** pushed to
`origin/genm-r1rankcharge` (isolated worktree off `expedition/aoyagi-full @a717cfe1`). **No Lean.**
**Method:** exact integer arithmetic over the *proven* `minAdm` layer-peeling recursion, brute-force
validated against the faithful `Adm`/`Mval` definition, + a decorrelated local-codex-consult (xhigh).

**Scripts (reproduce):** `rankcharge.py` (objects + anchors), `sweep.py` (exhaustive), `adversarial.py`
(adversarial + permutation invariance + fragility), `mechanism.py` (per-cut inequality + binding-cut
structure). All exact `ℕ`/`ℤ`; no floats.

---

## HEADLINE (controller-facing, one paragraph)

**R1-UPPER's descent is BOUNDED via the rank-corrected `a·s` route — re-scope to rank-stratified and
build.** The sjdescent obstruction is real (the pinned single step's `a·b/2` shift is not deliverable
on rank-deficient `Q_b`; the geometry delivers only `a·s/2`, `s = rank Q_b`), but the *weaker*
`a·s/2` shift, correctly accounted in the recursion, **still sums to exactly `½·minAdm M`**. Define the
rank-corrected recursion `minAdmRank` = the `minAdm` layer-peel with block charge `(M₀−t)(M₁−t)`
replaced by `(M₀−t)·min(M₁−t, min(M₂,…,M_L))`. Then `minAdmRank M = minAdm M` on **43,334 chains, zero
failures** (4,764 brute-validated against the `Adm`/`Mval` definition), including an adversarial
wide-early/narrow-deep battery where the per-step rank loss is largest. The closure is **exactly tight**
(it holds at `s = min(b,n)` and *breaks* — 256 failures — if `s` is shrunk by even 1), which certifies
that `a·s = a·min(b,n)` is precisely the geometric per-boundary codimension: the `a·b` figure is a slack
over-estimate, `a·s` is the tight one. The `a·s` accounting therefore **does not fail to close** — it
closes the generic (full-measure) stratum exactly, resolving the very bottleneck charts (`b > n`) the
obstruction flagged. The residual work is not a truth-gap but a build obligation: the lower-rank strata
`{rank Q_b = s′ < min(b,n)}` (measure-zero-in-`Q_b`) must be discharged by the banked corank machinery
composed with this arity recursion (§B), and their sub-stratum codimension bookkeeping needs genuine
care (a crude "block + determinantal codim" heuristic under-counts, e.g. `(4,4,2)` at `s′=1`). Escalate
as: **re-scope R1-UPPER to the rank-stratified `a·s` descent; the combinatorial gate is settled (this
cert); the open item is the analytic per-step primitive of §B and the lower-strata domination.**

---

## (A) THE RANK-CORRECTED CHARGE VERDICT: **CLOSES** (exact, tight, decorrelated)

### The objects (all exact integers)

For a chain `M = (M₀, M₁, …, M_L)` (`L ≥ 1`):
- `minAdm M` — the target codimension. Proven (`minAdmRec_eq_minAdm`, `RouteMLayerSplit.lean`) to equal
  the layer-peel recursion, and re-validated here 0-mismatch against the faithful `Adm`/`Mval`
  brute-force minimum:

      minAdm(M₀,M₁)          = M₀·M₁                                                    (leaf, L=1)
      minAdm(M₀,M₁,…,M_L)    = min_{t ≤ min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(t,M₂,…,M_L) ]  (L≥2)

- **The rank-corrected recursion** `minAdmRank` — same peel, block charge `a·b` → `a·s`:

      minAdmRank(M₀,M₁)       = M₀·M₁
      minAdmRank(M₀,…,M_L)    = min_{t ≤ min(M₀,M₁)} [ (M₀−t)·s_t + minAdmRank(t,M₂,…,M_L) ],
        with  a = M₀−t,  b = M₁−t,  n = min(M₂,…,M_L),  s_t = min(b, n).

`s_t` is the **generic rank of `Q_b`** (the `b` non-pivot rows of the tail matrix-product
`A₁·A₂·…·A_{L−1}`, whose generic rank is `min(M₁,…,M_L)`; restricting to `b = M₁−t ≤ M₁` rows gives
`min(b, min(M₂,…,M_L)) = min(b,n)`). The analytic per-peel step delivers exponent shift `a·s/2` (not
`a·b/2`) because `Γ ↦ Γ·Q_b` (`Γ` an `a×b` block) has kernel dimension `a·(b−s)` carrying no decay.

### The rank-corrected gate (the statement that closes)

For every chain `M` (`L ≥ 2`) and **every** legal cut `t ≤ min(M₀,M₁)`:

    (M₀−t)·min(M₁−t, min(M₂,…,M_L))  +  minAdm(t, M₂,…,M_L)   ≥   minAdm M,          (GATE≥)

with **equality achieved at some cut**, hence

    minAdm M  =  min_{t} [ (M₀−t)·min(M₁−t, n) + minAdm(redChain t M) ]  =  minAdmRank M.

This is the rank-corrected analog of the banked `minAdm_le_peelCharge_add_redChain` (which asserts only
the `a·b` form at *one* cut). (GATE≥) is stronger: it is the `a·s` form at *every* cut — exactly what
the descent needs, since the box is a finite union of pivot charts and every chart must be finite.

### The evidence — CLOSES, exhaustively

| sweep | chains | brute-validated | `minAdmRank = minAdm` | (GATE≥) per-cut fails |
|---|---|---|---|---|
| L+1=3, w0..6/7 | 343 / 512 | yes | 0 fail | 0 |
| L+1=4, w0..5/6 | 1296 / 2401 | yes | 0 fail | 0 |
| L+1=5, w0..4 | 3125 | yes | 0 fail | 0 |
| L+1=6, w0..4 | 15625 | recursion | 0 fail | — |
| L+1=4, w0..8 | 6561 | recursion | 0 fail | — |
| L+1=7, w0..3 | 16384 | recursion | 0 fail | — |
| adversarial (wide-early/narrow-deep, e.g. `(20,20,3,2,1)`,`(15,15,1)`,`(11,11,11,11,2)`) | 14 | — | 0 fail | — |

Instrument check: `minAdmRec == minAdm_brute` on all 4,764 brute cases (0 mismatch) — the recursion I
measure against is the faithful `Adm`/`Mval` object.

### The four mission anchors (per-cut `a·s`-charge breakdown; `*`=rank cap active `s<b,a>0`, `(B)`=binds)

- `(2,4,1)` minAdm=2: `t0[2×1*]=2(B)  t1[1×1*]=2(B)  t2[0×1]=2(B)` — cap active at t0,t1; still ≥2.
- `(3,3,4)` minAdm=8 (free-tail `s=b` always, reduces to old `ab`): `t0=9  t1[2×2]=8(B)  t2=9  t3=12`.
- `(3,3,3,4) t=(1,0,0)`-family minAdm=7: `t0=9  t1[2×2]=7(B)  t2[1×1]=7(B)  t3=8`.
- `(4,4,2,2)` minAdm=4 (bottleneck `s<b`): `t0[4×2*]=8  t1[3×2*]=8  t2[2×2]=7  t3[1×1]=5  t4[0×0]=4(B)` —
  cap bites hard at t0 (`ab`_sum=16 slashed to 8), yet 8 ≫ 4; binds at the cap-inactive t4.

### Tightness (the certificate that `s = min(b,n)` is the exact codim)

Shrink the charge to `a·max(0, min(b,n) − δ)`: closure **holds at δ=0**, **breaks at δ=1** (256 closure
failures over `L+1=4, w0..4`). So `a·s` is not merely *sufficient* — it is the *minimal* charge that
still sums to `minAdm`. The `a·b` charge (`δ` negative, i.e. more) is a valid but slack over-estimate;
`a·min(b,n)` is tight. This is strong independent evidence that the geometric per-boundary shift is
*exactly* `a·s/2` and that the descent is *critically* calibrated to `minAdm` — no margin, no waste.

### Mechanism (the "why", as data)

- **Permutation invariance.** `minAdm` is permutation-invariant in the widths (0 non-invariant over all
  multisets, `L+1=3,4`, w0..5) — matching the paper's `(C,θ)` permutation-invariance. Remarkably
  `minAdmRank` is **also** permutation-invariant and equal to `minAdm`, despite its per-cut charge
  `a·min(b,n)` depending on the *order* (the tail bottleneck). The order-dependence washes out in the min.
- **Equality direction (`≤`).** Every chain has an `ab`-binding cut where the rank cap is *inactive*
  (`s=b` or `a=0`) — verified 256/256 and 0 chains without a cap-inactive binding cut over the L+1=3,4,5
  sweeps. There `a·s = a·b`, so that cut achieves `minAdm` under the `a·s` charge too ⟹ `minAdmRank ≤ minAdm`.
- **Lower-bound direction (`≥`, the new content).** For cap-*inactive* cuts (`M₁−t ≤ n`) (GATE≥) is the
  banked `ab`-gate. For cap-*active* cuts (`M₁−t > n`, so `s = n`) it is a genuine strengthening, and it
  reduces to a **leading-width Lipschitz lemma**: `minAdm(w, W) ≤ minAdm(w′, W) + (w−w′)·min(W)` for
  `w ≥ w′` (fixed tail `W`), verified exhaustively (43,512 cases, 0 fails; per-unit increments always in
  `{0,…,min(W)}`, i.e. `w ↦ minAdm(w,W)` is nondecreasing with slope ≤ tail-bottleneck). Clean proof of
  cap-active (GATE≥) — **the reference-cut route (decorrelated-Codex, verified here 0-fail):** take the
  reference cut `u = min(M₀,M₁)`, whose block charge `(M₀−u)(M₁−u) = 0` (one factor vanishes), so the
  `minAdm` recursion gives `minAdm M ≤ minAdm(u, W)`. Since `t ≤ u`, Lipschitz gives `minAdm(u,W) ≤
  minAdm(t,W) + (u−t)·n`, and `(u−t)·n ≤ (M₀−t)·n` as `u ≤ M₀`. Chaining: `minAdm M ≤ (M₀−t)·n +
  minAdm(t,W) = a·s + minAdm(redChain t M)`. (Uses only the *upper* Lipschitz bound and `u ≤ M₀` — no
  edge case; cleaner than the alternative `t̃ = M₁−n` route.)

### Decorrelated Codex read (xhigh, conclusion withheld in the prompt) — CORROBORATES

Codex (`gpt-5.5`, xhigh) was given only the objects + the questions, **not** my conclusion. Its first
run stalled (the read-only sandbox blocked its verification subprocesses); its reasoning trace,
mid-run, independently reached "the ordinary recursion collapses to a three-smallest-width formula …
the rank-capped branch is controlled by a leading-width Lipschitz bound" — my exact mechanism. A second
run (hand-reasoning only, no code) completed a full verdict (`codex/rankcharge-answer.md`):
- **Q1: TRUE** — `minAdmRank(M) = minAdm(M)` for all chains; no counterexample exists.
- **Q2: TRUE** — cap-active needs the leading-width Lipschitz fact (constant `min(W)`), a genuinely new
  fact beyond the `minAdm` recursion.
- **Q3: PROVED** — `minAdm` is permutation-invariant; `0 ≤ minAdm(w+d,W) − minAdm(w,W) ≤ d·min(W)`.
- **Bonus proof (verified here, 0-fail):** permutation-invariance via *operator commutation* — writing
  `F(a,m₁,…,m_L) = K_{m₁}∘…∘K_{m_{L−1}}(B_{m_L})(a)` with `(K_m f)(a) = min_t (a−t)(m−t)+f(t)`, the
  `K`'s commute because the three-width quantity `min_t (A−t)(B−t)+C·t` is **symmetric in `A,B,C`**
  (I verified: 0 non-symmetric over all triples w0..7, and it equals `minAdm(A,B,C)`).
Codex's two crux sub-claims I re-checked independently, both **0 fails**: the 3-width symmetry, and its
cleaner Q2 chain (reference cut `u` + upper Lipschitz). This is a *decorrelated* second derivation
landing on the SAME verdict and the SAME mechanism (it did not merely echo — it supplied the cleaner
`u`-reference proof I then adopted above). I did **not** paste its argument without running it.

### How (GATE≥) closes the descent (the routing, for the controller's synthesis)

Strong induction on arity `L` (redChain has one fewer layer). Base leaf: threshold `½·M₀M₁ =
½·minAdm`. Step: on pivot chart `t`, after the rank-split (§B) the chart integral obeys, for the two
regimes of the sound primitive,
- `c' > ½·a·s`: `∫ ≤ Cresid · ∫ (deeper-core)^{−(c'−a·s/2)}`, and since `c' < ½·minAdm M ≤_{(GATE≥)}
  ½·(a·s + minAdm(redChain))`, the shifted exponent `c'−a·s/2 < ½·minAdm(redChain)` ⟹ IH finite;
- `c' < ½·a·s`: Morse dominance ⟹ finite directly.
Either regime is finite for all `c' < ½·minAdm M`, at every chart `t`; the finite pivot cover sums to
finite. The box threshold is `½·min_t(a·s_t + minAdm(redChain)) = ½·minAdm M` — reached exactly.

---

## (B) THE RANK-STRATIFIED DESCENT PRIMITIVE (Lean-ready SHAPES — sanity, not a build)

The sound per-step object (Codex Q3 of sjdescent + the banked bricks I read): on the pivot chart, after
the banked block-reindex + `frobSq_schur_block_split` + LEFT shear `measurePreserving_shearSub` exposing
`Γ = D − CA⁻¹B` (an `a×b` free block), apply a **right-factor rank-split change of variables** that
separates `Γ` into an `a×s` active part and an `a×(b−s)` kernel part, then the banked corank brick at
`q = s` on the active part + bounded kernel volume. Shift `a·s/2`.

**Objects reused (banked, verified present):**
- `pivotLocus_eq_iUnion` (`RouteMSJPivotChart.lean`) — the finite pivot-chart cover of the rank-`≥ t` locus.
- `measurePreserving_shearSub` (ibid.) — the LEFT block shear `(x,D) ↦ (x, D − Kx)`, Jacobian 1; the
  new primitive is its RIGHT-factor analog.
- `matBox_corank_residual_absZ_le` (`RouteMSJCorankPure.lean`) — regime A: `∫_Z ∫_{matBox p q T}
  (frobSq Δ + W z)^{−c'} ≤ Cresid(pq) · ∫_Z (W z)^{−(c'−pq/2)}` for `c' > pq/2`, `W > 0`. **Use at `q = s`
  on the active block** (`pq = a·s`).
- `matBox_corank_dominates_absZ_lt_top` (ibid.) — regime B: same block finite for `c' < pq/2`, `W ≥ 0`.
  **Use at `q = s`** for the terminal branch.
- The corank/rank stratification machinery `SchurRecStep`/`core_schurGen_lt_top` (`RouteMSchurGeneral.lean`)
  — the WellFounded-on-corank engine that handles the *inner* `rank Q_b = s` stratification.

**Lean-ready SHAPES (no proofs — statement contracts only):**

    /-- The right-factor rank-split: an `a×b` block Γ, given a full-row-rank `s`-row pivot `σ` of the
        `b×n` matrix Q with `rank Q = s`, splits by a MEASURE-PRESERVING linear chart into an `a×s`
        active block and an `a×(b−s)` kernel block, s.t. `Γ·Q = Γ_act · (Q restricted to σ-rows)` and
        `Γ_ker` does not enter `Γ·Q`. (Right-factor analog of `measurePreserving_shearSub`.) -/
    def rankSplitChart (a b n s : ℕ) (Q : Matrix (Fin b) (Fin n) ℝ) (σ : Fin s ↪ Fin b)
        (hσ : IsUnit (…s-row pivot of Q…)) : (Matrix (Fin a) (Fin b) ℝ) ≃ᵐ
          (Matrix (Fin a) (Fin s) ℝ × Matrix (Fin a) (Fin (b−s)) ℝ)

    theorem measurePreserving_rankSplitChart … : MeasurePreserving (rankSplitChart …) volume volume

    /-- One rank-stratified peel: on the outer stratum `{rank Q_b = s}`, the `a×b` box integral of
        `(frobSq(A·Qt) + frobSq(C·Qt + Γ·Q_b))^{−c'}` is bounded by the banked corank brick at `q = s`
        (block dim `a·s`) times the bounded kernel-box volume, giving the exponent shift `a·s/2`
        (regime A, `c' > a·s/2`) and a terminal branch (regime B, `c' < a·s/2`). -/
    structure RankStratPeelStep (a b n s : ℕ) : Prop where
      shiftA : c' > (a*s : ℝ)/2 → (chart integral) ≤ Cresid (a*s) c' · ∫ (deeperCore)^{−(c'−a*s/2)}
      termB  : c' < (a*s : ℝ)/2 → (chart integral) < ⊤

    /-- The decorated peel-charge, rank-corrected: replaces `peelCharge M u = (M₀−u)(M₁−u)` by
        `rankCharge M u = (M₀−u) · min(M₁−u, min_{i≥2} M i)`.  The gate `minAdm M = rankCharge M u +
        minAdm (redChain u M)` at the binding cut, and `≥` at every cut (this cert, GATE≥). -/
    def rankCharge (M : Fin (L+1) → ℕ) (u : ℕ) : ℕ := (M 0 - u) * min (M 1 - u) (tailMin M)
    theorem minAdm_eq_rankCharge_add_redChain_at_binding … -- (A)'s gate, ℕ form
    theorem rankCharge_add_redChain_ge_minAdm (M) (u) (hu) : minAdm M ≤ rankCharge M u + minAdm (redChain u M)
      -- (GATE≥); NOTE: this is the ≥ at EVERY cut, strictly stronger than the banked ab-form.

**Carry-the-kernel — the honest reading.** The `a·(b−s)` kernel directions are *not* a deeper integral
handed down; at the step they are **bounded box volume** `(2T)^{a(b−s)}` (a constant factor), because on
the kernel `Γ_ker·Q_b = 0` so `Γ_ker` drops out of the anisotropic term (Codex Q2). What is "carried
/ interleaved" is the **shift deficit** `a(b−s)/2` this boundary cannot supply — it is picked up by the
deeper recursion, and (GATE≥)/closure (A) is precisely the statement that the deficit is recovered
*exactly* (`a·s + minAdm(redChain) = minAdm`). So: kernel *variables* = bounded volume at the step;
shift *budget* = carried by the arity recursion, certified to balance by (A).

**The lower-rank strata (the load-bearing (B) obligation — flagged, not closed).** (A) certifies the
**generic** stratum `rank Q_b = s = min(b,n)` (full measure). On lower strata `{rank Q_b = s′ < s}` the
block shift is only `a·s′/2`; by the *tightness* result (closure breaks if `s` is reduced), these strata
**cannot** be folded into the generic charge — they must supply their missing codimension from the
stratum's own geometry (the Grassmannian/determinantal location + the kernel `a`-directions), handled by
the banked corank engine `SchurRecStep`/`core_schurGen_lt_top` (WellFounded on corank) composed with
this arity recursion. A crude additive heuristic `a·s′ + (b−s′)(n−s′)` under-counts (`(4,4,2)` at `s′=1`:
`4+3=7 < 8`), so the sub-stratum bookkeeping needs the genuine stratified accounting — this is the
sharpest thing to verify in the build. It does **not** threaten the (A) truth-value (the true RLCT is
`½·minAdm`, cited; lower strata are higher-codim and cannot lower the threshold), but it is real work.

---

## Firmest result / most likely to break / next step

- **Firmest (certificate):** `minAdmRank = minAdm` — the generic per-boundary charge `a·min(b,n)`
  summed over the recursion equals `minAdm` — **exact, 43,334 chains 0-fail, brute-validated,
  tight (breaks at −1), permutation-invariant, decorrelated-Codex-checked (§ below)**. The `a·s`
  accounting CLOSES; the sjdescent obstruction does not block the headline.
- **Most likely to break it:** *not* the combinatorics (that is settled) but the analytic §B lower-rank
  strata — whether the banked corank engine composed with the arity recursion supplies the lower strata's
  missing codimension without a hidden gap. My crude heuristic shows the accounting there is non-trivial.
- **Next construction/consult:** hand §B's `rankSplitChart` + `RankStratPeelStep` shapes to the
  formaliser; the decisive next probe is an exact-algebra check that the corank engine's per-stratum
  charge (`SchurRecStep` at `q=s′`) composed with the determinantal stratum codimension reaches
  `½·minAdm` on the sub-generic strata — the analog of this cert one level down (the inner corank axis).
