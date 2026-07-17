# redteam-cert — the `d=1, a≥u` corank-one LOCAL DOMAIN-SPLIT (d1design §2) stress-tested to a BREAK

**Seat:** pen-and-paper (obstruction / red-team), `genm-d1split`, Lane 1. **Date:** 2026-07-17. **NO Lean.**
Adjudicates: *does d1design's two-branch domain-split (dispatch by `σ_min(Q̃ₚ)`: ill→`_inner_bounded`,
well→`_inner_peel`) actually close the `d=1, a≥u` corank-one arm of `innerCorankDescent_lt_top`, with a
finite bound below `½·minAdm(M)` — or does a positive-measure region escape both branches?*
Verified two decorrelated ways that CONVERGE: my exact-algebra radial-exponent count + exact-ℕ census
(`minAdmRec` transcription) + Monte-Carlo guide, and a decorrelated `local-codex-consult` (xhigh, my
conclusion WITHHELD — `codex/split-redteam-{prompt,answer}.md`). Consumes the socket
`RouteMSJDecoratedPeelStep.lean` + `RouteMSJFreedPeel.lean` + `RouteMSJGammaAtom.lean` @ `origin/genm-integration`,
and d1design's `d1-atom-spec.md` §2 / `d1-build-plan.md` §2b.

---

## ★ VERDICT (LEAD) — the split as SPECIFIED does NOT close; it needs a MILD LOCAL DECORATION (native, buildable)

**The two-branch split, dispatched by the ABSOLUTE conditioning `σ_min(Q̃ₚ) < δ`, has a genuine gap.** A
**positive-measure cone** — the corner where the pivot `Q̃ₚ → 0` *radially* (all `u` singular values
comparably small), with `Q_b = O(1)` — is routed to the **bounded** branch (because `σ_min(Q̃ₚ)` is small
there), but the bounded branch **discards the corank block's charge** and its majorant **diverges** for
every `c'` in the open window `(½·minAdm((t,M₁,M₂,…)), ½·minAdm(M))`. The peel branch is *not dispatched*
there. The true integral is finite (the theorem holds), so this is **not a wall**; but the SPLIT is an
**incorrect proof** as written, and the arm d1design flagged as thinnest is where it breaks.

- **CLASSIFY: NEEDS A MILD LOCAL DECORATION — EXPENSIVE-TRANSCRIPTION (native, buildable).** NOT a new cite,
  NOT a new global decoration, NOT open-problem. The repair is a **radial-peel sub-branch** (blow up the
  radius `‖Q̃ₚ‖`, peel on the sphere where the pivot coefficient is bounded below) OR a **scale-invariant
  (relative-conditioning) dispatch** `σ_min(Q̃ₚ)/‖Q̃ₚ‖`. Both are native + use the banked peel/gammaAtom.
- **KILL (bake as a kill-condition):** the dispatch criterion *"`σ_min(Q̃ₚ) < δ` ⟹ bounded branch"* is
  **UNSOUND**. The bounded branch is sound **only where the pivot energy `w = frobSq(P·Q̃ₚ)` is bounded
  below** (which includes the pure rank-`(u−1)` drop d1design *intended*: there `σ_max(Q̃ₚ) = O(1)` ⟹
  `w = O(1)`). It is UNSOUND where `w → 0` (the radial corner `Q̃ₚ → 0`), which `σ_min < δ` erroneously sweeps in.
- **The precise error in d1design §2.** The flag judged *"the §1 atom handles `w → 0`; the bounded branch
  handles the `Q̃ₚ`-drop where `w` is bounded below."* The first clause is FALSE for `c'` above the
  pivot-only threshold: the §1 front-collapse atom applied to the bounded branch runs at the **full** exponent
  `c'` and reduces the pivot front `[P|B₁₂]` (only `t×M₁`, not `M₀×M₁`) to `hIH`, so it caps at
  `c' < ½·minAdm((t,M₁,M₂,…))`, **strictly below** `½·minAdm(M)`. The corank block's charge is required *even
  at the origin corner*, and the bounded branch throws it away.

---

## 1. The exact mechanism (why the bounded branch fails at the radial corner)

Setup (the socket, `b=1`, `a≥u=t`): `P` (`u×u`, invertible box), `B₁₂` (`u×1`), `C` (`a×u`), `Γ` (`a×1`);
tail product `Q` with top block `Q_p` (`u×q`), bottom row `Q_b` (`1×q`); `Q̃ₚ = Q_p + P⁻¹B₁₂Q_b`;
`w = frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·Q)`; `freedSchurLoss = w + frobSq(C·Q̃ₚ + Γ·Q_b)`.

**The two banked inner-`Γ` branches BOTH require `w > 0` (`hpiv`, `RouteMSJFreedPeel:118,158`).**
- `_inner_bounded`: `∫_Γ (freedSchurLoss)^{−c'} ≤ w^{−c'}·vol(box)` — drops the corank term entirely.
- `_inner_peel` (gammaAtom weld `R = Q_b`, emits `‖Q_b‖^{−a}`, `RouteMSJGammaAtom:142`): needs also
  `hG : (Q_bQ_bᵀ).PosDef` (`Q_b ≠ 0`) and `hc' : a·b/2 < c'`.
  — **Note (corrects d1design §2):** the banked `_inner_peel` emits the CORANK-tail Gram
  `det(Q_bQ_bᵀ)^{−a/2} = ‖Q_b‖^{−a}`, **not** the pivot Gram `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` (the latter would come from
  integrating `C` against `R = Q̃ₚ`, a *different* step needing `u ≤ q−b`). d1design §2 conflates the two.

**The radial corner.** Take `Q̃ₚ = ε·V` (`V` a fixed direction, `‖V‖=1`), `Q_b = O(1)` bounded away from 0,
`P` fixed invertible. Then `w = ε²·frobSq(P·V)` and
`freedSchurLoss = ε²·frobSq(P·V) + frobSq(ε·C·V + Γ·Q_b)`. Rescale `Γ = ε·H` (`dΓ = ε^{ab}dH = ε²dH`):

    ∫_C ∫_Γ (freedSchurLoss)^{−c'} dΓ dC  ≍  ε^{2 − 2c'} · K,   K < ∞ for c' > 1
    (the H-integral converges: dim Γ = ab = 2, and 2c' > 2).

`Q̃ₚ` is a **free** coordinate near 0 (translate `Q_p ↦ Q̃ₚ`, Jacobian 1; for `M=(4,3,2)` the tail is a single
free layer so `Q_p` is a free box). The shell `{‖Q̃ₚ‖ ≍ ε}` has measure `≍ ε^{uq−1}dε`. Radial integral:

| branch | inner-`Γ,C` exponent | × shell | net radial | converges iff |
|---|---:|---|---|---:|
| **true** integral | `ε^{2−2c'}` | `ε^{uq−1}dε` | `ε^{uq+1−2c'}dε` | `c' < (uq+2)/2` |
| **bounded** majorant `w^{−c'}` | `ε^{−2c'}` | `ε^{uq−1}dε` | `ε^{uq−1−2c'}dε` | `c' < uq/2` |

The gap between the two thresholds is exactly **`1`** (`= ab/2 = a·b/2`), the charge the corank block carries
and the bounded branch discards. For the two witnesses (`uq/2` = pivot-only `½minAdm`, `(uq+2)/2` = full `½minAdm`):

- **`M=(4,3,2)`, `t=2`** (`u=2,a=2,b=1,q=2`, tail = one free `3×2` layer): true converges `c'<3`, bounded
  converges only `c'<2`. **Binding window `c' ∈ (2,3)`.** Divergences at the endpoints are logarithmic.
  (`½minAdm((4,3,2))=3`, `½minAdm((2,3,2))=2` — exact ℕ, `minAdmRec`.)
- **`M=(3,2,2)`, `t=1`** (`u=1,a=2,b=1,q=2`): here `σ_min(Q̃ₚ)=‖Q̃ₚ‖`, so the ENTIRE "ill" piece IS the
  origin neighborhood. True `c'<2`, bounded only `c'<1`. **Binding window `c' ∈ (1,2)`.**

**Numerics (guide only).** For `M=(4,3,2)`, `c'=2.5`: measured inner-`(C,Γ)` growth exponent ≈ `3.0 = 2c'−2`
(vs bounded `2c'=5`). For `M=(3,2,2)`, `c'=1.5`: measured ≈ `1.05 ≈ 2c'−2 = 1`. Both match the exact count.

## 2. It is a POSITIVE-MEASURE escape, set-theoretically covered

The split covers the domain set-theoretically (`σ_min < δ` or `≥ δ`), so nothing is *unassigned*. But the
assignment is wrong: an **open angular cone** around a fixed full-rank direction `V` in `S^{uq−1}`, at small
radius, has positive surface measure, satisfies `σ_min(Q̃ₚ) < δ`, and is therefore routed to the bounded
branch on which the majorant is non-integrable for `c'` in the window. Codex (decorrelated) states the same:
*"a positive-measure cone escapes both successful estimates: PEEL is not dispatched there, and BOUNDED is
non-integrable. The actual integral remains finite."*

## 3. The repair (native, buildable — the local decoration)

**Radial-peel sub-branch.** Polar-blow-up the pivot: `Q̃ₚ = ρ·Θ`, `ρ = ‖Q̃ₚ‖`, `Θ ∈ S^{uq−1}`; equivalently
rescale `Γ = ρ·H`. Apply the banked peel on the sphere. The pivot **coefficient** after removing `ρ²` is

    ‖P·Θ‖_F²  ≥  σ_min(P)² · ‖Θ‖_F²  =  σ_min(P)²  > 0        (P injective, Θ ≠ 0)

**bounded below on the compact sphere — and it does NOT require `Θ` full rank** (only `Θ ≠ 0`). So the peel /
gammaAtom applies uniformly on `S^{uq−1}`, the residual `(‖P·Θ‖² + ‖C·Θ(I−P_{Q_b})‖²)^{−(c'−ab/2)}` is
bounded (the `‖P·Θ‖²>0` term blocks the `C`-integration from ever forming a `det(Q̃ₚQ̃ₚᵀ)`/`σ_max(Q̃ₚ^⊥)`
divisor), and the radial integral `∫ ρ^{uq−1 − 2(c'−ab/2)}dρ = ∫ ρ^{uq+1−2c'}dρ` converges for `c' < (uq+2)/2`
= the full `½·minAdm`. This single sub-branch closes the whole `{‖Q̃ₚ‖ small}` region (origin corner AND pure
rank-drop together), so it can REPLACE the bounded branch on the ill piece.

**Equivalent framing (Codex):** dispatch scale-invariantly by the **relative** conditioning
`σ_min(Q̃ₚ)/‖Q̃ₚ‖_F` instead of the absolute `σ_min(Q̃ₚ)`. The radial corner has good *relative* conditioning
(`σ_min/σ_max ≍ 1`) and lands on the peel side; only the genuine rank-`(u−1)` drop (relative conditioning `→0`,
`w = O(1)`) lands on the bounded side, where the bounded branch is sound.

**Either repair is native + banked** (blow-up + `_inner_peel`/`gammaAtom_aniso_shifted_eq` + `hIH`). It is a
mild LOCAL decoration of the dispatch, not a global carried weight, not a cite.

## 4. Scope of the obstruction (exact-ℕ census, `minAdmRec`)

The gap is present exactly when the corank block carries nonzero charge, i.e. `minAdm((t,M₁,M₂,…)) < minAdm(M)`:

- **`d=1, a≥u` cuts (arity 3–5, widths ≤ 5): 1221 / 1395 have the gap** (88 %). The bounded branch caps
  strictly below `½·minAdm(M)` on all of them.
- **No-gap: 174 / 1395** — where `minAdm((t,M₁,M₂,…)) = minAdm(M)` (the corank block contributes no charge),
  e.g. `M_last = 1` cells (`(2,2,1,1)`, `(3,2,1,1)`, `(4,3,1,2)@t=2`). ONLY on these is the bounded branch on
  the ill piece already sufficient — these are the cells for which d1design's split (as written) happens to work.
- The gap is present for both `a = u` (marginal, e.g. `(4,3,2)`) and `a > u` (e.g. `(3,2,2)@t=1`, window `(1,2)`;
  `(3,2,3)@t=1`, window `(1,2.5)`).

## 5. Caveats surfaced (two more corners, pre-existing)

- **`Q_b → 0` is a SEPARATE corner.** The peel emits `‖Q_b‖^{−a}`; near the null set `{Q_b = 0}` this weight
  needs its own handling (a drop-transverse / null-set argument). Not the corner red-teamed here, but on the
  repair's checklist.
- **`P → singular` is a SEPARATE degeneracy.** The sphere lower bound `‖PΘ‖² ≥ σ_min(P)²` is only *pointwise*
  in `P`; uniformity needs a uniformly-invertible `P`-subbox, i.e. the pre-existing front-collapse
  dominant-minor cover (`d1-build-plan §2a` atom 1). The repair inherits, not worsens, this.
- The displayed peel "equality" is exact over `ℝ^{ab}` and an **upper bound** over the finite shear box (fine
  for finiteness); the stated corner asymptotic needs `0` in the box interior (holds — `genBox` is centered).

## 6. Decorrelated confirmation

`local-codex-consult` (xhigh, conclusion withheld — I gave it the setup + the split + the questions, NOT my
verdict). It independently reproduced: the exact exponents (`ε^{5−2c'}` true vs `ε^{3−2c'}` bounded; endpoint
divergences logarithmic), the positive-measure-cone escape, and the fix (polar blow-up in `Q̃ₚ` / scale-invariant
split, `‖PΘ‖²≥σ_min(P)²>0` on the sphere, NOT requiring `Θ` full rank). It added the two caveats in §5 and the
scale-invariant-dispatch framing. Full artefact: `codex/split-redteam-{prompt,answer}.md`.

## Close

- **Firmest result.** d1design's `d=1 a≥u` split, dispatched by the absolute `σ_min(Q̃ₚ)<δ`, is an incorrect
  proof: the radial corner `{Q̃ₚ→0, comparable singular values}` (positive measure, `σ_min<δ`) is routed to the
  bounded branch, whose majorant diverges on the window `c' ∈ (½minAdm((t,M₁,M₂,…)), ½minAdm(M))` — a window of
  positive length on **1221/1395** `a≥u` cuts. Exact witnesses `M=(4,3,2)` (`c'∈(2,3)`), `M=(3,2,2)` (`c'∈(1,2)`),
  exact radial-exponent count, matched by numerics and a decorrelated Codex. The bounded branch is sound only
  where `w = frobSq(P·Q̃ₚ)` is bounded below (the intended rank-`(u−1)` drop), NOT wherever `σ_min(Q̃ₚ)` is small.
- **Most likely to break THIS finding.** (i) If the tail `Q_p` is NOT free at deeper arity (a genuine product),
  the origin corner couples to the deep tail and the shell-measure count changes — I verified the FREE case
  (arity-3 witness `M=(4,3,2)`, single tail layer); for deeper chains the corner is reached by a deep-tail /
  front cancellation and the `hIH` recursion must absorb it (expected finite, not re-checked exactly here). (ii)
  If a formaliser reads "peel branch" as `_inner_peel` used a.e. on the WHOLE domain (no bounded branch), that
  route DOES capture the corner (`ε^{2−2c'}`) but introduces a `σ_max(Q̃ₚ^⊥)^{−2}·‖Q_b‖^{−a}` weight elsewhere
  that is marginal/log-divergent on `{rows of Q̃ₚ ∥ Q_b}` — so "peel everywhere" is not clean either; the
  radial-peel sub-branch (which keeps `‖PΘ‖²>0` and never forms that divisor) is the clean route.
- **Next.** Hand the formaliser the **radial-peel sub-branch** (or the scale-invariant dispatch) as the
  corrected ill-piece mechanism, with the sharpened per-region thresholds: bounded branch ONLY where
  `w` is bounded below (rank-`(u−1)`, `c'` up to `½minAdm((t,M₁,M₂,…))` suffices there anyway); radial-peel on
  `{‖Q̃ₚ‖ small}` for `c'` up to the full `½minAdm(M)`. Verify the deeper-arity coupling (i) and the `Q_b→0`
  corner (§5) before the tide sinks in.

Files (absolute): `…/threads/genm-d1split/redteam-cert.md` (this);
`…/threads/genm-d1split/codex/split-redteam-{prompt,answer}.md` (decorrelated). Consumes:
`RouteMSJDecoratedPeelStep.lean`, `RouteMSJFreedPeel.lean`, `RouteMSJGammaAtom.lean` @ `origin/genm-integration`;
d1design `d1-atom-spec.md` §2 / `d1-build-plan.md` §2b @ `origin/genm-d1design`.
