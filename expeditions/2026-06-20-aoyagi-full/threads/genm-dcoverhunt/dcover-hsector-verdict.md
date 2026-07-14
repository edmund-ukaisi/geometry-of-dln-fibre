# hole (d) / hsector COVERAGE HUNT — VERDICT

**Seat:** pen-and-paper (obstruction, decorrelated), aoyagi-full Stage 2, `genm-dcoverhunt`.
**Date:** 2026-07-14. **NO Lean, NO build.** Exact ℕ arithmetic over the CURRENT Lean defs
(`minAdm`/`minAdmRec` `RouteMLayerSplit`, `bindingCut` = LEAST achiever `RouteMSJAdm`, `tailMinWidth`
`RouteMSJDeeperFlagCore:458`, deep factor `Z_deep = prod(dropHead(redChain u M))` = `M₂×M_last`).
Scripts `scripts/{defs,hunt_rankdef,hunt_sector_m2frame,hunt_overrun,hunt_secondary,hunt_frame_overrun,
numeric_corank}.py`. Decorrelated `local-codex-consult` (xhigh, my conclusion WITHHELD — asked to
adjudicate the M₂-vs-ρ_Z distinction and coupled convergence from scratch): `codex/sectorrank-{prompt,
answer}.md`. **Codex CONCURS on every point independently.**

Adjudicated against `origin/genm-sj5-good`: `RouteMSJGoodConnector` (the 3-way split + `hsector`/
`hstrict`/`hsat` holes), `RouteMSJDeeperFlagCore` (`shell_corankOffSector_le_unif`, `deeperFlag_shell_le`,
`headSplit_domination`), `RouteMSJShellUniform` (`uniformWenn_le`), `RouteMSJOffSectorBorderline`
(`corankOffSector_borderline_le`), + the covervalid ADDENDUM (`genm-covervalid/cover-hcvg-verdict.md`
§ADDENDUM), the plan of record for the sector discharge.

---

## ★ PRIMARY VERDICT — the covervalid-addendum SECTOR ROUTING is FALSE / mis-scoped (keyed to M₂, not ρ_Z). The sector nonetheless CONVERGES to minAdm/2: a SCOPE correction, not a math wall.

The addendum routes the sector `S₀` as two M₂-keyed sub-cases: **(i)** `a★+b★ ≤ M₂` → `uniformWenn_le`
("deep M₂-frame, no hcvg"); **(ii)** `a★+b★ = M₂+1` → `corankOffSector_borderline_le` (θ-interp,
`hZrank : Z.rank = M₂`). **Both are keyed to the WRONG invariant.** The load-bearing dimension is the
**effective deep rank** `ρ_Z = deepRank = min(M₂,…,M_last) = tailMinWidth` (at a nonempty sector),
NOT the deep-row dimension `M₂`.

### The exact corank-weight threshold keys off ρ_Z, not M₂ (Codex-confirmed, independent derivation)
For a fixed deep factor `Z` (`M₂×M_last`, rank `ρ_Z = min(M₂,M_last) ≤ M_last`), the decoupled corank weight
`Wenn(Z;a,b) = ∫_{A_cor∈matBox b M₂} det((A_cor Z)(A_cor Z)ᵀ)^{−a/2}` is

    Wenn(Z;a,b) < ∞  ⟺  b ≤ ρ_Z  and  a < ρ_Z − b + 1  ⟺  a + b ≤ ρ_Z     (NOT a+b ≤ M₂).

Local model: at a generic corank-1 `X = A_cor·(col-space basis)`, `det(X(CCᵀ)Xᵀ) ≍ |u|²`,
`u ∈ ℝ^{ρ_Z−b+1}`, so the singular locus has codim `ρ_Z − b + 1` and equality `a = ρ_Z − b + 1` is the
LOG endpoint. If `b > ρ_Z` the gram is identically 0 (hard divergence). The `M₂ − ρ_Z` extra columns of
`A_cor` are a passive kernel — they do NOT improve integrability.

### Consequence: the M₂-keyed lemmas are INAPPLICABLE (often literally unsatisfiable) for deepRank<M₂ chains
`uniformWenn_le` needs `Z Zᵀ ⪰ ε²·I_{M₂}` (full row rank `M₂`); `corankOffSector_borderline_le` needs
`Z.rank = M₂`. Since `Z_deep` is `M₂×M_last`, `Z.rank ≤ M_last`, so **whenever `M_last < M₂` the
full-M₂-rank hypothesis is LITERALLY UNSATISFIABLE.** And the decoupled M₂-corank weight genuinely
DIVERGES there (`a+b > ρ_Z`).

**Exhaustive counts (exact, arity 4–6, widths 1–7; matched arity 5 wid 1–10, arity 7 wid 1–5):**
every hcvg-FAILING sector chain (the ones the sector route must carry, `a★+b★ > m`) has

    a★ + b★  =  ρ_Z + 1   EXACTLY   (over-run w.r.t. ρ_Z is EXACTLY 1: 2602/2602 at wid 7)

so the "sub-case i, `a+b ≤ M₂`" bucket (2248/2602) has `ρ_Z < M₂` in **100%** of cases — the decoupled
uniformWenn route the addendum names covers **NONE** of them.

**Numeric confirmation** (`numeric_corank.py`, a guide): witness `M=(2,3,3,2)` (`Z_deep` 3×2, rank 2),
`a★=1,b★=2`: `Wenn` estimate GROWS ~+500/decade as the det-floor → 0 — LOG-DIVERGENT. The hypothetical
full-rank `M₂=3` `Z` (3×3): estimate STABILISES (~103.5, Δ→0) — CONVERGES. The M₂ lemma gives the wrong
verdict.

### But it is NOT a math wall — the sector converges to minAdm/2 (over-run exactly 1)
The buildable/connectable frame at a nonempty sector is the `U_s` `m`-frame, `m = min(M₁,M_last)`. Two
exact structural facts (0 counterexamples over the whole sweep):

- **`m = tailMinWidth = ρ_Z` at every hcvg-FAILING nonempty sector.** (`m ≥ tailMinWidth` always;
  nonemptiness of shell-0 forces `m ≤ tailMinWidth`; and `m < ρ_Z` would need `M₁ < M₂` = a `hpiv`-waist,
  excluded from GOOD. The 156 sweep cases with `m < ρ_Z` are ALL hcvg-HOLDING, `a+b ≤ m` — convergent, no
  borderline, rank-match irrelevant.)
- **Over-run over the buildable `m`-frame `(a★+b★) − m = EXACTLY 1`** (`5252/5252` at wid 8). No
  polynomial over-run, no `b>ρ_Z` hard divergence — the sector is ALWAYS at the `m`-frame LOG-borderline.

At the log-borderline the θ-interpolation over the `m`-frame (Codex Q2, independent): the θ-scaled weight
is finite for `θ·a < ρ_Z − b + 1` (⟺ `θ < 1` at the borderline), and the reduced pivot charge is
`c′ − θ·a★b★/2 < minAdm(redChain t★ M)/2`. With the binding identity
`minAdm(M) = a★b★ + minAdm(redChain t★ M)`, for EVERY `c′ < minAdm(M)/2` the interval
`θ ∈ ((2c′ − minAdm(red))/a★b★, 1)` is nonempty, so the coupled sector is finite; and
`sup_{θ<1}(reachable c′) = minAdm(M)/2` (not attained at equality). Verified `(2,3,3,2)` (`→ 2`) and
`(2,4,4,3)` (`→ 3`).

### The fix (scope correction — bounded labour, matching banked infrastructure)
Discharge `hsector` by a **θ-interpolation borderline over the `U_s` `m`-frame** — the BORDERLINE analogue
of the sorry-free `shell_corankOffSector_le_unif` (which already carries the `U_s` frame + Ky-Fan floor
`Z Zᵀ ⪰ ε²·U_s U_sᵀ` + corank-survival, in the CONVERGENT regime `a+b ≤ m`). Reuse the generic
`enn_geom_interp` + `borderline_real_identity` (both sorry-free) composed over the `U_s` frame, NOT the
M₂-keyed `corankOffSector_borderline_le`. This UNIFIES the sector into ONE case (`m`-frame borderline
`a★+b★ = m+1`); the addendum's "two M₂ sub-cases" dissolve. `uniformWenn_le` / `corankOffSector_borderline_le`
as stated should NOT be invoked at the sector (their M₂-rank hyps fail).

---

## ★ SECONDARY VERDICT — the 3-way cover `routeMBox_le_shellSum` COVERS all shells for all good chains.

The routing case-split in `deeperFlagGood_finite_impl` is a **Nat trichotomy** on `j : Fin (r+1)`
(`j=0` / `0<j<r` / `j=r`) — **exhaustive on `[0,r]` by construction**; no shell falls in NO branch.
Each branch's hypothesis:

- **`j=0` sector (`hsector`).** Inherits the PRIMARY routing issue — dischargeable (converges to
  minAdm/2), needs the `m`-frame borderline correction above. NOT a coverage hole.
- **`1≤j<r` off-sector (`hstrict` → `deeperFlag_shell_le`, needs `hcvg`).** `hcvg` (`a+b ≤ m`,
  `m = min(M₁,M_last)−j`) **HOLDS: 0 failures** over the full sweep (independently re-verified; matches
  covervalid). Frame buildable (see below).
- **`j=r` saturated (`hsat`).** **Always corank-trivial** (`a=0` or `b=0`): `0` non-trivial over the
  sweep.
- **Empty shells.** Shell-`j` is EMPTY for `j < min(M₁,M_last) − tailMinWidth` (`W = prod(tailChain)` has
  rank `≤ tailMinWidth`, so `weakEigCount ≥ min(M₁,M_last) − tailMinWidth`). Every "frame-unbuildable"
  shell (`m > ρ_Z`) is EXACTLY an empty shell (`m > ρ_Z ⟹ M₁ ≥ ρ_Z ⟹ tailMinWidth = ρ_Z ⟹ m >
  tailMinWidth ⟹ empty`): **0 nonempty frame-fails** over the sweep. Empty `shellSpineIntegrand = 0 < ⊤`,
  trivially covered.

So the cover is **SOUND**; the only branch whose *stated discharge* is mis-scoped is `j=0`, and it is a
scope correction, not a missing stratum. (Caveat for the formaliser: the covervalid "nonempty" filter
`m ≤ M₂` is looser than the TRUE nonemptiness `m ≤ tailMinWidth`; the shells with
`tailMinWidth < m ≤ M₂` are empty, not sector-borderline — do not route them to a real analytic bound.)

---

## Close
- **Firmest result.** The sector convergence keys off `ρ_Z = min(M₂,…,M_last) = tailMinWidth`, NOT `M₂`.
  Every hcvg-failing nonempty sector is at the `ρ_Z`-frame LOG-borderline `a★+b★ = ρ_Z+1` EXACTLY
  (over-run 1, no polynomial/hard divergence), with `ρ_Z = m` the buildable frame; the coupled θ-interp
  over the `U_s` `m`-frame reaches minAdm/2 per-`c′` (`sup = minAdm/2`, not attained). The M₂-keyed
  `uniformWenn_le` / `corankOffSector_borderline_le` are inapplicable (unsatisfiable full-M₂-rank hyps)
  for all `deepRank<M₂` sector chains and give the wrong convergence verdict (decoupled M₂-weight diverges,
  numerically confirmed). Off-sector `hcvg` holds (0 fails); saturated is corank-trivial; frame-fails are
  empty. Decorrelated Codex concurs on the M₂-vs-ρ_Z distinction and the per-`c′` reach to minAdm/2.
- **Most likely to break the FIX.** That the `U_s`-frame borderline θ-interp genuinely composes with the
  head-split (`headSplit_domination` Brick D consumes the frame agreement `Zf = Z_deep on G`; the sector's
  shell-0 image sits in the `m`-frame good set `G` with `m = ρ_Z` — the load-bearing structural fact
  `m = tailMinWidth = ρ_Z at hcvg-failing sectors`, which needs its own Lean proof, via `M₁ < M₂ ⟹ waist`
  excluded by `hpiv`). If that structural fact failed off-sample, `m < ρ_Z` could give over-run ≥ 2 (real
  wall) — but 0 counterexamples over arity ≤ 7 / widths ≤ 10.
- **Next construction.** Build `shell_corankOffSector_borderline_le_unif` (the `U_s`-`m`-frame θ-interp
  borderline, `a+b = m+1`), then wire `hsector` through it + the pivot-energy reduced comparator; retire
  the M₂-keyed borderline / uniformWenn from the sector path. Also prove the structural invariant
  `good ∧ nonempty-sector ⟹ min(M₁,M_last) = tailMinWidth = min(M₂,…,M_last)` and the sharp sector bound
  `a★+b★ ≤ tailMinWidth + 1` (both 0-failure over the sweep; the sharp analogue of covervalid's `≤ M₂+1`,
  keyed to the right frame).
