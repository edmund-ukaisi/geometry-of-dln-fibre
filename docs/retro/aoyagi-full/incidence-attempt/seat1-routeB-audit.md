# Seat-1 audit — does "route B" (full-matBox + S3/deep-floor) close to T1?

**Seat:** pen-and-paper (witness), aoyagi-full retro. **Date:** 2026-07-15. **No Lean edits.**
Sources read: `routefork-cert.md` §5–§6; Lean on `origin/genm-sj5-brickdcont` —
`RouteMLayerSplit.lean` (`redChain`/`minAdm`), `RouteMSJDeeperFlagCore.lean:458` (`tailMinWidth`), `:339`
(`deeperFlagCoreIntegrand`), `:517`/`:660` (`hpiv`), `:245–300` (`shell_corankOffSector_le_unif`);
`RouteMSJPivotBlowup.lean:154` (`pivotBlock_radial_blowup`); `RouteMSJLedger.lean:94` (`commonDivisor`);
`RouteMSJCornerComparator.lean:116` (`decLoss`). Exact rationals: `verify_routeB.py` (alongside).

## VERDICT

**Route B does NOT close to T1. It ceilings AND re-couples at the binding corner — two independent breaks,
both landing on `(2,2,3)`.** Route B is sound only on `M₂≤M₁` cuts (verified `(3,3,3)`, tight); the binding
corner `(2,2,3)` and every `M₂>M₁` in-scope cut fall outside it. The incidence machinery (or a genuinely
coupled estimate) is **REQUIRED** for those cuts, not fallback. **Recommendation: do not spawn a route-B tide
expecting it to reach `headSplit_domination` at `c'<T1` for all cuts** — it will wall at the waists, and the
`C_hle`/assembly step is the F4 obstruction in disguise, not plumbing.

---

## Q1 — the ceiling, reconciled with my §4a. FACT.

**The brief's premise is factually wrong: `tailMinWidth` INCLUDES `M₁`.** The Lean def
(`RouteMSJDeeperFlagCore.lean:458`) is `tailMinWidth M = inf_{i:Fin(L+2)} M(i.succ) = min(M₁,M₂,…,M_last)`.
For `L=0`, `tailMinWidth(M₀,M₁,M₂) = min(M₁,M₂)` — e.g. `tailMinWidth(2,2,3)=2`, **not** `M₂=3`. So

    u·tailMinWidth = u·min(M₁,M₂,…) = u·ρ   with ρ my §4a value (M₁ INCLUDED).

**⇒ route-B step-4 delivers codim `u·ρ` — identical to my §4a decoupled pivot codim. The two routes do NOT
differ; route B *is* the decoupled route.** No contradiction to reconcile; §4a and route B agree.

**For `L=0`, `hpiv ⟺ M₂ ≤ M₁`.** `redChain u (M₀,M₁,M₂) = (u,M₂)` (a `Fin 2` leaf), so
`minAdm(redChain u M) = u·M₂`; hence `hpiv : u·M₂ ≤ u·min(M₁,M₂) ⟺ M₂ ≤ M₁`. This is exactly Codex's
`M₂≤M₁` scope, arrived at independently through the recursion's own definitions.

**Chain ceiling `c' < ab/2 + u·tailMinWidth/2`, exact (`verify_routeB.py`):**

| chain / cut | a,b | T1 | minAdm(red) | u·tailMinWidth | hpiv? | route-B ceiling | shortfall T1−ceil | M₂>M₁ |
|---|---|---|---|---|---|---|---|---|
| `(2,2,3)` u=1,j=1 (BINDING) | 1,1 | 2 | 3 | 2 | **FAIL** | 3/2 | **+1/2** | yes |
| `(3,3,3)` u=2,j=1 | 1,1 | 7/2 | 6 | 6 | hold (tight) | 7/2 | 0 | no |
| `(3,3,4)` u=2,j=1 | 1,1 | 4 | 8 | 6 | **FAIL** | 7/2 | +1/2 | yes |
| `(3,3,7)` u=2,j=2 | 1,1 | 9/2 | 14 | 6 | **FAIL** | 7/2 | +1 | yes |

The peel bound the brief invokes, `T1 ≤ ab/2 + u·tailMinWidth/2`, **requires `hpiv`** (to replace
`minAdm(red)` by `u·tailMinWidth`). Where `hpiv` fails, `ab + u·tailMinWidth < minAdm(M)` (verified: `3<4`,
`7<8`, `7<9`), so the ceiling drops strictly below `T1`. **`(2,2,3)` — the zero-slack binding corner on which
the whole `rlct=C/2` result hinges — is a waist (`hpiv` fails), ceiling `3/2 < T1=2`.** The routefork cert
itself concedes "Waists (`hpiv` fails) are a SEPARATE base case" (§6) but does not specify what proves them;
the binding corner is precisely such a waist, so the capstone's most load-bearing case is deferred to an
unspecified base case. **If waists need the incidence charts, the charts are REQUIRED, not fallback.**

**Answer to Q1's sharp form:** the step-4 rank is `u·tailMinWidth = u·min(M₁,M₂,…)` (M₁ **included**), not
`u·min(M₂,…)`. Route B ceilings `< T1` exactly on the `M₂>M₁` cuts (shortfall `1/2` at both `(2,2,3)` and
`(3,3,4)`, `1` at `(3,3,7)`), closing only on `M₂≤M₁` (`(3,3,3)` tight). Route B cannot close the binding
corner.

---

## Q2 — the coupled weight (my F4). FACT: the composition genuinely re-couples.

**The target shape is A_cor-free; reaching it from `freedSchurLoss` is not.** `deeperFlagCoreIntegrand`
(`:339`) carries the pivot weight `(cornerComparator (redChain u M) k jc).decLoss v z`, which
(`RouteMSJCornerComparator.lean:116` + `RouteMSJLedger.lean:94`) equals

    decLoss = commonDivisor(e)(v)² · frobSq(prod (redChain u M) z) = commonDivisor² · ‖Q_p‖_F²   — A_cor-FREE.

`shell_corankOffSector_le_unif` (`:259`) is correspondingly stated for a **fixed real `w`** and a **fixed
`Ccross`** (both A_cor-free). But `pivotBlock_radial_blowup` (`:154`) applied to the actual pivot term
`‖[P|B₁₂]·hsQ‖²` (= `‖P·Q_p + B₁₂·Q_b‖²`, `Q_b=A_cor·Z`) yields

    ∫_{[P|B₁₂]} φ(‖[P|B₁₂]hsQ‖²) = ∫_sphere ∫_r r^{uM₁−1} φ(r²·‖P̂·hsQ‖²),

and the exposed pivot factor `‖P̂·hsQ‖² = ‖P̂_p Q_p + P̂_b Q_b‖²` **depends on `A_cor` through `Q_b`.**

**No A_cor-free lower bound exists:** for adversarial `A_cor`, `P̂_b Q_b` cancels `P̂_p Q_p`, driving
`‖P̂·hsQ‖²→0`. So the coupled pivot factor cannot be replaced by any A_cor-free `w>0`, and the
`step 2 → step 3` composition cannot supply `shell_corankOffSector_le_unif`'s A_cor-free `w`. **The
deep-factor floor `ZZᵀ⪰ε²U_sU_sᵀ` floors `Z` (the scale of `Q_b`) but does not stop the cancellation** — it
controls the corank block `frobSq(Ccross+Γ·A_corZ)`, not the pivot block. So it does not decouple `w`.

**This is exactly F4:** "K5 does NOT decouple the pivot weight; any decoupling strong enough to feed K4 IS
the missing incidence estimate." The routefork cert's step 2 ("blow-up exposes
`decLoss = commonDivisor²·frobSq(Q_p)`") states the *target* A_cor-free shape but not a mechanism to reach it;
the actual blow-up gives the A_cor-coupled `r²‖P̂·hsQ‖²`. **So the cert's "genuine remaining brick" (the
assembly, steps 1–5) is the F4 obstruction, not bounded plumbing** — the same reason the incidence route was
built. This break is present for **every** cut (independent of `hpiv`/`M₂≤M₁`), because the pivot term is
intrinsically A_cor-coupled.

**Pointwise-in-z? — and the §4b cross-check.** If the assembly did produce the A_cor-free `decLoss`, the
`shell_corankOffSector_le_unif` bound `Cunif·w^{−(c'−ab/2)}` with `w=commonDivisor²‖Q_p‖_F²` would be
**pointwise in z, `Cunif` uniform**. But §4b (`verify_R1_wall.py`) proved that pointwise bound is FALSE on the
`b<j` strata: as `σ_min(Q_p)→0` with `‖Q_p‖_F` floored, the LHS `→∞` while `commonDivisor²‖Q_p‖_F²` stays
`O(1)` (`commonDivisor=∏|z_ℓ|^k` is a monomial, `frobSq=‖Q_p‖_F²`; neither tracks `σ_min`). So a uniform
`Cunif` cannot exist at those strata — an independent confirmation that the assembly cannot close there. Note
`(3,3,7)@u=2,j=2` is simultaneously a route-B waist (`hpiv` fails, Q1) **and** a `b<j` stratum (`b=1<j=2`,
§4b): the two obstructions coincide.

**Answer to Q2:** the composition genuinely re-couples. The deep-factor floor does not replace `w` by an
A_cor-free lower bound; step 2→3 needs the coupled estimate (= F4 = the incidence estimate). The composed
bound would be pointwise-in-z if it existed, but §4b shows no uniform `Cunif` exists at the `b<j` strata.

---

## What this means for the tide (plainly)

- Route B is **sound and closes to T1 only for `M₂≤M₁` cuts** (`hpiv` holds; `(3,3,3)` verified, tight). The
  banked corank-half (`shell_corankOffSector_le_unif`) and comparator (L1) are genuinely useful **there**.
- Route B **cannot** reach `headSplit_domination` at `c'<T1` for `M₂>M₁` cuts — including the binding corner
  `(2,2,3)`. Two independent breaks: (Q1) the `hpiv` gate fails ⇒ step-4 ceiling `< T1`; (Q2) the step 2→3
  assembly is F4 (A_cor-coupled pivot weight, not decouplable by the deep floor).
- **The incidence charts are REQUIRED** for the `M₂>M₁` / waist cuts (the cert's "off-path" verdict on them is
  what leaves the binding corner unproven). Equivalently: adopt the coupled coordinatization
  (`freedSchurLoss=‖UR+WX‖²+‖WY‖²`, `seat1-design.md` §1) and prove the coupled incidence estimate there.
- **Do NOT** spawn a build tide that fills `headSplit_domination` via route B expecting T1; it will wall at the
  waists. Scope a route-B tide, if at all, to `M₂≤M₁` cuts explicitly, and open the waist/incidence brick as
  the real remaining analytic content.

## FACT / INFERENCE

- **FACT (from Lean defs + exact rationals):** `tailMinWidth` includes `M₁`; `hpiv⟺M₂≤M₁` (L=0); the ceiling
  table; `hpiv` fails at `(2,2,3)`,`(3,3,4)`,`(3,3,7)` and holds tight at `(3,3,3)`; `decLoss` is A_cor-free
  while `pivotBlock_radial_blowup` exposes the A_cor-coupled `‖P̂·hsQ‖²`; `shell_corankOffSector_le_unif`
  requires A_cor-free `w`.
- **INFERENCE:** that the assembly step 2→3 has no A_cor-free-`w` route (the cancellation argument shows no
  positive A_cor-free lower bound; I did not exhaustively rule out an exotic non-lower-bound assembly, but the
  §4b pointwise-failure independently blocks the uniform-`Cunif` conclusion). That waists require the incidence
  charts specifically (they require *something* beyond route B; charts are the on-branch candidate).
