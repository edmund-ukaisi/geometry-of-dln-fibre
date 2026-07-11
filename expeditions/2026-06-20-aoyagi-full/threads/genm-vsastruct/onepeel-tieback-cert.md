# genm-vsastruct — the one-peel TIE-BACK: literal (3,3,3,4) DecoratedPeelStep body

**Seat:** pen-and-paper (scope + obstruction). **Date:** 2026-07-11. **NO Lean.** **Charge:** scope the
full remaining chain from the actual peel object `gammaPeelIntegral(3,3,3,4) t=1` to the banked clean-coords
one-peel — the (a) A₂-casting and (b) chart construction — and locate `det M≠0`. **Decorrelated:**
`codex/tieback-{prompt,answer}.md` (gpt-5.6, xhigh; my lean withheld — it SHARPENED (b) with two load-bearing
catches I under-weighted). Prior: `onepeel334-audit`, `onepeel-tonelli-cert`.

---

## ONE-LINE VERDICT

**The literal (3,3,3,4) one-peel body is BUILDABLE-AS-LABOUR (standard math, not a wall) but is NOT a
mechanical completion of banked lemmas — it needs a genuine new chart/measure construction (b) + a
SECTOR-restricted casting (a) + the `det M≠0` / front-rank-drop control that is a SEPARATE obligation. Two
load-bearing catches (decorrelated): (1) `det M = det Ã₁ ≠ 0` (resolved front full rank) does NOT follow
from the A₀ pivot chart NOR the banked good-chart hyps (counterexample `W=[e₁;e₂], v̄=e₁`: all good-chart
inverses exist yet `det M=0`); its casting Jacobian `|det M|^{−4}` is NONINTEGRABLE over the front near
`{det M=0}` (`∫|det|^{−s}` needs `s<1`), so the casting is valid only on a quantitative sector `{|det M|≥η}`,
and the complement `{det M<η}` (front-rank-drop) is a DEEPER (S,J) corank stratum — a further peel, NOT
rescued by A₂-codim. (2) the unit-clear `L·Γ̂·R=diag(1,δ)` (det-1) does NOT preserve Frobenius energy, so
`U₀,U₁` are a proved COERCIVE COMPARISON (`U_k ≍ ‖·A₂‖²` up to bounded constants on a bounded angular chart),
NOT the definitional equality. So (b) is ~7 genuine pieces, and the bare per-chart closure still owes the
degeneration sector/complement — consistent with `sjJointResolution` remaining the named per-chart gap.**

## The chain (and what is banked / unbuilt)

`box → Σ_charts gammaPeelIntegral [BANKED: sjBoundaryPeel + arity driver] → gammaPeelIntegral(3,3,3,4) t=1
→ [b: CHART pivot+Schur+shear+blow-ups] → literal-A₂ corner slice → [a: A₂-CASTING] → clean-coords
onePeel334 [BANKED, c'<7/2]`.

**Confirmed unbuilt:** NO file connects `gammaPeelIntegral` to `cornerSlice334Integral` — the corner slice
is a DEFINED endpoint, not derived from the actual peel. So (b) is genuinely open.

## (a) The A₂-casting — SECTOR-restricted linear CoV (banked-adjacent)

Consumes: the raw-pi matrix CoV `mulLeftₚ` / `lintegral_comp_mulLeftₚ` (`RouteMSJDecoratedPeelMeas`, the
`Matrix.module` diamond workaround, `lean/CLAUDE.md`) for the linear map `A₂ ↦ (X,Z)`; the box⊃parallelepiped
enclosure (`lintegral_mono_set` + the clean lemma `∀T>0`). Carries the audit's (i)–(iv). **Sharpened:** the
casting Jacobian is `|δ·a_piv·det M|^{−4}` (constant IN A₂), so per fixed front the inner
`∫_{A₂} = |det M|^{−4}·J_clean`; over the FRONT `∫|det M|^{−4}` DIVERGES near `{det M=0}` — so (a) is valid
only on the sector `{|det M|≥η}`, NOT globally. A ~1-module build ON THE SECTOR; the complement is (b)'s
front-rank-drop stratum. [banked-adjacent, sector-restricted.]

## (b) The chart construction — UNBUILT, ~7 pieces, a genuine new chart/measure construction

Codex's decomposition (each piece; banked vs new):
1. **good-coordinate equality** — `gammaPeelIntegral_schurShearFree_eq` + `gammaPeelIntegral_sjGoodMap_eq`.
   BANKED.
2. **row split + `v`-translation** (expose `v` as an integration variable) — banked Tonelli + translation
   atom. PLUMBING.
3. **matrix flatten + Γ-polar CoV** — a `2×2` block IS `ℝ⁴` (measure-preserving flatten), then
   `lintegral_radial_polar_factor` (`N=4` → `r³dr`); the boundary row `v∈ℝ³` → `s²ds`. **The radial
   exponents `|u₀|³,|u₁|²` are STANDARD polar CoVs — NO bespoke matrix-radial/eigenvalue lemma.** BANKED-EXPONENT.
4. **finite angular/projective cover** — polar gives `Γ=rω, ω∈S³`; normalising an entry to reach
   `Γ̂=[[1,β],[γ,γβ+δ]]` needs a FINITE ANGULAR PIVOT COVER. The projective blow-up
   `(u,β,γ,δ)↦u·Γ̂` has Jacobian `|u|³` — a SEPARATE, presently UNBANKED CoV. NEW.
5. **unit-clear + fiberwise `W`-shear** — `L·Γ̂·R=diag(1,δ)`, `det L=det R=1` (banked Schur). ★ BUT
   `‖Γ̂WA₂‖² = ‖L^{−1}diag(1,δ)R^{−1}WA₂‖²` is NOT `‖w₁A₂‖²+δ²‖w₂A₂‖²` — a non-orthogonal det-1 matrix does
   NOT preserve Frobenius norm. What holds is a COERCIVE COMPARISON `U₀ ≍ ‖w₁A₂‖²+δ²‖w₂A₂‖²` with a uniform
   constant on a bounded angular chart. NEW (a proved comparison, not a rewrite).
6. **`v`-polar CoV** — as (3). BANKED-EXPONENT.
7. **coercive corner comparison + domain enclosure** — reading off `U₀,U₁` (via the (5) comparison) + the
   shifted-box domain transport. NEW.

**FACT:** (1),(2),(3),(6) banked/plumbing; (4),(5),(7) are genuine new chart/measure construction. B is
standard mathematics, NOT a research wall, but NOT pure lemma-assembly. **Most-likely-to-break: (5)→(7)** —
treating the det-1 triangular clear as Frobenius-preserving / yielding clean `U₀,U₁` exactly. It yields an
exact matrix factorisation but only a NORM COMPARISON whose uniform constant must be proved. [Codex Q1/Q3.]

## `det M≠0` provenance — a SEPARATE obligation, NOT free from the chart

`M=[w₁;w₂;v̄]`, the 3 resolved front rows. After the shears (rank-preserving),
`det M≠0 ⟺ rank[v;W]=3 ⟺ det Ã₁≠0` (the resolved front factor full rank). **The A₀ pivot chart (pivot
minor invertible) does NOT imply it, and neither do the banked good-chart hyps** (`sjGoodMap_injective`:
`P` left-inv, `W,A₂` right-inv) — counterexample `W=[e₁;e₂], v̄=e₁`: all stated inverses exist yet
`det M=0`. [FACT — Codex Q2.] For fixed rank-2 `W`, the bad `v̄∈rowspan W` is a measure-zero great circle
in `S²`, so `det M≠0` a.e. — **but a.e. does NOT suffice:** the casting Jacobian `|det M|^{−4}` is
nonintegrable near `{det M=0}` (`∫|det|^{−s}` over matrices needs `s<1`; `s=4` diverges), so the neighbourhood
must be controlled by a quantitative sector `{|det M|≥η}`, and the complement `{det M<η}` (front-rank-drop)
is a **DEEPER (S,J) corank stratum** — a further peel of the front factor, NOT the A₂-codim rescue of
`onepeel-tonelli-cert` (that was the DEEP factor `A₂`; this is the FRONT `Ã₁`). [INFERENCE — the front-rank
descent is the (S,J) recursion; consistent with `sjJointResolution` still open.] Alternatively (Codex): avoid
the casting by using the JOINT `sjGoodMap` endpoint directly rather than the `A₂`-casting.

## VERDICT — buildable-as-labour, NOT a mechanical completion; ~7 pieces + the degeneration sector

Literal (3,3,3,4) one-peel body = **{(b) chart [~7 pieces, (4)(5)(7) new] + (a) casting [sector-restricted]
+ onePeel334 [BANKED] + the `det M≠0` sector/front-rank-drop complement}.** All standard math (no research
wall), but the bare per-chart closure still owes: the finite angular/projective chart (b4), the coercive
unit-clear comparison (b5, the most-likely-to-break), and the quantitative `{|det M|≥η}` sector + the
front-rank-drop deeper stratum. This is exactly the residual the still-named `sjJointResolution` per-chart
gap encodes; the clean-coords one-peel + corner334 are the SECTOR endpoint, not the whole chart.

### Firmest / most-likely-to-break / next
- **Firmest.** (b1)(b2)(b3)(b6) are banked/plumbing; the radial exponents `|u₀|³|u₁|²` are standard polar
  CoVs (no bespoke matrix-radial). onePeel334 (clean-coords) + corner334 (sector) are sound (audited PASS).
- **Most likely to break.** (b5)→(b7): the det-1 unit-clear is NOT Frobenius-preserving — `U₀,U₁` are a
  coercive comparison (uniform constant to prove), not an equality. AND `det M≠0`: a separate full-rank
  obligation, `|det M|^{−4}` nonintegrable near `{det M=0}`, needing a quantitative sector + the
  front-rank-drop complement (a deeper (S,J) peel, not the A₂-codim rescue).
- **Next.** Two commissionable builds, both sector-restricted `{|det M|≥η}`: (a) the casting (~1 module,
  `mulLeftₚ` + enclosure + the coercive comparison); (b) the chart (~7 pieces, banked polar/Schur/shear +
  the new angular chart + the coercive unit-clear). THEN the front-rank-drop complement (`{det M<η}`) needs
  the (S,J) deeper-peel — this is where the still-open `sjJointResolution` per-chart content genuinely lives.
  Recommend: build (a)+(b) on the sector FIRST (closes the generic front), and scope the front-rank-drop
  complement as the next (S,J) descent rung (a separate charge). Alternatively evaluate Codex's suggestion
  to bypass the casting via the joint `sjGoodMap` endpoint (avoids the `|det M|^{−4}` artifact entirely).
