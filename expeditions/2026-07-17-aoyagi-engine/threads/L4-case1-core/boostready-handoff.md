# boostReady handoff — the wall's last obligation (seat-L4 → seat-L4B / successor)

**Target:** `realBranch_boostReady_case11` (`Case1Wire.lean:386`), the sole open obligation of
`case1_preserves_stepInv'` (the wall). Statement (elder-blessed, ruling B, canonical `0ce9c68b9`):
```
(hδ : edgeδ d p = true) (hc11 : ed.case = case11) (hbranch : (p.extend ed).IsRealBranch e)
(hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
           (supportAt d p.conState.layer p.conState.cleared) (supportLayerOf p.conState) (foldRegion d e p))
  ⊢ Deg1SupportedOn (foldResid d e p) ed.center (foldRegion d e p)
```

## Verdict — INSUFFICIENT-as-baked but PROOF-SIDE (statement layer STAYS closed; no re-bake)

Three-way decorrelated convergence on the sufficiency flag:
- **seat-L4 (me):** `realBranch_canonicalSchurStep hbranch : CanonicalSchurStep d p.conState ed.shearφ` is
  about the CURRENT edge's shear, but `foldResid p` is built from p's ANCESTOR shears — mis-aimed at the
  top level.
- **elder (frame-only, blind to Codex):** same flag; resolved PROOF-SIDE — `IsRealBranch`'s recursive
  `.step` holds `CanonicalSchurStep` at EVERY ancestor edge, so boostReady IS provable from `hbranch`
  as it stands, via a PATH-INDUCTION over p's ancestors (not a one-liner). Three baked ingredients stay.
- **Codex (bufv05qfv) — DISAGREES with the elder, STATEMENT-SIDE (needs a stronger invariant, not just a
  proof lemma):** the formal `CanonicalSchurStep d s shearφ := ∀ u k, shearφ u k ≠ 0 → k in carve interior`
  is TOO WEAK — **`shearφ := 0` (identity) satisfies it VACUOUSLY** (and `blockShear 0 = id` satisfies
  `ShearWithinCarveRaw`), so the current `IsRealBranch` ADMITS an unprepared/identity earlier shear = exactly
  `R_bad` (untouched coeff lacks the reused-pivot factor, yet still affine on the full block ⟹ satisfies
  `hslot`). The recursive ancestor predicates record only SUPPORT, **NOT the equation `shearφ = canonShearOf`**
  — so the path-induction cannot rewrite any stored shear via `canonShearOf_apply_interior`. **Codex fix: pin
  `shearφ = canonShearOf d p.conState` in `IsRealBranch`'s step-arm (≥ case12/case2)** — a STATEMENT change to
  a baked def (elder delta-read), re-opening the "statement layer closed" claim. Drop-test: `hslot` CONSUMED
  (both instruments agree). **⚠ ELDER↔CODEX DISAGREEMENT — controller reconciling; seat-L4B must NOT build on
  the elder's "provable-as-is" premise until reconciled: if Codex is right, sub-lemma (b) is impossible until
  the shear-equation is pinned in IsRealBranch.** Codex's path-induction shape (post-fix): `Case11BChainCoeffs`
  (∃ prepared `a,b` with `a i = u_q · b i` for `i ∈ S∖C`, coeffs ignore `C`) + a helper
  `ed.pivot ∉ supportAt d p.conState.layer p.conState.cleared` for δ=1 case11. Full Codex answer:
  `codex/boostready-proof-answer.md`; final assembly (conditional on the fix + lemma) in §2 there.

**DROP-TEST (elder):** `hslot` IS consumed (boost-readiness over `ed.center` needs the carried base +
the current pivot's b-chain position) → `hslot` STAYS. Weakest honest form confirmed.

## The weakest honest form — TWO sub-lemmas (elder decomposition)

**(a) [seat-L4B, self-contained, commissioning now]** combinatorial b-chain divisibility on `foldB p`:
`u_p ∣ b_i ⟺ i > J₁`, NO shear input — reads off `foldB`'s construction (`MonumentAtlas:402`,
`foldB_extend_eq:492`) by b-chain induction. Separates clean. Ground truth: pnp-boost's
`case11_boost_readiness.py` (banked) + my `case11_boostready_crosscheck.py` — the fact is SETTLED math,
only the formalization route is open.

**(b) [successor, the genuinely new content]** the prepared-form PATH-INDUCTION on `foldResid p`
(`MonumentAtlas:443`) consuming ANCESTOR `CanonicalSchurStep`: at each ancestor edge the per-edge
projection `realBranch_canonicalSchurStep` (`MonumentAtlas:1016`) is usable INSIDE the induction (NOT a
top-level discharge). The γ-clearing is what `R_bad` violates (see below) — this is where the real work is.

Assembly: (a)+(b) re-express `hslot` (foldResid p degree-1 on the full block `S_full`) over
`ed.center = {pivot} ∪ partial`: partial-block terms carry over; untouched (`S_full∖partial`, i.e. `i>J₁`)
terms are absorbed into `c'_pivot·u_pivot` via (a); coeffs `c'` ignore `ed.center`. Conclusion is
`Deg1SupportedOn ed.center`, which feeds `stepInv_child_delta1_append` (banked) — identical to the case12
cover route, only the `Deg1SupportedOn` source differs.

## The R_bad countermodel — why the prepared form (sub-lemma b) is IRREDUCIBLE
From my Codex cross-check (`codex/boost-readiness-2222-answer.md`) + `case11_boostready_crosscheck.py`
(re-verified by me): on (2,2,2,2), `R_bad = Z·B·[[1,β],[γ,u_p]]` (an UNPREPARED shear, off-diagonal
`γ ≠ 0`) has FULL-support Deg1 (every entry degree-1 in the B-block) AND the same scalar `foldB` — yet is
NOT boost-ready: center-zeroing leaves `γ·(b₀₁z₀₀ + b₁₁z₀₁) ≠ 0`, and `÷u_pivot` fails. So boost-readiness
does NOT follow from "full-support-Deg1 + scalar-foldB" alone — CanonicalSchurStep (γ Schur-cleared, the
prepared form) is the load-bearing extra, and it enters only via the ancestor path-induction (b). The
actual (2,2,2,2) fold IS boost-ready (A1/A2/A3 all pass) — the fact is true; (b) is the route.

## Exact ingredient locations (Case1Wire + MonumentAtlas + CanonShear)
- Target: `Case1Wire.lean:386` `realBranch_boostReady_case11` (sorry). Caller passes `hslot = hinv.2`
  from `case1_conjA` (`Case1Wire.lean:402`).
- `foldResid` def `MonumentAtlas:443`; `foldB` `:402`; `foldB_extend_eq` `:492` (the `u_pivot^δ · (foldB∘stepMap)` ratio); `foldNR` `:413`.
- `CanonicalSchurStep` def `MonumentAtlas:819`; `realBranch_canonicalSchurStep` (per-edge projection) `:1016`.
- `canonShearOf_support` `CanonShear.lean:63`; `canonShearOf_apply_interior` (the `−u_γ·u_β` interior value, the α/β witness) `:244`.
- `Deg1SupportedOn` / `Deg1SupportedSlot` / `IgnoresCoords` in `Core/Aoyagi/PrincipalInv.lean`;
  `foldRegion_eq_univ` (region = univ) in `MonumentAtlas`.
- On close: `case1_preserves_stepInv'` goes FULLY PROVEN (conjunct-A dispatch + conjunct-B via the
  step-form both banked) and the wall falls.
