# Statement card — the general-`L` R1-LOWER achiever `hdiv`, ALL branches discharged ∀L

**Status:** sorry-free, on `origin/genm-smearint` (branched off canonical `origin/expedition/aoyagi-full
@eb52d7a9`; smeared chain additively cherry-picked from `origin/genm-smearclose @3eb6ed8c`). Green-gate
PASS: `lake build DLNFibre` = `Build completed successfully (8708 jobs)`, exit 0 — the FIRST full
co-existence of the interior chain + the smeared chain in the aggregator, no clash (the `deepLayer →
deepLayerS` rename handles the one known collision; no others surfaced). One new module
(`RouteMAchieverFull.lean`, capstone) + the additive integration of the 14 smeared-chain / Core-Matrix
`.lean` files + the widened `RouteMAchieverDispatch` spine + aggregator/`AxCheck` wiring.

This assembles the general-`L` achiever box-divergence with **all three branches discharged** — clean
(in-spine), interior (`interiorLiveGen_hInterior`, ∀L), smeared (`hSmeared_smearedClose`, ∀L) — leaving
only the achiever stratum's `NoInteriorBothDrop M` and the clean structural side-conditions as
hypotheses on `M`.

## The claim

> **Claim.** For any width tuple `M : Fin (L+1) → ℕ` with `1 ≤ minAdm M`, all widths positive
> (`∀ s, 0 < M s`), the deepest block nonempty at every positive `L`
> (`∀ hL : 0 < L, (deepestCoords M hL).Nonempty`), and no interior both-drop (`NoInteriorBothDrop M`):
> for any `c' ≥ ½·minAdm M` and `ε > 0`, the achiever box integral diverges,
> `∫⁻_{cubeBox (routeMAmbient M) ε} |routeMCore M|^{−c'} = ⊤`, for EVERY `L`.
>
> - **Lean:** `DLNFibre.DLN.RLCT.routeMCore_box_diverges_achiever_full`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverFull.lean`).
> - **Gloss.** `routeMCore_box_diverges_achiever_full (M) (hpos : 1 ≤ minAdm M) (hMpos : ∀ s, 0 < M s)
>   (hne : ∀ hL : 0 < L, (deepestCoords M hL).Nonempty) (hNo : NoInteriorBothDrop M) (c') (hc' :
>   (minAdm M : ℝ≥0∞) / 2 ≤ (c' : ℝ≥0∞)) (ε) (hε : 0 < ε) : BoxDiverges M c' ε`, where
>   `BoxDiverges M c' ε := ∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^
>   (-(c':ℝ))) = ⊤`.
> - **Proved.** The one-line assembly: feed the 4-way dispatch spine
>   `routeMCore_box_diverges_achiever_spine` (RouteMAchieverDispatch) its two open slot-dischargers.
>   - INTERIOR slot ← `interiorLiveGen_hInterior M hpos c' hc' ε hε` (RouteMInteriorLiveGenHInterior,
>     canonical): `∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε`, the two `deepRank` sub-strata
>     combined (`Nat.eq_zero_or_pos`), unconditional on `InteriorDrop`.
>   - SMEARED slot ← `hSmeared_smearedClose M hpos c' hc' ε hε` (RouteMSmearedClose): `(2 ≤ L) →
>     BoundarySmeared M → NoInteriorBothDrop M → BoxDiverges M c' ε`, structural data derived ∀L.
>   - CLEAN branch + `L = 0` vacuity + `L = 1` always-clean: handled inside the spine, threading
>     `hNo`/`hne`/`hMpos`.
>   The two slot-dischargers' `(hpos)(c')(hc')(ε)(hε)` contexts and conclusion shapes match the spine
>   slots exactly (`BoxDiverges` unfolds definitionally to the `∫⁻ … = ⊤` both closers produce), so the
>   assembly is a direct spine application — no glue lemmas.
> - **Assumed (hypotheses on `M`).** `1 ≤ minAdm M` (the achiever regime); `hMpos`, `hne` (the clean
>   branch's structural side-conditions `routeMCore_box_diverges_clean` consumes — all widths positive,
>   deepest block nonempty); `hNo : NoInteriorBothDrop M` (the achiever value leg genuinely lives on
>   this stratum — the interior Aoyagi blocks vanish; the smeared slot also needs it). These are
>   decidable structural facts the caller / the R1-resolution assembly establishes per `M`.
> - **Cited.** `monomial_rlct` (the single permitted S2 axiom, the bare weighted-monomial-integral
>   fact), entering ONLY through the interior slot (`interiorLiveGen_hInterior`'s box-divergence atoms).
>   The smeared slot is S2-free (clean-three: the smeared box divergence is single-axis after the front
>   shear, not via `monomial_rlct`); the spine adds no axiom of its own.
> - **Deferred.** `hNo` is not yet proven from a coarser hypothesis: the general R1-resolution assembly
>   must PROVIDE `NoInteriorBothDrop M` (a hypothesis on `M`, or the open general `¬InteriorDrop →
>   NoInteriorBothDrop` bridge; the `L = 2` leg threads it). This is the R1-resolution runway, not a hole
>   in `hdiv` — the achiever box-divergence itself is complete ∀L given `hNo`.
> - **Status.** sorry-free.

## Axiom footprints (forced `#print axioms`, from the green-gate build)

- `hSmeared_smearedClose` = `[propext, Classical.choice, Quot.sound]` — CLEAN-THREE, S2-free, no `sorryAx`.
- `interiorLiveGen_hInterior` = `[propext, Classical.choice, Quot.sound, monomial_rlct]` — the interior
  slot carries the S2 citation.
- `routeMCore_box_diverges_achiever_full` = `[propext, Classical.choice, Quot.sound, monomial_rlct]` —
  the capstone inherits exactly `monomial_rlct` (via the interior slot), NO `sorryAx`. This is the
  expected footprint from the brief.

## Integration topology (banked)

- Additive cherry-pick (NOT a git merge): branched off canonical `@eb52d7a9`; brought ONLY the 14
  smeared-chain / Core-Matrix `.lean` files (`RouteMSmeared*` × 12 + `Core/Matrix/{CarrierBlock,
  GramFullRank}`) + the widened spine `RouteMAchieverDispatch.lean` from `genm-smearclose @3eb6ed8c`
  (`git checkout <branch> -- <files>`; grep==git verified: all brought files byte-match the smearclose
  blobs). Kept canonical's `synthesis.md` / `discuss-at-close.md` / `DLNFibre.lean` / `AxCheck.lean`
  (the latter two edited additively). All transitive smeared deps already exist on canonical, byte-
  identical on both branches.
- `DLNFibre.lean`: added `import RouteMSmearedSpineWire` + `import RouteMAchieverFull` at the end (after
  the interior Gen wire, before `AxCheck`); no reorder.
- `AxCheck.lean`: added `import RouteMSmearedClose` + `import RouteMAchieverFull` + three `#print axioms`
  (`hSmeared_smearedClose`, `routeMCore_box_diverges_achiever_full`; `interiorLiveGen_hInterior` was
  already printed).
- `scripts/sorries`: zero over the brought/new files (`RouteMSmeared*`, `RouteMAchieverFull`,
  `RouteMAchieverDispatch`, `CarrierBlock`, `GramFullRank`). The 22 pre-existing tree sorries + the 1
  axiom (`monomial_rlct`) live in unrelated open branches (Schur/D1/skeleton), unchanged.
