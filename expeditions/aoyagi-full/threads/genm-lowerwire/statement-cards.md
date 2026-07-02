# Statement cards — `genm-lowerwire` (general-L interior `hInterior` wiring)

Thread: wire the landed general-`L` interior box-divergence atom into the achiever-dispatch spine's
`hInterior` obligation. Branch `genm-lowerwire` off canonical `expedition/aoyagi-full` @ `fe204864`.

Module: `lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveGenWire.lean` (77 LoC, 0 sorries).

---

## Card 1 — `routeMCore_box_diverges_interiorLiveGen_of_deepRank_pos`

**Kind:** Proved (sorry-free), general `L`.

**Statement.** For `M : Fin (L+1) → ℕ` with `2 ≤ L`, `InteriorDrop M`, `0 < deepRank M`, and
`1 ≤ minAdm M`, every `c' ≥ ½·minAdm M` and `ε > 0`:
`∫⁻_{cubeBox (routeMAmbient M) ε} |routeMCore M x|^{−c'} = ⊤` (`= BoxDiverges M c' ε`).

**Route.** Direct application of the landed atom `routeMCore_box_diverges_interiorLiveGen`
(`RouteMInteriorLiveGenAtom.lean:124`, ∀L). The six atom inputs discharged:
`ha := structAdm_tach M (0<L)` (unconditional); `hL` from `2 ≤ L`; `h0c := hInt.1` (the FIRST
CONJUNCT of `InteriorDrop`, which IS `0 < Wext M L`); `h0r := hdr` (`0 < deepRank M`, defeq
`0 < Text M (tach M) L`); `hpos`, `hc'`, `hε` passed through.

**Fidelity (load-bearing).** `h0r : 0 < deepRank M` is carried as an EXPLICIT hypothesis, NOT derived
from `InteriorDrop`. `InteriorDrop M` does not imply `0 < deepRank M`: the L=2 characterization
`interiorDrop_L2_iff` is `0 < M 2 ∧ deepRank M < M 0 ∧ deepRank M < M 1` (upper bounds only), and
`(2,2,1)` (`tStar = ![0,0]`) has `deepRank = 0` yet `InteriorDrop`. Decorrelated-Codex (xhigh) confirmed
this and the scope. The `deepRank = 0` interior sub-stratum is handled at L=2 by a SEPARATE atom
(`routeMCore_box_diverges_eDeepRank0`, `Fin (2+1)`-pinned); there is NO general-`L` `deepRank = 0` atom,
so this lemma covers exactly the `0 < deepRank` sub-stratum.

**Axioms (forced `#print`, fresh olean):** `[propext, Classical.choice, Quot.sound, monomial_rlct]`
(clean-three + the single S2 cited axiom), no `sorryAx`. Matches the atom.

---

## Card 2 — `interiorLiveGen_hInterior_of_deepRank_pos`

**Kind:** Proved (sorry-free), general `L`. The `∀ _ : 2 ≤ L`-shaped consumer form.

**Statement.** For `M : Fin (L+1) → ℕ` with `0 < deepRank M`, `1 ≤ minAdm M`, `c' ≥ ½·minAdm M`,
`ε > 0`: `∀ _ : 2 ≤ L, InteriorDrop M → BoxDiverges M c' ε`.

**Route.** `fun hL2 hInt => Card1 …`. This is the EXACT shape the spine's `hInterior` slot
(`routeMCore_box_diverges_achiever_spine`, `RouteMAchieverDispatch.lean:81`) consumes, restricted to the
`0 < deepRank M` sub-stratum.

**Axioms:** same footprint as Card 1.

---

## Controller wiring TODO (single-writer files — not edited by this thread)

1. `lean/DLNFibre.lean` (aggregator): add `import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLiveGenWire`
   at the end, before `AxCheck`.
2. `lean/DLNFibre/DLN/RLCT/AxCheck.lean`: add `#print axioms interiorLiveGen_hInterior_of_deepRank_pos`
   (and/or `routeMCore_box_diverges_interiorLiveGen_of_deepRank_pos`) to the load-bearing gate; expected
   `[propext, Classical.choice, Quot.sound, monomial_rlct]`.

## Remaining general-`L` interior gap (not this thread's scope)

The general-`L` `deepRank = 0` interior sub-stratum has NO atom (only `Fin (2+1)`). A general-`L` E-block
radial atom (the lift of `routeMCore_box_diverges_eDeepRank0`) is required before the FULL general-`L`
`hInterior` (∀ `InteriorDrop`) is dischargeable.
