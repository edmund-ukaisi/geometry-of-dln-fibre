# Statement card — fully-unconditional smeared `hSmeared` ∀L + the `deepLayer` name clash

**Status:** sorry-free, on `origin/genm-smearclose @edf1ac14` (based on `origin/genm-smearfin
@344c0f3b`). Closes the two residuals the `genm-smearbox` card flagged (§90, §c): the ∀L
structural-data derivation and the mechanical assembly, plus the co-import name clash. Two new modules
(both green), 8 files re-token-renamed. Aggregator wiring left for the controller (single-writer).

This makes the BOUNDARY-SMEARED branch of the ∀M achiever dispatch spine **fully unconditional ∀L** —
the spine's `hSmeared` slot is discharged with no open per-family hypothesis (only the branch's own
`2 ≤ L`, `BoundarySmeared M`, `NoInteriorBothDrop M`, plus the spine-level `1 ≤ minAdm M`).

## The claim

> **Claim.** For any width tuple `M : Fin (L+1) → ℕ` with `1 ≤ minAdm M`, and any `c' ≥ ½·minAdm M`,
> `ε > 0`: on the boundary-smeared stratum (`2 ≤ L`, `BoundarySmeared M`, `NoInteriorBothDrop M`) the
> achiever box integral diverges, `∫⁻_{cubeBox N ε} |routeMCore M|^{−c'} = ⊤`. All structural data the
> smeared box supplier needs is derived from those hypotheses; nothing is carried open.
>
> - **Lean:** `DLNFibre.DLN.RLCT.hSmeared_smearedClose`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedClose.lean` @ `edf1ac14`)
>   ; spine discharge `DLNFibre.DLN.RLCT.routeMCore_box_diverges_achiever_smearedClosed`
>   (`lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSpineWire.lean` @ `edf1ac14`).
> - **Gloss.** `hSmeared_smearedClose M hpos c' hc' ε hε : (2 ≤ L) → BoundarySmeared M →
>   NoInteriorBothDrop M → ∫⁻ x in cubeBox (routeMAmbient M) ε, ENNReal.ofReal (|routeMCore M x| ^
>   (-(c':ℝ))) = ⊤`. This is EXACTLY the widened `hSmeared` slot shape of
>   `routeMCore_box_diverges_achiever_spine`.
> - **Proved.** The ∀L structural-data derivation + the assembly into `hSmeared_boxGen`. Concretely,
>   inside the slot (`r := deepRank M`, `s := deepRows M − deepRank M`):
>   - `hrs : r + s = M (deepLayerS).castSucc` — since `M (deepLayerS).castSucc = M ⟨L−1⟩ = deepRows M`
>     and `deepRank ≤ deepRows` (from `BoundarySmeared.2`);
>   - `hr : 0 < deepRank M` and `hc : 0 < M (deepLayerS).succ` — from `1 ≤ minAdm M = deepRank M ·
>     M (Fin.last L)` (`minAdm_eq_deepRank_mul_last`, needs `NoInteriorBothDrop`);
>   - `hminadm : deepRank M · M (deepLayerS).succ = minAdm M` — same identity via `deepLayerS_succ_width`;
>   - waist `q ≤ L−1`, `hMq : M ⟨q⟩ = deepRank M`, `hwidth : ∀ t < L, deepRank M ≤ Wext M t`, and
>     `hr0 : deepRank ≤ M 0`, `hrL : deepRank ≤ M ⟨L−1⟩` — from `smeared_waist` (needs
>     `NoInteriorBothDrop`), reading `hwidth` at `t = 0, L−1`;
>   - `hN : routeMAmbient M = n + 1` — from `routeMAmbient M > 0` (`routeMAmbient_pos_of_front`: the
>     `s = 0` term `M ⟨0⟩·M ⟨1⟩ > 0`, both widths positive since `deepRank ≤ M ⟨0⟩, M ⟨1⟩` and
>     `deepRank > 0`, using `2 ≤ L`);
>   - pivot `p := hN ▸ pivotCoordG …`, `hp` by the ambient round-trip cast.
>   Then `hSmeared_boxGen` fires. **Fidelity (Item-3):** every structural fact genuinely follows from
>   `BoundarySmeared ∧ NoInteriorBothDrop ∧ 1 ≤ minAdm` — decorrelated-Codex-confirmed sound, no
>   sorry-laundering, no fabricated hypothesis.
> - **Assumed.** `1 ≤ minAdm M` (the spine's regime), `2 ≤ L`, `BoundarySmeared M`,
>   `NoInteriorBothDrop M` — all supplied by the dispatch spine at the smeared branch (the smeared
>   stratum genuinely IS `BoundarySmeared ∧ NoInteriorBothDrop`; the spine has `hNo`).
> - **Cited.** none in `hSmeared_smearedClose` itself (axiom footprint `[propext, Classical.choice,
>   Quot.sound]`, S2-free, no `sorryAx`). The spine discharge
>   `routeMCore_box_diverges_achiever_smearedClosed` picks up `monomial_rlct` only via the CLEAN
>   branch's monomial atom in the co-import (inherited, not from the smeared side).
> - **Deferred.** none for the smeared branch. (The spine still owes its INTERIOR branch + the clean
>   structural side-conditions `hMpos`/`hne` — carried as hypotheses in
>   `routeMCore_box_diverges_achiever_smearedClosed`, unchanged by this thread.)
> - **Status.** sorry-free.

## Flag 2 — the `deepLayer` name clash (resolved)

`RouteMSmearedDecodeGen`'s `deepLayer (hL) : Fin L` and `RouteMBoundaryCleanChart`'s
`deepLayer (M) (hL) : Fin L` were both `DLNFibre.DLN.RLCT.deepLayer` — co-importing the smeared DECODE
chain (which `hSmeared_boxGen` needs) with the clean chain (which the spine pulls) failed
`environment already contains DLNFibre.DLN.RLCT.deepLayer`. Renamed the smeared-decode one (newer,
more local) and its two width theorems: `deepLayer → deepLayerS`, `deepLayer_castSucc_width →
deepLayerS_castSucc_width`, `deepLayer_succ_width → deepLayerS_succ_width`, across the 8 smeared-Gen
files (`RouteMSmeared{DecodeGen,AssembleGen,SquareGen,BoxGen,BoxSupply,UniformLam,CancelGen,DetData}`).
Pure token rename (219 ins / 219 del, symmetric); no claim change. `RouteMSmearedSpineWire` co-imports
both chains and compiles clean — the clash is gone.

## Verification banked

- `RouteMSmearedBoxSupply` (renamed smeared Gen chain): `Build completed successfully (8346 jobs)`.
- `RouteMSmearedSpineWire` (co-import of both chains + spine discharge): `Build completed successfully
  (8356 jobs)` — the co-import test PASSES post-rename, and `hSmeared_smearedClose` type-matches the
  spine's widened `hSmeared` slot.
- `#print axioms` (forced): `hSmeared_smearedClose = [propext, Classical.choice, Quot.sound]`;
  `routeMCore_box_diverges_achiever_smearedClosed = [propext, Classical.choice, Quot.sound,
  monomial_rlct]` (monomial_rlct via the clean co-import); `routeMAmbient_pos_of_front = clean-three`.
- `scripts/sorries`: zero in the two new files (`RouteMSmearedClose`, `RouteMSmearedSpineWire`). The
  22 pre-existing tree sorries live in unrelated open branches (Schur/interior/skeleton); the
  `#print axioms` confirms none leak into `hSmeared_smearedClose` (no `sorryAx`).

## Aggregator wiring (for the controller)

`DLNFibre.lean` does not yet import `RouteMSmearedClose` / `RouteMSmearedSpineWire` (single-writer).
To wire the fully-unconditional smeared branch into the achiever headline, import
`DLNFibre.DLN.RLCT.Validate.RouteMSmearedSpineWire` at the end of the aggregator (after the interior
Gen wire). It transitively pulls the renamed smeared Gen chain and re-uses the already-imported clean
chain — no reorder of existing imports. The smeared `hSmeared` slot of
`routeMCore_box_diverges_achiever_spine` is then dischargeable ∀L by `hSmeared_smearedClose`.
