# deepRank=0 interior handler (#250) — build state + item-5 entry point

## Verdict (banked)
BOUNDED, kill-condition PASSES at EXACTLY ½·minAdm = ½·M0·M1 (Codex xhigh + rBlock·cBlock budget,
`codex/deeprank0-{prompt,answer}.md`). The deepRank=0 stratum (e.g. M=(1,1,2): unique tStar=![0,0])
is genuinely InteriorDrop, uncovered by the LIVE-leaf atom (its leafPivot needs 0<deepRank). Chart =
radial blow-up on the FRONT E-block (activeEImg.card = M0·M1 = minAdm at deepRank=0; leaf vacuous).

## DONE (sorry-free, green) — RouteMInteriorDeepRank0.lean @2e6352bd
1. `eBlockPivot` + `eBlockPivot_mem_activeM` (reuses activeSlotE_mem_activeM).
2-3. `eDeepRank0Phi := phiFlatLiveAt … eBlockPivot` + `eDeepRank0Phi_rate` (rate = (x p₀)²·V, reuses
   the PIVOT-GENERIC `phiFlatLiveAt_rate` verbatim — the rate half of routeMCore_interiorLivePhi
   transfers fully; leaf K-block untouched).
4. `eDeepRank0_leafH` (single-axis: minAdm−1 at pivot, 0 else) + `_pivot` (pure radial; all K-blocks
   vanish at deepRank=0, so NO LDU/Schur exponents).

## ITEM 5 — THE CRUX (det), entry point + the real shape
Goal: `|det D(eDeepRank0Phi) u| = ∏_j |u_j|^{eDeepRank0_leafH j} = |u eBlockPivot|^{minAdm−1}`.
Route: `radialComp_abs_det_at` (GENERIC in pivot, RouteMRadialComp:74) gives, given an hmap
`eDeepRank0Phi = B ∘ pivotBlowupOn activeM eBlockPivot` + `hasDB`:
   `|det Dφ| = |u eBlockPivot|^{minAdm−1} · |det DB|`.
Then need `|det DB| = 1` (pure radial, no boundary shear at deepRank=0) ⟹ single-axis monomial.

THE WALL (flagged, NOT thrashed): the existing hmap (`hmap_leaf`) → `chartParamsGen_match` →
`{Cgen1,Cgen2,Nblk,Wblk}_match` → `read{K,X,N,E,W}_pbo` are LEAF-BLOCK-STRUCTURED, not merely
leafPivot-indexed: `read*_pbo` are typed with leaf-block index types `Fin (Text (0+2)) = Fin(deepRank)`
(= Fin 0 at deepRank=0), `rfinFixedPivot` scales the LEAF block. The deepRank=0 chart INVERTS roles
(radial in FRONT E-block, leaf empty/spectator), so the hmap is NOT a leafPivot→p₀ substitution — it
needs a re-derived chart-parameter match for the E-radial decomposition:
   `chartParamsGen (x eBlockPivot) … (genBlkFlatLive … x) = (E-radial B-decoder) ∘ pbo_E`,
i.e. read*_pbo_E analogs (radial-in-E, leaf-spectator) + Cgen*_match_E. ~250-350 lines, real proof
work — the from-scratch chart-parameter-match (the ‖E·G‖² factorization surfacing in chart-param form).

Possible simplification to probe FIRST (could shrink item 5 a lot): at deepRank=0 the leaf block is
0-dim and genBlkFlatLive may reduce so that the residual map B (after the radial pivot) is LINEAR /
unimodular — if `|det DB| = 1` can be shown WITHOUT the full chartParamsGen_match (e.g. via a direct
phiGen-fderiv = pivotBlowup ∘ (measure-preserving reshape) argument, the RouteM4422 phi4422_abs_det
template: det = pb_abs_det · Q_abs_det with Q unimodular), item 5 collapses to the 4422-style
"radial · unimodular-reshape" det, avoiding the leaf-match machinery entirely. CHECK phiGen's fderiv
structure / whether chartParamsGen at deepRank=0 is affine-in-residual.

## TAIL (items 6-9, after item 5)
6. U a.e.-pos (VvalGen_ae_pos / all-ones template) + bounded-on-box + measurable.
7. injOn (mirror interiorLive_injOn with eBlockPivot in the inj domain).
8. cov + NodeAchieverChart₀ bundle + `routeMCore_box_diverges_eDeepRank0`.
9. wire into achiever_L2 interior branch (combine 0<deepRank atom + this → hInterior ∀ InteriorDrop).

## Bedrock reqs (lead, standing)
Pure-monomial pivotBlowupOn Jacobian throughout (NO poly-det fold — Item-102 trap); U-pos PROVED not
assumed; target axioms = [propext, Classical.choice, Quot.sound, monomial_rlct].

## Item-5 det: the conservative-generalization shape (lead-approved shared edit, RouteMLeafBData)

Approved route: generalize the radial pivot leafPivot → generic p₀ ∈ activeM in RouteMLeafBData, so
both legs share it. BEDROCK GUARD (lead): must be CONSERVATIVE — existing leaf leg recovers every lemma
by p₀ := leafPivot with the same proof; after the edit, GREEN-GATE THE WHOLE LIB + #print axioms on
routeMCore_box_diverges_interiorLive UNCHANGED ([propext,Classical.choice,Quot.sound,monomial_rlct]);
else REVERT to isolated re-derive.

THE INTRICACY (more than a pivot-rename — flagged): the deepRank=0 chart INVERTS block roles.
- Leaf chart: radial lives in the LEAF block; readE SCALES by x(leafPivot) (readE_pbo); K/X/N/W are
  spectators (read*_pbo via pbo_fixes_boundary0 "slot ≠ pivot"); rfinFixedPivot scales the leaf block;
  Cgen2_match handles the leaf radial.
- deepRank=0 chart: radial lives in the FRONT E-block; the PIVOT is one E-slot (→1 under pbo), OTHER
  E-slots scale; leaf block is 0-dim (vacuous); K/X/N/W still spectators.
So readE_pbo must split: pivot E-slot → 1, non-pivot E-slots → scale by x p₀. The pbo_fixes_boundary0
spectator lemmas (K/X/N/W) generalize cleanly (pivot-generic "slot ≠ p₀"). The genuinely new pieces:
(a) readE_pbo_generic: at a generic E-pivot p₀, readE(pbo x) at slot ≠ p₀ scales by x p₀, at p₀ = x p₀
    (pivot fixed) — this is the radial kernel for the E-block.
(b) Cgen1_match_generic: the interior Cgen match with the radial-u in the E-block (schurFrameProd_u_to_E
    already does u→E; the question is whether it composes with a generic E-pivot).
(c) Cgen2_match at deepRank=0: the leaf Cgen is VACUOUS (leaf 0-dim) — should be trivial/refl.
(d) chartParamsGen_match_generic + hmap_generic threading (a)-(c).
Then radialComp_abs_det_at (generic) + |det DB| = 1 (pure radial, no leaf shear) → the single-axis det.

ESTIMATE: ~250-350 lines, intricate (block-role inversion). Conservative-recovery of the leaf leg is
the load-bearing guard — the generalization must keep leafPivot-instantiation proof-identical. Needs a
fresh focused session to do conservatively + whole-lib green-gate. Resume here.
