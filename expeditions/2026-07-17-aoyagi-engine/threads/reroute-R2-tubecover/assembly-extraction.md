# R2 assembly extraction — the born-native σ_p family + the (3,3,4) headline wiring

**Purpose (continuity artifact, not a report).** The banked hand-off for a fresh **(A)** seat
(born-native σ_p fan + `hcover`) and **(B)** seat (the ×9 `hentry` entry-equalities). Everything here
is self-contained so no seat depends on the transcript. Author: assembly thread (r2assembly branch),
2026-07-26.

## 0. Where the value path already stands (LANDED, sorry-free, clean-three)

The (3,3,4) V-lower headline `4 ≤ rlctAt (sumSqFam (coreGen dvec eWrap)) 0` is reduced to a clean
contract by two banked bricks (`lean/DLNFibre/DLN/Aoyagi/`):

- `Corank2Headline334.rlctAt_coreGen334_ge_four_of_family` — headline ⟸ the wire's per-chart family
  (g/dom/nbhd/excep/bexp/k₀/jac/unit/cst/U + the `h…` fields) + `divisorMin = 8`. Discharges
  `hFmeas` + `hbdd` (V-upper #110, `bddAbove_localAdmissible_coreGen334`) + the STEP 4→5 joint + the
  ½·8=4 arithmetic.
- `Corank2HeadlineValue334.rlctAt_coreGen334_ge_four_of_survivor_entries` — the **tighter** contract
  (no measure-theoretic sandwich): headline ⟸ the exact per-leaf **entry-equality**
  `hentry : ∀ c w, coreGen dvec eWrap (k0 c) (g c w) = ∏_d (w d)^(ek₀ c d)` + area-data + `hcover`
  + `divisorMin = 8`. `hsandwich` is discharged internally via `Finset.single_le_sum`
  (loss ≥ monomial² globally; cst = 1/Mn, Mn = 12; `hchain = le_refl` on the constant survivor
  family). **This is the seat's target contract.**

So the seat must construct: the born-native family `g c`, `hentry`, `hcover`, per-leaf `jac`, and
`divisorMin = 8`. NOTHING else (the value→headline path is closed).

## 1. Coordinate layout (Fin 21) — from `Corank2CoreGenWrap`

- `eWrap` is the transpose flatten: `A0 = C₁ᵀ` (3×3), `A1 = C₂ᵀ` (4×3), `mult = A1·A0 = Pmatᵀ`.
- `A0` slot map (which `u`-coord is which `A0[i,j]`):
  `{(0,0):20, (0,1):2, (0,2):3, (1,0):0, (1,1):4, (1,2):6, (2,0):1, (2,1):5, (2,2):7}`.
- `A1[a,b] = u(8 + 4·b + a)`, so coords `8..19` are the `C₂` block.
- The exceptional / survivor monomial for the CANONICAL dominant is `c₁₁·E = u₀·u₂₀`
  (`bexpWrap = [1 at 0, 1 at 20]`); `jac(E=0) = 7`, `jac(c₁₁=20) = 8` ⟹ chartMin = min(8,9) = 8.

## 2. The 9 explicit W3-CLEAN native σ_p shears (the buildable core)

Each dominant `(i,j)` (the surviving `A0[i,j]` entry) has an **explicit native block-shear**
`σ_(i,j) = blockShear φ_(i,j)` given DIRECTLY below as coordinate displacements — this is the
**W3-clean** form (NOT the `σ⁻¹∘shearH∘σ` conjugate; the conjugate is the pnp DESCRIPTION only). Each
`φ` is a quadratic block-shear: every corrected coord is a sum of ≤ 2 products, so `‖φ x‖ ≤ 2‖x‖²`
⟹ `blockShear_covers_scaled` at `C = 2` (box inflation `r ↦ r + 2r²`) applies per pivot. Each is a
well-formed block-shear (`cleared coords ∩ read coords = ∅`, listed per dominant). `dom(0,0)` is
exactly the landed `Corank2GWrapDecomp.shearH` / `Corank2ChartJac.shearPhiH`.

```
dom(0,0)  outer-pivot=slot20   cleared=[4,5,6,7,8,9,10,11]   reads=[0,1,2,3,12,13,14,15,16,17,18,19]
    phi[4]  = u0*u2
    phi[5]  = u1*u2
    phi[6]  = u0*u3
    phi[7]  = u1*u3
    phi[8]  = -u0*u12 - u1*u16
    phi[9]  = -u0*u13 - u1*u17
    phi[10] = -u0*u14 - u1*u18
    phi[11] = -u0*u15 - u1*u19

dom(0,1)  outer-pivot=slot2    cleared=[0,1,6,7,8,9,10,11]   reads=[3,4,5,12,13,14,15,16,17,18,19,20]
    phi[0]  = u20*u4
    phi[1]  = u20*u5
    phi[6]  = u3*u4
    phi[7]  = u3*u5
    phi[8]  = -u12*u4 - u16*u5
    phi[9]  = -u13*u4 - u17*u5
    phi[10] = -u14*u4 - u18*u5
    phi[11] = -u15*u4 - u19*u5

dom(0,2)  outer-pivot=slot3    cleared=[0,1,4,5,8,9,10,11]   reads=[2,6,7,12,13,14,15,16,17,18,19,20]
    phi[0]  = u20*u6
    phi[1]  = u20*u7
    phi[4]  = u2*u6
    phi[5]  = u2*u7
    phi[8]  = -u12*u6 - u16*u7
    phi[9]  = -u13*u6 - u17*u7
    phi[10] = -u14*u6 - u18*u7
    phi[11] = -u15*u6 - u19*u7

dom(1,0)  outer-pivot=slot0    cleared=[2,3,5,7,12,13,14,15]  reads=[1,4,6,8,9,10,11,16,17,18,19,20]
    phi[2]  = u20*u4
    phi[3]  = u20*u6
    phi[5]  = u1*u4
    phi[7]  = u1*u6
    phi[12] = -u1*u16 - u20*u8
    phi[13] = -u1*u17 - u20*u9
    phi[14] = -u1*u18 - u10*u20
    phi[15] = -u1*u19 - u11*u20

dom(1,1)  outer-pivot=slot4    cleared=[1,3,7,12,13,14,15,20]  reads=[0,2,5,6,8,9,10,11,16,17,18,19]
    phi[1]  = u0*u5
    phi[3]  = u2*u6
    phi[7]  = u5*u6
    phi[12] = -u16*u5 - u2*u8
    phi[13] = -u17*u5 - u2*u9
    phi[14] = -u10*u2 - u18*u5
    phi[15] = -u11*u2 - u19*u5
    phi[20] = u0*u2

dom(1,2)  outer-pivot=slot6    cleared=[1,2,5,12,13,14,15,20]  reads=[0,3,4,7,8,9,10,11,16,17,18,19]
    phi[1]  = u0*u7
    phi[2]  = u3*u4
    phi[5]  = u4*u7
    phi[12] = -u16*u7 - u3*u8
    phi[13] = -u17*u7 - u3*u9
    phi[14] = -u10*u3 - u18*u7
    phi[15] = -u11*u3 - u19*u7
    phi[20] = u0*u3

dom(2,0)  outer-pivot=slot1    cleared=[2,3,4,6,16,17,18,19]  reads=[0,5,7,8,9,10,11,12,13,14,15,20]
    phi[2]  = u20*u5
    phi[3]  = u20*u7
    phi[4]  = u0*u5
    phi[6]  = u0*u7
    phi[16] = -u0*u12 - u20*u8
    phi[17] = -u0*u13 - u20*u9
    phi[18] = -u0*u14 - u10*u20
    phi[19] = -u0*u15 - u11*u20

dom(2,1)  outer-pivot=slot5    cleared=[0,3,6,16,17,18,19,20]  reads=[1,2,4,7,8,9,10,11,12,13,14,15]
    phi[0]  = u1*u4
    phi[3]  = u2*u7
    phi[6]  = u4*u7
    phi[16] = -u12*u4 - u2*u8
    phi[17] = -u13*u4 - u2*u9
    phi[18] = -u10*u2 - u14*u4
    phi[19] = -u11*u2 - u15*u4
    phi[20] = u1*u2

dom(2,2)  outer-pivot=slot7    cleared=[0,2,4,16,17,18,19,20]  reads=[1,3,5,6,8,9,10,11,12,13,14,15]
    phi[0]  = u1*u6
    phi[2]  = u3*u5
    phi[4]  = u5*u6
    phi[16] = -u12*u6 - u3*u8
    phi[17] = -u13*u6 - u3*u9
    phi[18] = -u10*u3 - u14*u6
    phi[19] = -u11*u3 - u15*u6
    phi[20] = u1*u3
```

Reproduce/verify with the pnp one-liner over `seam_all9_dominants_334.py`'s helpers
(`shearH_disp` = the canonical displacement; `make_sigma(i,j) = colswap(j)∘rowswap(i)`;
`φ_(i,j)[k] = (shearH_disp(u∘σ))[σ(k)]`). The extraction script is banked in this thread dir.

## 3. STRUCTURAL QUESTION — pin the fan shape before the def (elder to confirm)

The pnp verifies via the WHOLE-`gWrap` conjugate `σ⁻¹∘gWrap∘σ` (3 blow-up nodes bbA1/bbA0/sigmaPiv +
shear). The elder's fact-#2 shorthand `g_c = blockBlowupMap S p ∘ σ_p` reads as one node. Candidate
explicit-native shapes:
- **(a)** 1-node outer fan (`blockBlowupMap(perm center)(slot i,j) ∘ σ_(i,j)`, 9 leaves) — but one
  node cannot produce `jac(E)=7 ∧ jac(pivot)=8` (⟹ divisorMin=8); RULED WEAK.
- **(b)** 3-step `fanOfSteps` with per-pivot NATIVE shears replacing the fixed `(shearH∘permP, id,
  id)` of the landed `gWrapFan` — leaves = pivot-paths. **Controller's lean; matches the fact-#2
  engine + gives jac 7&8.**
- **(c)** whole-`gWrap`-conjugate unfolded per dominant (3 permuted blow-ups + permuted shear), 9
  leaves — risks W3-drift, may under-cover.

The σ_(i,j) shears in §2 are the STEP-1 (outer sigmaPiv-node) native shears under reading (b)/(c).
**Do not commit the def until the elder pins the shape** (this determines the blow-up centers/pivots
per step and the W3 grep target).

## 4. `hcover` route (mapped, LANDED atoms — no enumeration bridge)

The wire's `hcover : volume (U \ ⋃ c, g c '' dom c) = 0` (flat `Fin` family, up-to-null) is
discharged DIRECTLY by `SurvivorFanCover.volume_box_diff_charts_eq_zero` — NO tree/`leafImages`
enumeration (the crux-B/#143 bridge is unlanded and OFF the critical path):
- `gen := the coreGen entries`; `commonZero gen = {X=0}` (the deepest locus).
- `hchart : ∀ a, survivorRegion R gen a ∩ box ⊆ chart a '' dom a` — the block-blowup argmax, the
  `NodeCover334.keptSubsetBornFan_cover_334` / `CoverFold.bornSiblings_union_covers` shape.
- `hnull : volume (commonZero gen) = 0` — cheap, one nonzero generator via
  `SurvivorFanCover.volume_commonZero_eq_zero_of_single`.
- `iUnion_survivorRegion` (R ≥ 1) ⟹ the hole is null EVERYWHERE ⟹ no radius shrink; both cover and
  value are global under fact #2 (radius tension fully dissolved). Take `U = ball 0 R ⊆ box`,
  `R ≥ 1`, `U ∈ 𝓝 0`.

## 5. `hentry` (the (B) seat) + `jac`/`divisorMin` (the (C) seat)

- **`hentry`** (×9, the pnp F5–F9 core): `coreGen (k0 c) (g c w) = ∏_d (w d)^(ek₀_c d)` exactly. The
  canonical anchor is `Corank2CoreGenWrap.coreGen_gWrap_flat` (coreGen∘gWrap = u₂₀·flat(Pmat)(τk)∘
  gFaithful) + the `hideal_faithful` block-elim; the recoord σ_(i,j) cancels the cross-term so
  `M[0,0] = E` EXACTLY (stronger than the landed IDEAL equality — needs the native σ, which the
  fixed shearH does NOT give). Detail-at-scale (patient block-matrix algebra ×9), pnp-certified
  (`born_alpha_cert_334.py`, `seam_all9_dominants_334.py`, exact sympy + Codex).
- **`jac`/`divisorMin`** (C): per-leaf `jac` from the permuted blow-up structure; canonical
  `jac(E=0)=7`, `jac(c₁₁=20)=8` (`Corank2ChartJac.jacWrap`); `divisorMin = ⨅_c ⨅_binding (jac+1) = 8`
  (all-leaves min; `seam_all9` confirms every dominant gives divisorMin=8). `hunit_mult` = binding
  exps are 1 (squarefree).

## 6. Pointers

- **pnp certs** (F5–F9; banked in this thread's `pnp/` dir, currently untracked — commit if a seat
  needs them): `born_alpha_cert_334.py` (the parametrized F5 recoord + block-elim), 
  `seam_all9_dominants_334.py` (all 9 dominants → rlct 4 / single survivor / divisorMin 8),
  `leaftype_census_334.py`, `deep_chart_ablation.py` (T8/T9), `loss_gcd_toggle.py` (T6),
  `jac_divisormin_334.py`, `permconj_jac_334.py`.
- **Landed Lean infra**: `SurvivorFanCover` (up-to-null cover + `sumSq_residual`), `ImageTreeCover`
  (Fin-indexed tree + fold), `Corank2FanCover334.gWrapFan_leafImages_mem_nhds` (L2 general-R, 𝓝 0),
  `GeneralGeoAtlas.blockShear_covers_scaled`/`covers_fanOfSteps`/`fanOfSteps`,
  `NodeCover334.keptSubsetBornFan_cover_334`, `StepConstructor` (`bornSiblings`/`PivotStep`/
  `CleanClearing.jacDet_shear`), `Corank2GWrapDecomp.shearH` (= dom(0,0)),
  `Corank2ChartJac.jacWrap`/`shearPhiH`.
- **Value path (target contract)**: `Corank2HeadlineValue334.rlctAt_coreGen334_ge_four_of_survivor_entries`.

## 7. W3 grep-clean gate (elder, HARD — verify at the def's landing)

The σ_p Lean def must be grep-clean of `Corank2Transport334` / `resolution334_of_fanCover` /
`transportChart` / K-orbit / `conjResolution` in the CONSTRUCTION (the `σ⁻¹∘shearH∘σ` conjugate =
docstring/comment ONLY). The §2 displacements ARE the explicit native form — transcribe them as
`blockShear φ` directly.
