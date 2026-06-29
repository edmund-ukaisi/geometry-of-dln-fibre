# Statement card — RouteMBData222 (faithful BData M222: fidelity + map identity)

**Status:** sorry-free, builds green, axiom-clean `[propext, Classical.choice, Quot.sound]`.
**File:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMBData222.lean` (branch `genm-bdata222` off `genm-detfderiv`).
**Claim source:** `route-i-bridge-resolved.md` + `codex/bridge-answer.md` (the faithful `φ = B ∘ π`
decomposition for the concrete (2,2,2) node).

## Lean theorems (exact signatures) + English gloss

### `Agen0_Glr_eq` / `Agen1_Glr_eq` (the fidelity — the load-bearing content)
```lean
theorem Agen0_Glr_eq (rfin) (x) :
  Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct …) 0
    = !![aRead x, aRead x * nRead x;
         aRead x * bRead x, aRead x * bRead x * nRead x + x (structPivot M222 hN_M222)]
theorem Agen1_Glr_eq (rfin) (x) :
  Agen (x (structPivot M222 hN_M222)) M222 tach222 (Glr rfin x) (hleStruct …) 1
    = !![x (structPivot …) * rfin x ⟨0⟩ ⟨0⟩ - nRead x * w0Read x,
         x (structPivot …) * rfin x ⟨0⟩ ⟨1⟩ - nRead x * w1Read x;  w0Read x, w1Read x]
```
**Gloss:** the two chain layers of the FIXED-pivot/live-leaf decoder `genBlkFlatLiveR1 M222`
(`Glr rfin x`), reindexed, ARE the Codex-claimed explicit Schur-frame matrices. The `+ x structPivot`
at `Agen0[1,1]` is the fixed pivot's `u·E(0,0) = u·1` — the pivot COORDINATE (not an affine constant).
Readers `aRead = readK ⟨0⟩ 0 0` etc are the opaque-slot Schur coords. Verified against the actual
decoder (the abstract-vs-concrete pin that bred prior conflations — now machine-checked).

### `hmap_222` (BData obligation (1) — the genuine hard piece)
```lean
theorem hmap_222 :
  phiFlatLiveR1 M222 tach222 structAdm_tach222 hN_M222 1 hp1_222 hp2_222 rfin222
    = Bchart ∘ pivotBlowupOn active222 (structPivot M222 hN_M222)
```
**Gloss:** the faithful map identity `φ = B ∘ π`. `Bchart y = paramsEquivFlat M222 (Bparams y)` with
`Bparams` reading the pivot as the ORDINARY coord `y structPivot` (the `+u`), readers a/b/n/w0/w1 from
`y`, leaf `y lf0 / y lf1`; `rfin222 x = !![x lf0, x lf1]`; `active222 = {structPivot, lf0, lf1}`
(`card = minAdm M222 = 3`). The leaf slots `lf0, lf1` are chosen from the COMPLEMENT of the (opaque)
reader slots (R2: `free_card_ge_two`), so `lf ≠ structPivot`, `lf ∉ readerSet` hold by membership — the
opaque-`chartIdxEquiv` slot wall sidestepped. `Bchart` is NOT `phiGen 1 (genBlkFlatLiveR1)` (the
superseded wrong B — reads `E(0,0)` as constant 1).

## Hypotheses (carried, not assumed away)
- `structAdm_tach222 : StructAdm M222 tach222` (proved; `tach222 = ![2,1,0]`).
- `hp1_222 : Text(2) ≤ Text(1)`, `hp2_222 : Text(2) ≤ Wext(1)` (the R1 pivot drops, proved by `decide`).
- the leaf-pair choice uses `Classical.choice` (axiom-clean modulo it).

## Residual (NOT yet in Lean — see `bdata222-residual.md`)
The `BData` term needs `DB`/`hasDB`/`engine`/`hdet` — `Bchart`'s fderiv + `|det DB| = |aRead u|²` (the
`Bparams` Jacobian = a², the de-radialized analog of `T222Deriv_abs_det`). Mechanical-but-large
(~120-150 LoC). The headline `interiorDet_headline_of_BData` then gives `|det Dφ| = |u_p|²·|aRead u|²`.

**Pinned commit:** `genm-bdata222` HEAD (push to origin).
