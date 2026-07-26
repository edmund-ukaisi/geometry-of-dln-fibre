# Over-vanishing per-type DATA — 16 canonical leaves (p1=20)  [for the pattern seats]

Sympy-derived DIRECTLY from the Lean `gFlat` (faithful `blockBlowupMap`/`nativeSel20`/`nativePerm20`/`blockShear`
composite); every leaf's 8 reg-seq entry identities VERIFIED end-to-end vs the numeric `gFlat` (max err 1.3e-15,
300 pts/leaf). Recipe + proof template: `DLNFibre/DLN/Aoyagi/Corank2OverVanishCanon334.lean` @ `8113eb62c`.

## How to consume (per leaf), mirroring the (20,1,1) template

For leaf `(20,p2,p3)`, build a module (or a section) with:
- `idxCanon := ⟨⟨20,by decide⟩, ⟨p2,by decide⟩, ⟨p3,by decide⟩⟩`
- `gCanon := blockBlowupMap S1 20 (nativeChart1 20 (blockBlowupMap (sigmaC1Fs 20) p2 (blockBlowupMap (sigmaC2Fs 20) p3 ·)))`;
  `gFlat_idxCanon : gFlat idxCanon = gCanon := by funext w; rfl`
- `phiCanon u i := if i = <b0> then <φ_b0> else if i = <b1> then … else 0`  (block = the 4 straightened coords)
- `vmExpCanon d := if d = <a> ∨ d = <b> (∨ d = <c>) then 1 else 0`  (the nonzero-vm coords; PROVE `prod_vmExpCanon`)
- `pairsCanon`, `zcPair`, `Scanon = pairsCanon.image finProdFinEquiv`, `zcCanon k := zcPair (finProdFinEquiv.symm k)`,
  `Zcanon` (= the 8 straightened coords)
- 8 entry lemmas `entry_ij` at `finProdFinEquiv ((i:Fin 4),(j:Fin 3))`, EACH via the template recipe:
  `rw [coreGen_eWrap_entry]; simp only [Equiv.symm_apply_apply, Fin.isValue]; rw [Matrix.mul_apply, Fin.sum_univ_three];`
  `simp (config:={decide:=true}) only [gCanon, psiCanon, phiCanon, blockShear, A0, A1_00..A1_32, nativeChart1,`
  `  nativeSel, nativePerm, blockBlowupMap, sigmaC1Fs, sigmaC2Fs, qdisp, sterm, t1P20, t2P20, Function.comp_apply,`
  `  Matrix.of_apply, Matrix.cons_val'..head_fin_const, cpermS20, Equiv.ofBijective_apply, cperm20, Pi.add_apply,`
  `  Fin.isValue, Option.elim, if_true, if_false]; ring`  (per-decl `set_option`s: maxHeartbeats 4000000, maxRecDepth 8000,
  linter.unusedSimpArgs false, linter.style.maxHeartbeats false — see template)
- `canon_hentry` via `simp only [Scanon, Finset.mem_image] at hk; obtain ⟨p,hp,rfl⟩; simp only [zcCanon,`
  `Equiv.symm_apply_apply]; fin_cases hp <;> exact entry_ij` ; then `canon_domination` / `canon_foldedJac` verbatim.

GOTCHA (from the template): numeric literals at `Fin (dvec (Fin.last 2)*dvec 0)` are OfNat/subst-hostile — hence
`Scanon` via `finProdFinEquiv`-image of clean `Fin 4 × Fin 3` pairs + `fin_cases hp`, NEVER raw Fin-12 literals.

NOTE all leaves share the SAME `nativeChart1 20` / `nativeSel 20` / `nativePerm 20` / `t1P20`/`t2P20`/`cperm20`;
only the node-2 pivot p2, node-3 pivot p3, vmExp, and φ change. c=0 entries are pure coords (no φ correction).

---

### leaf (20,1,1) — pattern A COINCIDING  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 1 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 1 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u12, (1,0)→u2, (1,1)→u13, (2,0)→u3, (2,1)→u14, (3,0)→u4, (3,1)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 10 + u 1 * u 16 * u 5)
    if i = 13 then -(u 1 * u 17 * u 5 + u 10 * u 2)
    if i = 14 then -(u 1 * u 18 * u 5 + u 10 * u 3)
    if i = 15 then -(u 1 * u 19 * u 5 + u 10 * u 4)

### leaf (20,1,5) — pattern A  [φ max-deg ⇒ QUADRATIC cover atom]
- `vmExpCanon d := if d = 1 ∨ d = 5 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 1 * u 5 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u12, (1,0)→u2, (1,1)→u13, (2,0)→u3, (2,1)→u14, (3,0)→u4, (3,1)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 10 + u 16 * u 5)
    if i = 13 then -(u 10 * u 2 + u 17 * u 5)
    if i = 14 then -(u 10 * u 3 + u 18 * u 5)
    if i = 15 then -(u 10 * u 4 + u 19 * u 5)

### leaf (20,1,6) — pattern A  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 1 ∨ d = 6 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 1 * u 6 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u12, (1,0)→u2, (1,1)→u13, (2,0)→u3, (2,1)→u14, (3,0)→u4, (3,1)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 10 + u 16 * u 5 * u 6)
    if i = 13 then -(u 10 * u 2 + u 17 * u 5 * u 6)
    if i = 14 then -(u 10 * u 3 + u 18 * u 5 * u 6)
    if i = 15 then -(u 10 * u 4 + u 19 * u 5 * u 6)

### leaf (20,1,7) — pattern A  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 1 ∨ d = 7 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 1 * u 7 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u12, (1,0)→u2, (1,1)→u13, (2,0)→u3, (2,1)→u14, (3,0)→u4, (3,1)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 10 + u 16 * u 5 * u 7)
    if i = 13 then -(u 10 * u 2 + u 17 * u 5 * u 7)
    if i = 14 then -(u 10 * u 3 + u 18 * u 5 * u 7)
    if i = 15 then -(u 10 * u 4 + u 19 * u 5 * u 7)

### leaf (20,5,1) — pattern A  [φ max-deg ⇒ QUADRATIC cover atom]
- `vmExpCanon d := if d = 1 ∨ d = 5 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 1 * u 5 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u16, (1,0)→u2, (1,1)→u17, (2,0)→u3, (2,1)→u18, (3,0)→u4, (3,1)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 10 + u 1 * u 12)
    if i = 17 then -(u 1 * u 13 + u 10 * u 2)
    if i = 18 then -(u 1 * u 14 + u 10 * u 3)
    if i = 19 then -(u 1 * u 15 + u 10 * u 4)

### leaf (20,5,5) — pattern A COINCIDING  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 5 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 5 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u16, (1,0)→u2, (1,1)→u17, (2,0)→u3, (2,1)→u18, (3,0)→u4, (3,1)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 10 + u 1 * u 12 * u 5)
    if i = 17 then -(u 1 * u 13 * u 5 + u 10 * u 2)
    if i = 18 then -(u 1 * u 14 * u 5 + u 10 * u 3)
    if i = 19 then -(u 1 * u 15 * u 5 + u 10 * u 4)

### leaf (20,5,6) — pattern A  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 5 ∨ d = 6 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 5 * u 6 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u16, (1,0)→u2, (1,1)→u17, (2,0)→u3, (2,1)→u18, (3,0)→u4, (3,1)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 10 + u 1 * u 12 * u 6)
    if i = 17 then -(u 1 * u 13 * u 6 + u 10 * u 2)
    if i = 18 then -(u 1 * u 14 * u 6 + u 10 * u 3)
    if i = 19 then -(u 1 * u 15 * u 6 + u 10 * u 4)

### leaf (20,5,7) — pattern A  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 5 ∨ d = 7 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 5 * u 7 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,1)→u16, (1,0)→u2, (1,1)→u17, (2,0)→u3, (2,1)→u18, (3,0)→u4, (3,1)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 10 + u 1 * u 12 * u 7)
    if i = 17 then -(u 1 * u 13 * u 7 + u 10 * u 2)
    if i = 18 then -(u 1 * u 14 * u 7 + u 10 * u 3)
    if i = 19 then -(u 1 * u 15 * u 7 + u 10 * u 4)

### leaf (20,6,1) — pattern B  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 1 ∨ d = 6 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 1 * u 6 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u12, (1,0)→u2, (1,2)→u13, (2,0)→u3, (2,2)→u14, (3,0)→u4, (3,2)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 11 + u 1 * u 16 * u 7)
    if i = 13 then -(u 1 * u 17 * u 7 + u 11 * u 2)
    if i = 14 then -(u 1 * u 18 * u 7 + u 11 * u 3)
    if i = 15 then -(u 1 * u 19 * u 7 + u 11 * u 4)

### leaf (20,6,5) — pattern B  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 5 ∨ d = 6 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 5 * u 6 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u12, (1,0)→u2, (1,2)→u13, (2,0)→u3, (2,2)→u14, (3,0)→u4, (3,2)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 11 + u 16 * u 5 * u 7)
    if i = 13 then -(u 11 * u 2 + u 17 * u 5 * u 7)
    if i = 14 then -(u 11 * u 3 + u 18 * u 5 * u 7)
    if i = 15 then -(u 11 * u 4 + u 19 * u 5 * u 7)

### leaf (20,6,6) — pattern B COINCIDING  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 6 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 6 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u12, (1,0)→u2, (1,2)→u13, (2,0)→u3, (2,2)→u14, (3,0)→u4, (3,2)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 11 + u 16 * u 6 * u 7)
    if i = 13 then -(u 11 * u 2 + u 17 * u 6 * u 7)
    if i = 14 then -(u 11 * u 3 + u 18 * u 6 * u 7)
    if i = 15 then -(u 11 * u 4 + u 19 * u 6 * u 7)

### leaf (20,6,7) — pattern B  [φ max-deg ⇒ QUADRATIC cover atom]
- `vmExpCanon d := if d = 6 ∨ d = 7 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 6 * u 7 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u12, (1,0)→u2, (1,2)→u13, (2,0)→u3, (2,2)→u14, (3,0)→u4, (3,2)→u15
- `Zcanon = {0, 12, 2, 13, 3, 14, 4, 15}`  (straightened block = [12, 13, 14, 15] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 12 then -(u 0 * u 11 + u 16 * u 7)
    if i = 13 then -(u 11 * u 2 + u 17 * u 7)
    if i = 14 then -(u 11 * u 3 + u 18 * u 7)
    if i = 15 then -(u 11 * u 4 + u 19 * u 7)

### leaf (20,7,1) — pattern B  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 1 ∨ d = 7 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 1 * u 7 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u16, (1,0)→u2, (1,2)→u17, (2,0)→u3, (2,2)→u18, (3,0)→u4, (3,2)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 11 + u 1 * u 12 * u 6)
    if i = 17 then -(u 1 * u 13 * u 6 + u 11 * u 2)
    if i = 18 then -(u 1 * u 14 * u 6 + u 11 * u 3)
    if i = 19 then -(u 1 * u 15 * u 6 + u 11 * u 4)

### leaf (20,7,5) — pattern B  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 5 ∨ d = 7 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 5 * u 7 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u16, (1,0)→u2, (1,2)→u17, (2,0)→u3, (2,2)→u18, (3,0)→u4, (3,2)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 11 + u 12 * u 5 * u 6)
    if i = 17 then -(u 11 * u 2 + u 13 * u 5 * u 6)
    if i = 18 then -(u 11 * u 3 + u 14 * u 5 * u 6)
    if i = 19 then -(u 11 * u 4 + u 15 * u 5 * u 6)

### leaf (20,7,6) — pattern B  [φ max-deg ⇒ QUADRATIC cover atom]
- `vmExpCanon d := if d = 6 ∨ d = 7 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 6 * u 7 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u16, (1,0)→u2, (1,2)→u17, (2,0)→u3, (2,2)→u18, (3,0)→u4, (3,2)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 11 + u 12 * u 6)
    if i = 17 then -(u 11 * u 2 + u 13 * u 6)
    if i = 18 then -(u 11 * u 3 + u 14 * u 6)
    if i = 19 then -(u 11 * u 4 + u 15 * u 6)

### leaf (20,7,7) — pattern B COINCIDING  [φ max-deg ⇒ CUBIC cover atom]
- `vmExpCanon d := if d = 7 ∨ d = 20 then 1 else 0`   (∏ u^vmExp = u 7 * u 20)
- reg-seq pairs → zc: (0,0)→u0, (0,2)→u16, (1,0)→u2, (1,2)→u17, (2,0)→u3, (2,2)→u18, (3,0)→u4, (3,2)→u19
- `Zcanon = {0, 16, 2, 17, 3, 18, 4, 19}`  (straightened block = [16, 17, 18, 19] + pure [0, 2, 3, 4])
- `phiCanon`:
    if i = 16 then -(u 0 * u 11 + u 12 * u 6 * u 7)
    if i = 17 then -(u 11 * u 2 + u 13 * u 6 * u 7)
    if i = 18 then -(u 11 * u 3 + u 14 * u 6 * u 7)
    if i = 19 then -(u 11 * u 4 + u 15 * u 6 * u 7)
