# Certificate — the parametric `B_det M` decoder (build-ready, the LAST design gate)

**Seat:** pen-and-paper (witness). **Date:** 2026-06-27. The last design gate before the multi-tide build
(B_det+rate+Ubound → bridge → cov+assemble). Specifies the width-parametric `B_det M` / `active` / `leafH_M`
/ the nonzero-VvalGen witness, extracted from the two banked anchors (`B_det222` L=2, `B_det3333` L=3) +
step-1 (`tStar`/`rBlock`/`cBlock`, banked `RouteMAchieverPath`). Closes the route-(i)-parametric plan of
`certificate-genM-det.md`.

Decorrelated xhigh Codex (independent, sharp verdict — confirms the pattern + specialization + no research
wall): `codex/genM-Bdet-{prompt,answer}.md`. Exact scripts: `scripts/extract_Bdet.py`, `count_actual.py`,
`reconcile_widths.py`, `check_334_and_flatdim.py`, `vval_witness.py`, `pivot_survives.py`.

**VERDICT — the construction is fully specified and reproduces both anchors. NO research wall.** The one
genuine residual is the uniform nonzero-VvalGen "pivot-survival" lemma (substantial dependent-width
engineering, but uniform ∀M — NOT per-M). Everything else (active.card=minAdm, minAdm≤N, leafH) is
construction-level/banked.

---

## 1. The chain ↔ Aoyagi bridge (the indexing that makes the placement parametric)

Step-1 banks `tStar M : Fin L → ℕ` (the Aoyagi minimizer, `Mval_tStar_eq = minAdm`), `rBlock M j =
tPrev − tStar` (rows), `cBlock M j = M_{j+1} − tStar` (cols), `sum_rBlock_cBlock_eq_minAdm`. The CHAIN
decoder uses `tach M : Fin (L+1) → ℕ`, the descent ranks: **`tach 0 = M_0`** (identity boundary,
`Text 0 = Text 1`), **`tach (k+1) = tStar k`** (so `Text (k+1) = tStar k`), `tach L = 0`-ish (the leaf rank).

**The exact correspondence (verified, `scripts/reconcile_widths.py`):** Aoyagi block `j` (`j = 0..L−1`)
realizes at **chain boundary `k = j+1`**:
- `j < L−1` → the INTERIOR `Rmat_{j+1}` bottom-right E-block, dims `r_{j+1} × c_{j+1}` where (chain)
  `r_{k} = Text_k − Text_{k+1} = tStar_{k−1} − tStar_k = rBlock_{k−1}`,
  `c_{k} = Wext_k − Text_{k+1} = M_k − tStar_k` — which equals the Aoyagi `cBlock_{k−1} = M_{(k−1)+1} −
  tStar_{k−1}`… (the chain leaf uses `Wext_L = M_L`, `Text_L = tStar_{L−1}`, matching `cBlock_{L−1}`);
- `j = L−1` → the LEAF `Rfin_L`, dims `Text_L × Wext_L = tStar_{L−1} × M_L`.

The dims line up so the chain E-block sum = the Aoyagi block sum = `minAdm` for all anchors (222: 1+2=3;
3333: 1+2+3=6; 221: 1+1=2; 334: 4+4=8 — `scripts/reconcile_widths.py`, exact).

---

## 2. The parametric `B_det M : GenBlk M (tach M)` (reproduces both anchors)

Per boundary `k`, at the opaque widths `Text`/`Wext`. The free flat coords are read from disjoint
`FlatIdx` slots (canonical order). The five fields:

- **`Bmat 0 = Matrix.reindex (Equiv.refl) (finCongr (Text_0 = Text_1)) (1)`** — the identity boundary
  (PRESERVED; `Text_0 = Text_1 = M_0` since `tach 0 = M_0`). **`Rmat 0 = 0`**. This keeps `hC0` (`C 0 = 1`,
  the `C0_eq_one_gen` proof reads only these) and the banked decoder-agnostic rate `routeMCore_phiGen`
  untouched. `Nblk 0`/`Wblk 0` are the empty `c_0 = 0` blocks.

- **`Bmat (k+1)` (interior, `k = 0..L−1`)** = the Schur kept-frame `[K_k ; X_k·K_k]` (`bmatStack`), `Text_k ×
  Text_{k+1}`. `K_k` (the LDU core, `Text_{k+1} × Text_{k+1}`) + `X_k` (the shear, `r_k × Text_{k+1}`) read
  from `FlatIdx` slots — the NON-active spectator coords (carry the per-boundary Schur/LDU spectator dets).

- **`Nblk (k+1)`** = the chaining residual `N_k` (`Text_{k+1} × c_k`); **`Wblk (k+1)`** = the lift `W_k`
  (`(Wext_k − Text_{k+1}) × Wext_{k+1}`). Both spectators (NON-active).

- **`Rmat (k+1)` (interior)** = `rmatPad` of the E-block into the bottom-right `r_k × c_k` (zeros elsewhere),
  `Text_k × Wext_k`. The E-block entries are the ACTIVE angular normals (`x_p · angular`), EXCEPT the one
  designated fixed-1 pivot entry (a CONSTANT `1`, not read from `x` — `u = x_p` scales it).

- **`Rfin L`** = the LIVE leaf residual `Text_L × Wext_L` (the D1 fix — NONZERO), all entries ACTIVE
  (angular, or the fixed-1 pivot if the pivot is placed in the leaf).

**The fixed-1 pivot — canonical choice** (Codex Q1; det-invariant, so any nonempty active block works): the
cleanest uniform rule is **"the leaf `Rfin_L (0,0)` = the fixed 1"** (reproduces `B_det222`'s
`Rfin_2 = !![1, x7]`) — valid whenever the leaf block is nonempty (`Text_L ≥ 1`, `Wext_L = M_L ≥ 1`, always
for a genuine chain). (Alternatively "first nonempty E-block, top-left" reproduces `B_det3333`'s
`Rmat_1(2,2) = 1`; both give the SAME det `|x_p|^{minAdm−1}` — only `active.card` matters.) **Recommend the
leaf-(0,0) rule** — uniform, always nonempty, matches the simpler L=2 anchor.

**Specialization check (Codex Q1 confirms):**
- `B_det222`: `Bmat_1 = [x4;x5]` (`K=x4`, `X=x5`), `Nblk_1=[x1]`, `Wblk_1=[x2,x3]`, `Rmat_1` E-block `x6`,
  `Rfin_2 = [1, x7]` (pivot `(0,0)=1`, active `x7`). active = {pivot, x7, x6} = 3 = minAdm. ✓
- `B_det3333`: `Bmat_1`(3×2 LDU `K`), `Bmat_2=[x9;x10·x9]`, `Rmat_1` E-block (the fixed-1 at `(2,2)`),
  `Rmat_2` E-block `[x13,x14]`, `Rfin_3 = [x24,x25,x26]`. active = {pivot, x13,x14, x24,x25,x26} = 6 = minAdm.
  ✓ (This uses the interior-pivot variant; the leaf-(0,0) rule would place the pivot at `Rfin_3(0,0)` instead
  — an equally-valid chart, same det.)

---

## 3. `active : Finset (Fin N)` + `minAdm ≤ N` (RESOLVED — construction-level, no extra hypothesis)

`active := Finset.univ.filter (isAoyagiResidualSlot M ∘ decodeFlatIdx)` — the decidable set of the `minAdm`
residual-normal slots (the interior E-blocks + the leaf Rfin), pivot `p ∈ active` (the fixed-1 slot's
canonical `FlatIdx`). `active.card = minAdm M` (banked `sum_rBlock_cBlock_eq_minAdm` + the chain↔Aoyagi
dim match §1). `radialFactor active p` det `|x_p|^{active.card − 1} = |x_p|^{minAdm − 1}`.

**`minAdm ≤ N` is AUTOMATIC** (Codex Q2; `scripts/check_334_and_flatdim.py` confirms for all anchors): the
active normals are a SUBSET of the residual coords, themselves a subset of the `N = ∑_k M_k M_{k+1}` flat
coords: `active ⊆ residualCoords ⊆ Fin N`, so `active.card = minAdm ≤ N`. **Construction-level — NOT a
separate admissibility hypothesis to prove.** (The `Finset.filter` on `Fin N` makes `active.card ≤
Fintype.card (Fin N) = N` immediate; the `= minAdm` is the banked sum identity.)

---

## 4. `leafH_M : Fin N → ℕ`

`leafH_M p = minAdm M − 1` (the radial pivot, the binding axis — `leafH_pivot`); on the per-boundary
Schur/LDU spectator axes (the `k=0` axes), the spectator exponents (`schurFrame` `r_j+c_j` powers of
`|det K_j|`, `lduCore` `2(t−1−i)` powers of `|q_i|`); `0` elsewhere. `∏_j |x_j|^{leafH_M j} = |det Dφ_M|`
(the radial `|x_p|^{minAdm−1}` × spectators), matched against `composeFold_abs_det`. Only `leafH_M p =
minAdm−1` is threshold-relevant; the spectators are on `k=0` axes (ratio `⊤`, do not lower `½·minAdm`).
(3,3,4): `leafH = {0:7, 1:2}`; (3,3,3,3): `{0:5, 1:4, 4:2, 9:3}` — banked.)

---

## 5. The parametric nonzero-VvalGen witness (the ONE genuine residual — uniform, NOT per-M)

The rate gives `F = (x_p)²·VvalGen`; the node bundle needs `VvalGen > 0` a.e. + bounded/measurable. `VvalGen
= ‖H‖²` with `prod = u·H`, `H = reindex (Hmat_0)`. The a.e.-positivity is the nonzero-polynomial zero-set
route (`Uval222_ae_pos` pattern) — needs `VvalGen ≢ 0`, i.e. `Hmat_0 ≢ 0`.

**The UNIFORM witness** (`scripts/vval_witness.py`, `verify_witness.py`, `pivot_survives.py`): the witness
point `w := {all Bmat_k(0,0) = 1 (the kept-diagonal), all Nblk/Wblk/angular = 0, the fixed-1 pivot = 1, u
arbitrary}`. At `w`:
- `chainQ(N_k = 0) = [I | 0]` (zero residual cols), so `C_k = [Bmat_k | 0] + u·Rmat_k`;
- the coupling terms `E_k · suffix_{k+1}` VANISH (the angular E-entries are 0; only the fixed-1 pivot
  survives, injecting one nonzero entry);
- `Hmat_0 (0,0) = (∏_k Bmat_k(0,0)) · (leaf/pivot value) = 1·…·1 = 1 ≠ 0` — the all-kept telescoping path.

So `Hmat_0 ≢ 0`, `VvalGen` is a nonzero polynomial, `{VvalGen = 0}` is Lebesgue-null, `VvalGen > 0` a.e.
(222 check exact: `M222bar(0,0) = x4 = 1` at `w`, `‖H‖² = 1 > 0`.) **This is the parametric analog of
`UPoly222_ne_zero` — ONE witness-point FORMULA ∀M, not a per-M search.**

**Sharp caveat (Codex Q3, my read):** formalizing it needs a **dependent-width "pivot-survival"
telescoping lemma**: `Hmat_0(0,0)` evaluated at `w` equals `∏_k Bmat_k(0,0)·1 = 1` over opaque widths
(the `Hmat` recursion `Hmat_k = Bmat_k·Hmat_{k+1} + E_k·suffix_{k+1}`, with the coupling killed at `w`).
**Real engineering, but uniform.** Boundedness/measurability (`Ubound`/`Umeas`) are the existing
continuous-polynomial obligations (VvalGen is a polynomial in `x` — `continuous_Uval222` pattern).

---

## 6. Specialization-validated + (3,3,4) check

| `M` | minAdm | `tach` (chain) | Aoyagi blocks | chain E-blocks (int + leaf) | active.card | banked |
|-----|--------|----------------|---------------|------------------------------|-------------|--------|
| (2,2,1) | 2 | (2,1,0) | (1,1),(1,1) | int k=1: 1×1; leaf 1×1 | 1+1=2 | — |
| (2,2,2) | 3 | (2,1,0) | (1,1),(1,2) | int k=1: 1×1; leaf 1×2 | 1+2=3 | `B_det222` ✓ |
| (3,3,4) | 8 | (3,1,0) | (2,2),(1,4) | int k=1: 2×2=4; leaf 1×4=4 | 4+4=8 | (check) ✓ |
| (3,3,3,3) | 6 | (3,2,1,0) | (1,1),(1,2),(1,3) | int k=1:1, k=2:2; leaf 3 | 1+2+3=6 | `B_det3333` ✓ |

(All exact, `scripts/reconcile_widths.py`/`check_334_and_flatdim.py`.) The **(3,3,4)** check: `tach=(3,1,0)`,
`Text=[3,3,1]`, the interior boundary `k=1` has E-block `r_1×c_1 = (Text_1−Text_2)×(Wext_1−Text_2) = (3−1)×
(3−1) = 2×2 = 4` (the genuine Schur K with `r=2`), leaf `Rfin_2 = Text_2×Wext_2 = 1×4 = 4`; active.card =
8 = minAdm. The fixed-1 pivot at `Rfin_2(0,0)` (leaf rule), radial `|x_p|^{8−1}=|x_p|^7`, matching the banked
`RouteMLayerCoverGEL2` `leafH334 0 = 7`. ✓ My parametric `B_det` formula reproduces it.

---

## 7. Residual risk / kill-conditions (NONE a research wall — Codex Q4 confirms)

| piece | status |
|-------|--------|
| parametric `B_det M` (the 5 fields over opaque widths) | substantial dependent-width engineering (`bmatStack`/`rmatPad` banked, the per-boundary `match`-on-`k` + the `FlatIdx` slot readers); NOT research |
| `active : Finset`, `active.card = minAdm`, `p ∈ active` | routine (banked sum identity + the chain↔Aoyagi dim match); the decidable `isAoyagiResidualSlot` filter |
| `minAdm ≤ N` | immediate (`active ⊆ Fin N`) |
| `leafH_M` (radial minAdm−1 + spectators) | banked-shape (`leafH222`/`leafH3333` templates), parametric |
| **nonzero-VvalGen pivot-survival lemma** | **the main remaining proof burden** — the dependent-width `Hmat_0(0,0)|_w = 1` telescoping. Uniform ∀M (NOT per-M), but real engineering. The one to watch. |
| the bridge `chartParamsGen = pack_M ∘ T_M` | the `certificate-genM-det.md` route-(i) funext (separate gate, the heavy det piece) |

**The ordering for the build tides:** (1) parametric `B_det M` + `hleStruct`/`hC0` (rate FREE via
`routeMCore_phiGen`); (2) `active`/`leafH_M`; (3) the nonzero-VvalGen pivot-survival lemma (Ubound/Umeas);
(4) the route-(i) bridge `chartParamsGen = pack_M ∘ T_M` (det); (5) `cov` + `nodeChartGeneral` + atom.
Validate each on (3,3,4) (the genuine `r=2` Schur K) before the ∀M lift.

---

## Close

**Firmest result:** the parametric `B_det M` is fully specified — `Bmat 0 = reindex I`/`Rmat 0 = 0`
(preserves rate+hC0); interior `Bmat (k+1) = [K;XK]`, `Rmat (k+1) = rmatPad(E)`; LIVE leaf `Rfin L`; the
fixed-1 pivot at the canonical `Rfin_L(0,0)`. `active` = the interior-E + leaf-Rfin slots, `active.card =
minAdm ≤ N` (construction-level). `leafH_M p = minAdm−1` + k=0 spectators. The nonzero-VvalGen witness is
uniform (`Hmat_0(0,0)|_w = ∏ Bmat_k(0,0)·1 = 1`). Specialization-validated against `B_det222`/`B_det3333` +
a (3,3,4) check. Triple-confirmed (anchor extraction / sympy / xhigh Codex).

**Most likely to bite:** the nonzero-VvalGen pivot-survival lemma (#5) — the dependent-width `Hmat`
evaluation at the witness; uniform ∀M but genuine engineering. The route-(i) bridge funext
(`certificate-genM-det.md`) is the other heavy piece. **NO research wall** (Codex Q4): every sub-piece is
substantial-but-bounded dependent-width work with banked templates, not an open design question.

**Next construction that settles it:** build the parametric `B_det M` (the `match`-on-`k` decoder over the
banked `bmatStack`/`rmatPad`/`FlatIdx`-readers), then the pivot-survival witness lemma, on (3,3,4) first;
the rate, active.card, leafH, and minAdm≤N are construction-level/banked.

---

## BUILD-TIDE ADDENDUM (2026-06-27) — two corrections to §5

The first build tide (rate-side phases 1–3) landed phase-0 (`tach M` + `StructAdm M (tach M)`, the achiever
admissibility, with `StructAdm.hdesc` weakened `∀k → ∀k, k<L→` since `tStar(last)=0` makes `hdesc L` false)
+ the FREE rate-side fields (`achiever_leaf_integrand` ∀M, `routeMCore_achieverPhi`, `achieverUfun_nonneg` —
`RouteMAchieverRateFields.lean`, axiom-clean). Two corrections to §5's framing surfaced:

1. **The live leaf is NOT needed for the RATE side / witness** (only for the DET-side full-rank `cov`). The
   STRUCTURED DEAD-leaf decoder (`genBlkFlatStruct`, `Rfin=0`) already has `VvalGen ≢ 0` for `L ≥ 2`: the
   telescope's INTERIOR `E_k = Rmat_k·A_k` terms feed `Hmat_0` even when `Hmat_L = Rfin_L = 0`. Sympy
   `(2,2,2)`: `Hmat_0 = [[0,0],[E·w0, E·w1]]`, `VvalGen = E²(w0²+w1²)` (=1 at `E=1,w0=1`). So §5's "the dead
   leaf makes `Hmat_0=0` at the witness" is true ONLY for the all-kept/all-zero witness — a DIFFERENT witness
   (interior E,W nonzero) makes it nonzero without any live leaf.
2. **BUT the dead-leaf route FAILS for `L = 1`** (`Hmat_0 = 0`, `VvalGen ≡ 0`: only the identity boundary +
   dead leaf). So a UNIFORM ∀M a.e.-positivity needs EITHER the live-leaf `B_det M` (clean uniform witness
   `Hmat_0(0,0) = ∏Bmat_k(0,0)·1 = 1`) OR an `L=1` case split + an interior-nonempty hypothesis.

3. **The `B_det M` live-leaf sub-design §2 UNDER-SPECIFIED** (the genuine residual for the live route): the
   leaf `Rfin L : Text L × Wext L` does NOT fit the dead `Rmat L = rmatPad(readE)` E-role slot
   `r_{L-1} × c_{L-1}` — the leaf is the FULL `Text L × Wext L`, the E-role is the residual sub-block. Routing
   leaf coords needs a slot-accounting design (which flat coords feed the full leaf vs the interior E-blocks)
   — `flatDim = ∑_k (schurDim k + liftDim k)` has no separate leaf budget; the leaf must reuse the slot the
   dead `Rmat L` (chart-slot `L-1`'s E-role) currently wastes, but at a LARGER dimension. This is the genuine
   `B_det M` design question to settle before the live build.

4. **The a.e.-positivity needs the recursion-level `MvPolynomial` encoding REGARDLESS of leaf choice** (Codex
   `codex/deadleaf-vval-aepos`, ×2 on Q4): the witness gives non-vacuity at ONE point; a.e.-positivity needs
   `{VvalGen=0}` null, i.e. `MvPolynomial.ae_eval_ne_zero` on a NAMED nonzero `UPolyGen` with
   `eval x UPolyGen = VvalGen`. The cleanest (Codex Q2 rank ii): a parallel `PolyHmat`/`PolySuffix` recursion
   over `MvPolynomial (Fin N) ℝ` + ONE `eval`-naturality lemma — but the banked `Chain`/`Hmat`/`suffix`
   engine is `ℝ`-PINNED, so this is either a ring-generalization of that engine or a hand-built parallel
   recursion (a substantial, well-defined multi-tide piece). Q3's "one entry = 2-coord monomial ∀M" does NOT
   generalise (deepest block propagates through `B_1·…·B_{L-2}`; residual col width >1 → a sum).
