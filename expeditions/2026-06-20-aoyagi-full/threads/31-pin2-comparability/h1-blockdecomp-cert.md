# h1 (per-layer block decomp) + h2/h3 sanity — build-ready cert

The producer's germ-charge `sorry` (DeepestGaugeConstruction:2680) needs three obligations feeding the
banked bridge `germ_charge_of_schur_factorization`. h1 (the block decomp ⇒ `hR`) is the heaviest;
h2/h3 sanity-checked against the bridge's hypotheses. **Honest read: h1 MODERATE (2 tides); h2 CLEAN
(banked shared bridge); h3 needs a NON-obvious regrouping (2 new off-diag-block bounds) — MODERATE, NOT
the squared-K dead-end the naive route hits.** Decorrelated Codex (xhigh) on h1 effort + the h2/h3 risks;
all algebra sympy/numeric-verified. Read-only.

## The exact target (what `hR` is)
The producer's `Mw := reindex(rThr, pivotThr J)(P0·(prod(symm w)−B)·QL)`, `Rcore := Mw₂₂ − Mw₂₁·(Mw₁₁+1)⁻¹·Mw₁₂`.
The bridge needs `hR : Rcore = S0·(1−K)·S1` (then the BANKED `schur_product_ldu` + S5c close it).

## h1 — the per-layer block decomposition (MODERATE, 2 tides)

`M̂w := reindex(rThr, pivotThr J)(prod F)` (the FRAMED product reindexed). By the banked `hRegBlocks`,
`M̂w = corner + Mw`, so `M̂w₁₁ = Mw₁₁+1` (the Rcore pivot), `M̂w₁₂=Mw₁₂`, etc. The claim:
**`M̂w = C0·C1`** where `C_s = fromBlocks A_s Y_s Z_s T_s` are the `rThr`-blocks of `(symm w)_s` (the raw
symm-product layer — NOT frame-conjugated; `hS1`/`hS2_front` already strip the frames to `P0·prod(A w)·QL`).

Two Lean facts:
1. **`reindex_mul` (shared-middle cancel):** `reindex(rThr_{H0}, rThr_{Hlast})(F_0·F_1) =
   reindex(rThr_{H0}, rThr_{Hmid})(F_0) · reindex(rThr_{Hmid}, rThr_{Hlast})(F_1)`. Mathlib
   `submatrix_mul_equiv` / repo `reindex_fromBlocks_mul` pattern. **Risk (Codex): cast noise from
   `castSucc`/`succ`/threshold-proof on the middle `Hmid` split** — needs a local normalization lemma
   around `submatrix_mul_equiv`, NOT a deep grind. ~the bulk of h1's LoC.
2. **Per-layer block read:** `reindex(rThr, rThr)((symm w)_s) = fromBlocks A_s Y_s Z_s T_s` with
   `A_s = 1+readX_s, Y_s=readY_s, Z_s=readZ_s, T_s=coreRead_s` — via the BANKED
   `reindex_fromBlocks_reads_eq_deviation` ((symm w)_s = deepest_s + deviation, deepest_s = the corner
   fromBlocks 1 0 0 0) + the affine bridge. (For front pivot the last-layer col split is `pivotThr J=rThr`.)

Then `fromBlocks_multiply` ⇒ `M̂w` blocks `= (A0A1+Y0Z1, A0Y1+Y0T1, Z0A1+T0Z1, Z0Y1+T0T1)`, and the
banked `schur_product_ldu` ⇒ `Rcore = S0·(1−K)·S1` = `hR`. **`A_s` invertible** (= `1+readX_s → 1` at w0,
det-continuity on a nbhd, same as S5a's `Invertible P00`); `schur_product_ldu` needs only that.

**Effort: MODERATE 2 tides** (~150-250 LoC). The math is the banked LDU; the work is the reindex_mul
middle-cancel (the cast-noise risk) + the per-layer block read (banked deviation lemma + unfold). NOT a
frame-residue problem (Codex's clean-case) — the frames are stripped BEFORE, the blocks are the raw
`(symm w)_s` rThr-blocks.

## h2 — core identification: CLEAN (matches the bridge, banked shared bridge)

The bridge's `hCore : coreΦ w = frobSq(S0 w · S1 w)` needs the SAME cores `S_s = T_s − Z_s·⅟A_s·Y_s` as
h1/`schur_product_ldu`. lemma-1 (`deepestCoreF_coreAbsorb`, banked) gives `coreΦ = frobSq(∏ S'_s)`,
`S'_s = (symm core)_s + schurCorrection_s`. **They MATCH exactly:**
- `(symm core)_s = coreRead_s = T_s` (the same core read).
- `schurCorrection_s = −readZ_s·(1+readX_s)⁻¹·readY_s = −Z_s·⅟A_s·Y_s` (with `A_s = 1+readX_s`, the
  SAME pivot block as h1, via `reindex_fromBlocks_reads_eq_deviation`).
⇒ `S'_s = T_s − Z_s·⅟A_s·Y_s = S_s`. **h2 is NOT heavier** — the `⅟(1+readX_s)` in `schurCorrection`
IS `schur_product_ldu`'s `⅟A_s` (both read off the SAME deviation lemma). Codex's flagged risk
("framed-vs-raw `⅟A_s` mismatch") does NOT bite: both are the raw `1+readX_s`.

## h3 — the remainder charge: needs a NON-OBVIOUS REGROUPING (MODERATE)

The bridge's `hRem : frobSq(R − S0·S1) ≤ Crem·Sreg²`. `R − S0·S1 = −S0·K·S1`, `K = Z1·⅟P·Y0`.
**The naive submult route FAILS** (verified): `frobSq(S0·K·S1) ≤ frobSq S0·frobSq K·frobSq S1` then
needs `frobSq K ≤ C·Sreg²` (BLOWS UP, `~3e4`) OR `frobSq S_s ≤ C·Sreg` (BLOWS UP — `S_s` contains the
CORE `T_s`, NOT in Sreg). Both dead ends.

**The CLEAN route — REGROUP:** `R − S0·S1 = −(S0·Z1)·⅟P·(Y0·S1)`. The blocks `S0·Z1`, `Y0·S1` each pair
a core-bearing `S` with a REGULAR read (`Z1, Y0`), landing them in the OFF-DIAGONAL Schur blocks that
Sreg controls. Verified (numeric, all 3 scales): `frobSq(S0·Z1)/Sreg → 0` and `frobSq(Y0·S1)/Sreg → 0`
(bounded by `~2.7` at 1e-1, `0.03` at 1e-2). So:

    frobSq(R−S0S1) = frobSq((S0Z1)·⅟P·(Y0S1)) ≤ frobSq(S0Z1)·‖⅟P‖²·frobSq(Y0S1)
      ≤ (C·Sreg)·‖⅟P‖²·(C·Sreg) = Crem·Sreg².

**The two NEW sub-bounds** (the genuine h3 work): `frobSq(S0·Z1) ≤ C·Sreg` and `frobSq(Y0·S1) ≤ C·Sreg`.
`S0·Z1` = the (2,1) off-diag block of `D0·(U0 L1)·D1` (the LDU middle, h1's step 3); `Y0·S1` = the (1,2).
These ARE the off-diagonal Schur blocks — and `Schur-invariance` (h1's step 2) ties them to `Mw₂₁, Mw₁₂`
(the Sreg blocks) up to the unipotent shifts. So the bound routes through the SAME LDU h1 builds.
**Effort: MODERATE** — 2 new linear sub-bounds + `frobenius_mul_le` (banked) + the `⅟P` bound (S5a-style).
NOT clean-one-liner, NOT a wall.

## NET ranking + biggest risk
1. **h1 MODERATE (2 tides)** — the reindex_mul middle-cancel cast-noise is the watch-item; the LDU + block
   read are banked/unfold.
2. **h3 MODERATE** — the regrouping `R−S0S1 = (S0Z1)⅟P(Y0S1)` is non-obvious (the naive submult is a dead
   end), then 2 off-diag-block linear bounds. Tie the off-diag blocks to Sreg via the LDU (reuses h1).
3. **h2 CLEAN** — matches the bridge via the banked `reindex_fromBlocks_reads_eq_deviation`; the `⅟A_s`
   align. NOT heavier (Codex's framed-vs-raw risk doesn't bite — both raw `1+readX`).

**Biggest risk across all three: the h3 regrouping route** — `hRem` as the bridge LITERALLY states it
(`≤ Crem·Sreg²`) is TRUE but ONLY via the regroup (`(S0Z1)⅟P(Y0S1)`), NOT the naive submult. **Flag to
the formaliser: do NOT attempt `frobSq S0·frobSq K·frobSq S1` (dead end — core escapes Sreg); use the
regrouped form + the 2 off-diag-block bounds.** This is the one place an optimistic build thrashes.

## Honest overall (third estimate, ruthless)
NOT a deep research-grade multi-tide grind. **h1+h3 together ~2-3 tides, h2 ~contained.** The math is all
verified (h1 LDU banked; h2 cores match; h3 regroup numeric-bounded). The risks are Lean-plumbing
(reindex_mul cast-noise) + the ONE non-obvious h3 regrouping (which I've pinned, so the formaliser won't
thrash). The bridge `germ_charge_of_schur_factorization` is banked and its `hRem ≤ Crem·Sreg²` form IS
achievable (via the regroup) — no bridge-restatement needed.

## Build-ready new lemmas
- `Mw_eq_blockProduct` (h1): `reindex(rThr,pivotThr J)(prod F) = C0·C1`, `C_s` = the rThr-blocks of (symm w)_s.
  (reindex_mul + per-layer block read.) ⇒ `hR` via `schur_product_ldu`.
- `coreΦ_eq_frobSq_prodSchur` (h2): `coreΦ = frobSq(S0·S1)` with the matched cores (lemma-1 + the read align).
- `frobSq_S0Z1_le_Sreg`, `frobSq_Y0S1_le_Sreg` (h3, the 2 off-diag bounds) → `frobSq(R−S0S1) ≤ Crem·Sreg²`
  via the regroup + `frobenius_mul_le` + `⅟P` bound.
Then the producer's germ-charge = `germ_charge_of_schur_factorization` applied with these.

## Files
- `/tmp/h1_design.py`, `h2_reconcile.py`, `h3_gap.py`, `h3_route.py`, `h3_final.py`, `h3_regroup.py`,
  `hrem_check.py` (the route + the regroup + the dead-end identification). `codex/h1-blockdecomp-*` (the
  decorrelated effort read + h2/h3 risk flags). Banked: `schur_product_ldu`, `germ_charge_of_schur_factorization`,
  `reindex_fromBlocks_reads_eq_deviation`, `deepestCoreF_coreAbsorb`, `hS2_front`/`hRegBlocks`, `frobenius_mul_le`.
