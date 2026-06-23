# Lift-cert: rank_rectangular_partial_identity to Core (crux2 → rs-grind, 2026-06-23)

Controller option (b): lift the rectangular-partial-identity rank to Core (`rank_rectangular_partial_identity`,
the 2nd-use home; #116/CascadeRank is the 2nd use). One-writer: rs-grind owns #116/CascadeRank → builds the
Core lemma + cites it; crux2 supplies THIS construction-cert (the proof recipe), NOT the commit.

## The lemma (already PROVEN on the spine, to lift verbatim)

`Skeleton.lean:566`, `Dblock_rank` (private) — the exact statement:

    theorem rank_rectangular_partial_identity {m n r : ℕ} (hrm : r ≤ m) (hrn : r ≤ n) :
        (Matrix.of (fun (i : Fin m) (j : Fin n) =>
          if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℝ) else 0)).rank = r

That is `rank [[I_r, 0],[0, 0]]_{m×n} = r`. Bypasses the square-only `rank_diagonal`.

## The construction (transcribe to Core)

THREE matrices (the rectangular partial-identity = its r-column-by-r-row factorisation):
- `Dc : Matrix (Fin m) (Fin r) ℝ := Matrix.of (fun i k => if (i:ℕ)=(k:ℕ) then 1 else 0)`  (m×r embed)
- `Dr : Matrix (Fin r) (Fin n) ℝ := Matrix.of (fun k j => if (k:ℕ)=(j:ℕ) then 1 else 0)`  (r×n project)
- `Sec : Matrix (Fin n) (Fin r) ℝ`, `DrM : Matrix (Fin r) (Fin m) ℝ` — the right-/left- one-sided inverses.

PROOF (le_antisymm):
1. `hfac`: the partial-identity = `Dc * Dr` (`Dblock_factor`, Skeleton.lean — the `(i=j ∧ i<r)` indicator
   factors as embed·project; ext + per-block `if`-case).
2. `hle : (Dc*Dr).rank ≤ r`: `rank_mul_le_left` ≤ `Dc.rank` ≤ `rank_le_card_width` = `r` (Dc has r columns).
3. `hge : r ≤ (Dc*Dr).rank`: the one-sided-inverse SANDWICH —
   `r = rank (1 : r×r)` [rank_one, card_fin]
     = `rank (DrM * Dc)` [`proj_emb_eq_one hrm : DrM * Dc = 1` — the LEFT inverse]
     ≤ `Dc.rank` [rank_mul_le_right]
     = `rank ((Dc*Dr) * Sec)` [`hDceq : (Dc*Dr)*Sec = Dc`, via `proj_emb_eq_one hrn : Dr*Sec = 1` + mul_one]
     ≤ `(Dc*Dr).rank` [rank_mul_le_left].
4. `le_antisymm hle hge`.

DEPENDENCIES to lift alongside (or inline): `Dblock_factor` (the indicator=Dc·Dr factor) +
`proj_emb_eq_one` (the `project · embed = I_r` one-sided inverse, both orientations). Both private in
Skeleton.lean (`proj_emb_eq_one`:528, `Dblock_factor`:544; `Dblock_rank`:566). For the Core lemma, EITHER
lift these two helpers too, OR inline their short proofs (each is an `ext` + `Finset.sum_eq_single` +
`if`-case, ~10 lines). The Core home: `DLNFibre/Core/Matrix/RankNormalForm.lean:46` (where
`rank_normal_form_exists` already lives — the natural neighbour; #77's frame consumes it). de-private route
is also fine if you'd rather cite Skeleton directly, but Core is the clean 2nd-use home per lean/CLAUDE.md.

DEDUPE: if #116/CascadeRank already RE-DERIVED this rank (the re-derive trap — rung 1 landed green),
drop the re-derivation and cite the Core lemma. (Controller routed fm3 to check rung-1 status.)

## BONUS — rung-3 (window-min product) spine precedent (don't re-derive THIS either)

Flagging before the later rungs re-derive: the "window-min product" RLCT machinery is ALREADY on the spine —
- `S1ProductMin.lean:180` `product_min_rlct` + `:255` `product_min_rlct_of_ne` (the product-min RLCT, the
  ⨅-of-factors content).
- `Skeleton.lean`: `monomialThreshold`/`monomialOrder` (:88/:94) + `monomialThreshold_ge_of_mult` (:134),
  `_le_axis` (:142), `_le_regularSeq` (:149); `balancedSplit_min` (:1602).
So rung-3's window-min should CITE `product_min_rlct` + the `monomialThreshold_*` family, not re-derive.
(Same re-derive-trap as the rank lemma; surfacing now so rs-grind checks the spine first.)
