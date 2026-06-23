# C1↔C5 datum-unification — adjudication CERT (pen-and-paper, decorrelated)

Adjudicates the residual seam #97 left (surfaced in #133): **does ONE
`IsSchurStraightenSqueeze`-shaped datum cover BOTH the hard-pivot C1 residual squeeze AND the C5
smooth-shear regular-½ resolution, or are two datum shapes forced?** Unblocks G-a (#135) by pinning the
datum shape the general-M `hnode` producer must supply.

Exact algebra (sympy over ℝ-symbols; no float). Decl-grounded against the committed
`IsSchurStraightenSqueeze` (`GeneralR1Recursion.lean:406`) + the #97 C5 witness
(`c5-hnode-probe-CERT.md`, `c5_*.py`).

## Verdict (one line)

**ONE datum suffices. `IsSchurStraightenSqueeze` covers both C1 and C5 — the difference is FIELD VALUES
(where the defect sits + the squeeze constants), NOT structure (the fields are identical).** The C5
rank-1 defect, after the smooth shear, is one regular generator in the `nReg` block; the C1 defect is a
bounded pivot perturbation `b·E`. Both land in the SAME squeeze `c₁·Φ ≤ flatCore ≤ c₂·Φ` with
`Φ = (∑_{j<nReg} w.1_j²) + G²`. No structural fork. The general-M `hnode` producer supplies ONE datum
type; per node it chooses the defect's placement (regular block vs bounded perturbation) — a producer
decision, not a type decision.

No kill-condition. One transcription note for the formaliser (the `nReg` count varies per node — below).

## The datum (decl-grounded, `GeneralR1Recursion.lean:406`)

`IsSchurStraightenSqueeze M S flatCore G redEmbed c₁ c₂` fields:
- `flatCore : (Fin nReg → ℝ) × Y → ℝ`, `G : Y → ℝ`, `redCore_eq : G² = dlnLoss S.red 0 ∘ redEmbed`;
- `c₁pos : 0 < c₁`, `c₂pos : 0 < c₂`;
- `squeeze : near (0,0), 0 ≤ Φ ∧ c₁·Φ ≤ flatCore ∧ flatCore ≤ c₂·Φ`, `Φ = smoothBlockSplitForm G w =
  (∑_{j} (w.1 j)²) + G(w.2)²` — `nReg` literal regular coordinate-squares + the single reduced core `G²`;
- `Gne`, `measure_drops`.

Consequence (PROVEN, `schur_straighten_squeeze_of_data`): `rlct flatCore (0,0) = nReg/2 + rlct(G²) 0`.

## C1 — the hard-pivot node IS the datum, verbatim (FACT)

`flatCore = (∑_j E_j²) + ∑_{i,j} (b_i·E_j + SΓ_{ij})²`, pivot `b` bounded (`∑b² ≤ T²`, `b→0` deepest).
Field assignment: `nReg = #E` (regular block `∑E_j²`), `G² = ∑SΓ²` (the reduced survivor core), squeeze
constants `c₁ = (2(1+T²))⁻¹`, `c₂ = 2+2T²` from `squeeze_bounds_abstract` (PROVEN,
`GeneralR1Recursion.lean`). The defect lives in the PERTURBATION `b·E`, not in `nReg`. This is exactly
`schur_node_squeeze_unif` — the existing `schur_straighten_squeeze_exists` consumes it.

## C5 — the partial-drop node fits the SAME datum after the shear (exact, `pp_c1c5_datum.py`)

C5 node loss (the #97 model): `loss = ∑‖G·p‖²(survivor) + ‖G·q + δ·e‖²(rank-1 complement)`, `e` a
bounded nonzero gauge. The smooth shear `δ' = δ + (G·q·e)/‖e‖²` gives EXACTLY (sympy `loss − split = 0`):

    loss = ‖e‖²·δ'²  +  [‖G·p‖² + ‖G·q‖² − (G·q·e)²/‖e‖²]   (the survivor core projected off e)

So the defect becomes ONE regular square `‖e‖²·δ'²` (a Morse ½) and the bracket is the reduced survivor
core `G²`. Field assignment: `nReg` INCLUDES the `δ'`-generator (alongside the survivor's full-rank
regular part), `G²` = the projected survivor core. **Fits the datum's `Φ = (∑reg²) + G²` shape.**

## The two "too clean" guards I ran (the role's diligence)

### Guard 1 — RLCT accounting: is the C5 defect a regular ½, or a separate monomial-lane exceptional?

(`pp_c1c5_rlct_accounting.py`.) The danger: if the hard-pivot route routes `δ` through the monomial/cover
lane (an exceptional `x_p` with a different threshold), the datum's `nReg/2` would MISCOUNT it. Exact
2-variable local model near the deepest point `loss(δ,φ) = ‖e‖²δ² + φ² + 2c·δφ` (`φ` = survivor proxy,
`c` = e-coupling): the shear `δ' = δ + (c/‖e‖²)φ` diagonalises to `‖e‖²δ'² + (1 − c²/‖e‖²)φ²`, a
NONDEGENERATE quadratic iff `det Gram = ‖e‖² − c² > 0` — exactly the `‖e‖²≠0` chart condition #97 §3
established holds per `pivotBlowupOn` chart. So the defect's share is a clean ½ in BOTH readings, SAME
value, NO monomial-lane discrepancy. The datum's `nReg/2 + rlct(G²)` counts it correctly.

(Note: #97 already caught the related confound — a FIXED-`δ` bounded-pivot reading passes `0/3000` but
blows up as `Φ→0` because the cross term `2δ(G·q·e)` is `√Φ`-scale. The shear is what removes that cross
term; the naive hard-pivot squeeze is not uniform near the deepest point without it. The corrected
mechanism — shear, or blow-up-then-normalise-`e` — is what fits the datum.)

### Guard 2 — does `‖e‖` need to be CONSTANT for a uniform squeeze? (the Q4 obstruction)

(`pp_c1c5_datum.py` + the inline Q4 check.) `‖e‖²` varies over the chart in `[c, C]` (`0 < c ≤ C`). With
the UNWEIGHTED regular square `δ'²` in `Φ` (`Φ = δ'² + core`, `loss = ‖e‖²δ'² + core`):
`c₁ = min(c,1) > 0`, `c₂ = max(C,1)` give `c₁·Φ ≤ loss ≤ c₂·Φ` (verified: lower slack `(c−min(c,1))δ'² +
(1−min(c,1))core ≥ 0`; upper symmetric). **No requirement that `‖e‖` be constant** — the bounded gauge
`‖e‖∈[√c,√C]` plays exactly the `c₁,c₂>0` unit role the datum already allows, the same mechanism as the
C1 bounded pivot `b→0` giving `c₁=(2(1+T²))⁻¹`, `c₂=2+2T²`. So the squeeze field absorbs the varying
gauge with no structural change.

## The decision (Q3): FIELD VALUES, not STRUCTURE

- C1 and C5 differ ONLY in: (a) where the defect sits — C1 in the bounded perturbation `b·E`, C5 in the
  regular block `nReg` after the shear; (b) the squeeze constants — C1 `(2(1+T²))⁻¹ / 2+2T²`, C5
  `min(c,1) / max(C,1)`. Both are FIELD VALUES of `IsSchurStraightenSqueeze`. The structure's fields
  (`flatCore`, `G`, `c₁`, `c₂`, `squeeze`, `redCore_eq`, `Gne`, `measure_drops`) are IDENTICAL.
- The shear route (C5) is in fact the `b=0` LIMIT of the hard-pivot squeeze: at `b=0` the perturbation
  vanishes and `F = Φ` exactly (sympy `F − Φ = 0` at `b=0`, `pp_c1c5_datum.py`). The C5 defect, after the
  shear decouples it, has NO bilinear perturbation — it is a pure regular generator. So C5 is not a new
  datum; it is the SAME datum with the perturbation set to zero and the freed coordinate counted in `nReg`.

⟹ **ONE datum.** Two shapes are NOT forced.

## Transcription note for the formaliser (the one real subtlety)

`nReg` (the regular-square count) is NOT the same constant at C1 and C5 nodes:
- C1 (pure pivot): `nReg = #E` (the pivot-row generators); the defect is in the perturbation.
- C5 (partial drop): `nReg = #E + 1` (the pivot-row generators PLUS the freed `δ'`-generator); the
  survivor core is `G²`.

The datum already carries `nReg` as a parameter (`{nReg : ℕ}`), so this is a per-node value, not a type
change — the producer sets `nReg` from the node's rank-drop profile. The codim bookkeeping matches: a
rank-1 partial drop adds ONE regular ½, exactly the `Mval` increment for that step (#97 §4). The
multi-drop (rank `a−b > 1`) iterates `a−b` rank-1 C5 nodes (pp2 g224/g225; `schurState` drops 1 per pivot
per step), each contributing one ½ via the SAME datum — so "one datum" survives the multi-drop by
iteration (one `ChainDimSplit` step per rank-1 peel), NOT by a multi-dimensional exceptional.

## Recommended datum spec for G-a (#135)

The general-M `hnode` producer supplies, per node, ONE `IsSchurStraightenSqueeze M S flatCore G redEmbed
c₁ c₂` with:
- `flatCore` = the node's post-blow-up residual core (the `‖Â·A2‖²` Schur form);
- `nReg` = (# pivot-row generators) + (# rank-1 defects freed at this node) — from the rank-drop profile;
- `G²` = `dlnLoss S.red 0` via `redEmbed`, `S.red = schurState M` (the survivor reduced chain);
- `c₁, c₂` = the bounded-perturbation / bounded-gauge constants (`squeeze_bounds_abstract` for the C1
  part; `min(c,1)/max(C,1)` for the C5 freed generator — both `>0`);
- `squeeze` = `schur_node_squeeze_unif` (C1 part) composed with the shear-diagonalised regular ½ (C5 part).

The shear (`δ' = δ + (G·q·e)/‖e‖²`) is the producer's coordinate move; it is `measurePreserving` (det-1),
matching the existing `measurePreserving_coreShear` idiom (`RouteMState`/S1-Fubini). NO new datum type.

## Decorrelation note (fresh codex consult — captured, agrees on every point)

My three exact-algebra scripts (`pp_c1c5_datum.py`, `pp_c1c5_rlct_accounting.py`, the inline Q4 check) all
converge on ONE-datum. A fresh hypothesis-withheld `codex exec` consult (xhigh, via the
`local-codex-consult` skill with `--output-last-message`, captured at
`codex/codex_c1c5_answer_captured.md`) independently confirms the verdict on all four questions:

- **Q1** C1 IS a `Datum` instance — same field assignments (`nReg=#E`, `c₁=(2(1+T²))⁻¹`, `c₂=2+2T²`);
  "the defect is not counted in `nReg`; it is controlled as a bounded linear perturbation."
- **Q2** C5 after the shear `loss = ‖e‖²δ'² + G²` fits via the rescaled coordinate `x=‖e‖δ'`:
  `loss = x² + G² = Φ`, `c₁=c₂=1`. "The C5 defect has become an actual Morse square, so it belongs in
  the regular block."
- **Q3 [the decision]** "ONE `Datum` structure covers both C1 and C5. The difference is a difference of
  FIELD VALUES and producer proofs, NOT of structure." Codex independently proposes the two-constructor
  pattern `Datum.ofHardPivot` / `Datum.ofPartialDropShear` returning the SAME `Datum` type — sharpening
  "producer decision, not type decision" into a concrete API hint for G-a.
- **Q4** `‖e‖` need NOT be constant: `c₁=min(c²,1)`, `c₂=max(C²,1)` for `0<c≤‖e‖≤C` (the same result as my
  `min(c,1)/max(C,1)` under the `‖e‖` vs `‖e‖²` renaming), and codex independently names the ONLY real
  obstruction — "loss of a uniform nonzero bound: if `‖e‖` can approach 0 or blow up" — exactly the
  `‖e‖²≠0` per-chart condition #97 §3 established holds.

Decorrelation is genuine and properly captured (the earlier `codex exec` runs this session omitted
`--output-last-message`, hence the thin captures; the skill's invocation fixes it). #97's PRIOR completed
Codex consult (`c5-hnode-probe-CERT.md` codex/) — that the C5 hard-pivot route "reuses the EXISTING
`schur_straighten_squeeze_exists` `hnode` verbatim" (Codex Q1/Q2 FACT) — is a third, agreeing read. No
disagreement across all three.

## Scripts (this dir) — exact, re-runnable

- `pp_c1c5_datum.py` — the shear split (exact `loss − split = 0`), the hard-pivot `b=0` limit (`F−Φ=0`),
  the datum-fit for both presentations.
- `pp_c1c5_rlct_accounting.py` — the 2-var local model + Gram-det nondegeneracy (the regular-½ accounting,
  no monomial-lane discrepancy).
- `codex/codex_c1c5_prompt.md` + `codex/codex_c1c5_answer_captured.md` — the decorrelated consult
  (hypothesis-withheld; captured via `--output-last-message`, agrees on all four questions).
