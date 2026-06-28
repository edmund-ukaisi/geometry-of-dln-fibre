# KC1 Route-1 adjudication — pen-and-paper (obstruction seat, exact algebra, read-only, 2026-06-28)

**Question (controller's bedrock concern).** Before a ~250-LoC soundness-critical Lean build:
is genm-l2's **Route 1** (re-instantiate `block_elimination` with bases whose first `r` vectors
span `Im(Uᵀ)` / `Im(V)`) **sound** — does it make `top-r-rows(U)` invertible (KC1) for *every*
rank-`r` `B`?

**VERDICT: Route 1 as stated is INSUFFICIENT (obstruction certificate below). The fix is a
ROW-WLOG on `B` applied BEFORE `block_elimination`. KC2 is already discharged by the banked
colPerm seam. KC1 + KC2 decouple and hold simultaneously.**

All certificates are exact (sympy exact rationals / integers); the sweep (179/179) is corroboration,
the basis-independence argument is the proof. Scripts: `/tmp/kc1_adjudication.py`,
`/tmp/kc1_q2q3.py`, `/tmp/kc1_q2_wlog.py`, `/tmp/kc1_lean_convention.py`,
`/tmp/kc1_obstruction_b.py`, `/tmp/kc1_kc2_relation.py`, `/tmp/kc1_simul_wide.py`.

---

## The load-bearing identity (what `top-r-rows(U)` actually reads)

`block_elimination` (`Skeleton.lean:279`) gives invertible `P,Q` with `P·B·Q = corner =
[[I_r,0],[0,0]]`, so `B = P⁻¹·corner·Q⁻¹ = U·V` with `U = first-r-cols(P⁻¹)`, `V =
first-r-rows(Q⁻¹)`. In the Lean construction `P = bCod.toMatrix stdW`, so `P⁻¹ = stdW.toMatrix
bCod` has the basis vectors `bCod` as its columns; the **first `r` are `bRange`, a basis of
`range(f) = Im(B)`** (`Skeleton.lean:312,324,470`). Therefore:

> **The columns of `U` are a basis of `Im(B)` (the column space).** `top-r-rows(U)` is the leading
> `r×r` block — i.e. the basis vectors of `Im(B)` read in the **fixed first-`r` ambient row
> coordinates**.

Hence the exact characterization (the brief's iff, verified 6/6 on random rank-`r` `M`,
`kc1_obstruction_b.py`):

> `top-r-rows(U)` invertible  ⟺  `Im(B)` projects **isomorphically** onto the first-`r` ambient
> coordinates  ⟺  `Im(B) ∩ {x : x₀=…=x_{r−1}=0} = 0`.

This is a property of the **subspace `Im(B)` + the fixed coordinate choice**, NOT of the basis. The
load-bearing observation: re-choosing the `block_elimination` basis of `Im(B)` *rescales/recombines
the columns of `U`* but leaves `Im(B)` (and which ambient coords the leading block reads)
**unchanged** — so it cannot change whether the projection is an iso.

---

## Q1 — OBSTRUCTION CERTIFICATE (Route 1 fails)

**Witness (rank-1, 2×2):**

    B = [[0,0],
         [1,0]]          rank(B) = 1 = r.   Im(B) = span{(0,1)}.

`Im(B) = span{(0,1)}`. Every basis of a 1-dim space is a nonzero scalar multiple of `(0,1)`; its
first coordinate is `0`. So for **every** choice of `block_elimination` basis,
`top-r-rows(U) = [0]`, **singular** (checked at scales `3/7, 5, −11/2`: all det `0`,
`kc1_adjudication.py`). Equivalently `Im(B) ∩ {x₀=0} = Im(B) ≠ 0` — the projection is not an iso.

**Conclusion Q1.** There IS a rank-`r` `B` for which NO `block_elimination` basis makes
`top-r-rows(U)` invertible. **Route 1 (basis selection alone) is INSUFFICIENT.** The controller's
geometric worry is exactly correct: choosing a basis "spanning `Im`" does not change which ambient
coordinates the leading minor reads, and obstruction (b) blocks a post-hoc coordinate permutation.

This matches the pre-existing `a11_check.py` finding (`U=[[0],[1]]`, top block `0`) cited in
`l2-frontier-scope.md:104–108`.

---

## Q2 — the ROW-WLOG fix, and its validity

**The fix.** Permute the **rows** of `B` (`B ↦ R·B`, `R` a permutation matrix on the `H 0` rows)
so that `R·Im(B)` projects isomorphically onto the first-`r` coordinates. This is **always
possible**: `Im(B)` is `r`-dimensional, so a basis matrix of it is `a×r` of rank `r`, hence has
`r` independent **rows**; permute those to the top. On the Q1 witness, swapping the two rows gives
`R·B = [[1,0],[0,0]] = corner`, and `top-r-rows(U) = [1]` invertible (`kc1_q2q3.py`,
`kc1_obstruction_b.py`).

**Is row-permutation a valid RLCT-WLOG?** YES — it is the exact **dual** of the banked
`rlct_infimum_colPerm_eq`. Lean's `prod` (`Foundations/Loss.lean:33,48`) is
`prodAux(k+1) = prodAux(k) · A_k`, i.e. `prod = A_0·A_1·…·A_{L-1}`, shape
`(Fin (H 0)) × (Fin (H (last L)))`. So:

| WLOG | acts on | absorb into | identity (exact, verified) |
|------|---------|-------------|----------------------------|
| **col** (banked) | `B`'s columns = `H(last L)` = output | **last** layer `A_{L−1}` by RIGHT-mult | `prod(τ_C A) = prod(A)·C` |
| **row** (the fix) | `B`'s rows = `H 0` = input | **first** layer `A_0` by LEFT-mult | `prod(ρ_R A) = R·prod(A)` |

(`kc1_lean_convention.py`: both identities exact `True`.) Then
`‖prod(ρ_R A) − R·B‖² = ‖R·(prod A − B)‖² = ‖prod A − B‖²` since `R` permutes rows
(Frobenius-invariant; loss equal `3266 = 3266`, `kc1_q2_wlog.py`). `R` is a permutation
(orthogonal) matrix, so `ρ_R` — a coordinate permutation of the first layer's entries — is
**measure-preserving**, exactly as `paramColPermLast` is. The new lemma
`rlct_infimum_rowPerm_eq` is provable by the **same proof skeleton** as the banked
`FrontPivotWLOG` (swap "right-mult last-layer columns" → "left-mult first-layer rows"). **No such
`rowPerm` lemma exists in Lean today** (grep: only the colPerm family is banked) — this is the new
machinery KC1 requires.

**Obstruction (b) does NOT interfere.** (b) blocks a *post-hoc* row permutation on `(P,Q)` for a
**fixed** `B` (the corner-commutant is block-diagonal `r|(a−r)`; a row-swap on `P` sends `corner`'s
leading block down and no right-`Q` can lift it, `kc1_obstruction_b.py`). The row-WLOG instead
changes `B` to `R·B` **before** running `block_elimination` — `block_elimination` is re-run from
scratch on a *different matrix* with col-space `R·Im(B)`, producing fresh `(P_R,Q_R)`. (b) is about
the stabiliser of one fixed corner-factorisation; it says nothing about re-running the elimination
on a permuted target. Verified: on `R·B` the fresh `P_R=Q_R=I` gives `top-r-rows(U_R)=1`
invertible, (b) untriggered.

---

## Q3 — KC1 and KC2 decouple (achievable simultaneously)

- **KC1** (`top-r-rows(U)` inv) reads `Im(B)` against the first-`r` **row** coords → controlled by
  the **row**-WLOG `R`.
- **KC2** (`front-r-cols(V)` inv) reads `RowSp(B)` against the first-`r` **column** coords →
  controlled by the **col**-WLOG `Π`.

These act on **disjoint index sets** (rows vs columns) and commute on the relevant data:
- `Im(R·B·Π) = R·Im(B·Π) = R·Im(B)` (right-mult by invertible `Π` fixes the column space) — so the
  col-WLOG does not disturb KC1.
- column-independence of `B` is preserved by left-mult by invertible `R` — so the row-WLOG does not
  disturb KC2.

**Verified: 179/179** random deficient `B = X·Yᵀ` across rectangular shapes (`a,b ∈ 2..5`) and all
ranks `1..min(a,b)`: after `R` then `Π`, **both** KC1 and KC2 hold simultaneously
(`kc1_simul_wide.py`). They **DECOUPLE**.

---

## KC2 is ALREADY discharged by the banked colPerm seam (no new machinery)

`KC2` (`front-r-cols(V)` invertible)  ⟺  `B`'s **first `r` columns are independent** (verified
5/5 across shapes, `kc1_kc2_relation.py`). That is *exactly* what the banked
`front_pivot_perm_exists` (`FrontPivotWLOG` Lemma 1) guarantees: it produces a col-perm `Π` bringing
`r` independent columns of `B` to the front, with the first `r` columns at rank `r`. The downstream
`rlct_infimum_colPerm_eq` then carries the RLCT. **So KC2 needs nothing new — the asymmetry is real:
the column side is banked, the ROW side (KC1) is the missing dual.**

---

## Q4 — VERDICT + corrected sufficient construction

**Route 1 (basis selection alone): INSUFFICIENT** for KC1. The corrected, sufficient construction:

1. **Row-WLOG (NEW, the fix).** Front the rows: find `R` (permutation on `H 0`) bringing `r`
   independent rows of an `Im(B)`-basis to the top, equivalently making `R·Im(B)` project iso onto
   the first-`r` coords (always exists, `Im(B)` is `r`-dim). Discharge via a NEW
   `rlct_infimum_rowPerm_eq` — the exact dual of the banked colPerm: absorb `R` by **left-multiplying
   the FIRST layer `A_0`**; measure-preserving (permutation), loss-exact (`prod(ρ_R A)=R·prod(A)`).
2. **Col-WLOG (banked).** Front the columns via `front_pivot_perm_exists` + `rlct_infimum_colPerm_eq`
   — this already gives KC2 (first `r` columns independent ⟺ `front-r-cols(V)` invertible).
3. **Then `block_elimination` on `R·B·Π`** produces `(P,Q)` whose `U = first-r-cols(P⁻¹)` has
   `top-r-rows(U)` invertible (KC1) and whose `V = first-r-rows(Q⁻¹)` has `front-r-cols(V)`
   invertible (KC2). Both hold because `R` and `Π` control disjoint, decoupled data (Q3).

Note for the formaliser: it is cleaner to do step 1 with `R` chosen to **directly** front the
`Im(B)` coordinates (not "span a basis"), since basis-spanning is the part Q1 shows is vacuous. The
"invertible-leading-block" then follows from the projection being an iso, via the banked triangular
normalizers `RankNormalFormTriangular.{blockLower_left_normalizer, blockUpper_right_normalizer}`
which require exactly `[Invertible A11]`.

---

## What is most likely to break this / open part

- **The `rlct_infimum_rowPerm_eq` proof is not yet in Lean.** I assert it follows from the banked
  `FrontPivotWLOG` skeleton by the row/column mirror, and verified the two product identities + loss
  invariance + MP-by-permutation exactly. The only genuine Lean risk is plumbing: `paramColPermLast`
  updates the **last** layer via `Function.update`; the row dual updates the **first** layer
  (`A 0`), so the `volume_preserving_pi` / `piCongrLeft` argument re-targets index `0` instead of
  `last`. Mechanically symmetric; no new math. **Recommend the formaliser builds
  `rlct_infimum_rowPerm_eq` as a sibling module to `FrontPivotWLOG` before wiring KC1.**
- **WLOG-placement (kill-condition 3 in `l2-frontier-scope.md`).** The seam sits at the `⨅`-over-
  `optimalSet` level (like the banked colPerm), NOT at `Nonempty (DeepestGaugeChart …)`. Compose
  row-WLOG then col-WLOG at the headline `⨅`: `⨅ B = ⨅ R·B = ⨅ R·B·Π` with both fronts achieved.
- **Next construction that would settle it:** the formaliser stating `rlct_infimum_rowPerm_eq`
  mirroring `FrontPivotWLOG` Lemmas 2–4 with `A 0` / left-mult, and `#print axioms`-gating it
  axiom-clean. The math here is settled.

---

## Decorrelated Codex check (high effort, hypothesis withheld) — AGREES on all four

Fired independently (`/tmp/codex_kc1_prompt.md` → `/tmp/codex_kc1_answer.md`); frame + facts in,
my conclusion withheld. Codex reaches the **identical verdict** through partly different reasoning:

- **Q1 INSUFFICIENT** — Codex's witness is the even-smaller `B = [0; 1]` (2×1, `r=1`): the single
  basis column of `Col(B)=span(e₂)` is `(0,t)ᵀ`, leading block `[0]` singular for every `t≠0`.
  Same basis-independence mechanism. (Both witnesses are minimal in their shape class.)
- **Q2 row-WLOG valid** — Codex independently names the SAME reparametrization (`A_0 ↦ R·A_0`,
  left-mult first layer; Jacobian `|det|=1` ⟹ measure-preserving; `prod(A')=R·prod(A)`,
  loss-exact). It adds a **cleaner sufficiency proof** worth handing the formaliser: once
  `top-r-rows(B') = top-r-rows(U)·V` has rank `r` and `V` is full row-rank, `top-r-rows(U)` *must*
  be invertible — a one-line rank argument that bypasses reasoning about the `Im`-basis entirely.
- **Q3 decoupled** — same commuting-rank identities (`top_r_rows(R·B·C)=top_r_rows(R·B)·C`, etc.),
  same combined parameter change.
- **Q4 INSUFFICIENT + identical corrected recipe** (`R` left on `A_0`, `C` right on `A_{L-1}`, run
  `block_elimination` on `R·B·C`).

**One place my finding is STRONGER than Codex's.** Codex treats KC2's column side as needing a fresh
col-WLOG `C`; it did not know the col side is **already banked** (`front_pivot_perm_exists` +
`rlct_infimum_colPerm_eq`). Net: the corrected construction needs exactly ONE new piece — the row
dual `rlct_infimum_rowPerm_eq` — not two. (Fact, not inference: the colPerm family is in
`FrontPivotWLOG.lean`; no rowPerm lemma exists, by grep.)
