   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading additional input from stdin...
OpenAI Codex v0.142.4
--------
workdir: /home/ubuntu/workspace/genm-r1lower-wt
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019f1a55-4402-71a2-86da-5eeb1cbb5c05
--------
user
# Codex consult: Lean 4 match-reduction decode (the genm-ambdet thrash-point)

Lean 4 + Mathlib v4.29. I'm proving `leafH_diagAxis`. After `rw [interiorLive_leafH, if_neg …, diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]` the goal is (verified):

```
⊢ (match
      (frameSplitEquiv M (tach M) (0 + 1) ⋯ ⋯)
        ((frameSplitEquiv M (tach M) (0 + 1) ⋯ ⋯).symm (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, i)))))) with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      if (finProdFinEquiv.symm qK).1 = (finProdFinEquiv.symm qK).2 then
        Text M (tach M) (0 + 1) - Text M (tach M) (0 + 2) + (Wext M (0 + 1) - Text M (tach M) (0 + 2)) +
          2 * (Text M (tach M) (0 + 2) - 1 - ↑(finProdFinEquiv.symm qK).1)
      else 0
    | x => 0)
  = Text M (tach M) 1 - Text M (tach M) 2 + (Wext M 1 - Text M (tach M) 2) + 2 * (Text M (tach M) 2 - 1 - ↑i)
```

The `⋯ ⋯` are proof args `(ha.hdesc 0 _) (ha.hub 0)`. `frameSplitEquiv … k …` is an `Equiv` (a `_ ≃ _`). The scrutinee is `e (e.symm X)` with `X = Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, i))))`.

WHAT FAILS:
- `simp only [Equiv.apply_symm_apply]` — does NOT reduce the scrutinee (goal unchanged; match stays).
- `rw [Equiv.apply_symm_apply (frameSplitEquiv M (tach M) (0+1) (ha.hdesc 0 (by norm_num)) (ha.hub 0))]` — "did not find pattern".
- `have hround : e (e.symm X) = X := Equiv.apply_symm_apply _ _; rw [hround]` — hround typechecks but `rw [hround]` "did not find pattern".

The blocker (genm-ambdet's note): the match-discriminant `(0:Fin 2).val + 1` (from `diagAxis`, where `frameSplitEquiv` is applied at literal `(0:Fin 2).val+1`) vs `k.val + 1` (in `liveLeafHOnIdx` after the outer `match ⟨k, Sum.inl s⟩` binds `k = ⟨0,_⟩`) — proof-irrelevant but syntactically distinct `frameSplitEquiv` instances (different `hdesc`/`hub` proof args, or `(0:Fin 2).val` vs `0`), so `rw` (syntactic) can't bridge and `simp [Equiv.apply_symm_apply]` won't fire on the coe form.

`frameSplitEquiv M t s hdesc hub : (Fin … ⊕ …) ⊕ … ≃ …` (a Mathlib `Equiv` built from `finCongr`/`Equiv.sumCongr` pieces). `finProdFinEquiv : Fin a × Fin b ≃ Fin (a*b)`.

QUESTION: what's the robust Lean 4 idiom to reduce `e (e.symm X)` → `X` inside a `match` scrutinee when `e` carries proof args that may not be syntactically identical to a hand-written copy? Options I'm considering: (a) `conv` to the scrutinee + `rw [Equiv.apply_symm_apply]` (does conv's `rw` tolerate the instance better?); (b) `simp only [Equiv.apply_symm_apply]` with `(config := …)`; (c) `generalize`/`set` the equiv as `e` first so the two occurrences unify, THEN `rw [Equiv.apply_symm_apply e]`; (d) `dsimp only [diagAxis, liveLeafHOnIdx]` to force defeq match-reduction before the round-trip; (e) prove via `Fin.cases`/`decide` on `i`? (i : Fin (Text 2), opaque width — decide won't work). Give the most likely-to-work idiom + a fallback. Concise.
codex
I’ll check the local definitions around `leafH_diagAxis`, `diagAxis`, and `liveLeafHOnIdx` so the advice matches the exact reducibility and notation in this repo.
exec
/bin/bash -lc "rg --files . | rg \"\\.lean"'$|CLAUDE'"\\.md|README\\.md\"" in /home/ubuntu/workspace/genm-r1lower-wt
2026-06-30T21:00:30.306915Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019f1a55-4402-71a2-86da-5eeb1cbb5c05`" }
 exited 1:
2026-06-30T21:00:30.307433Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc "rg --files . | rg \"\\.lean"'$|CLAUDE'"\\.md|README\\.md\""`: CreateProcess { message: "Rejected(\"rejected by user\")" }
exec
/bin/bash -lc 'rg -n "leafH_diagAxis|diagAxis|liveLeafHOnIdx|frameSplitEquiv|finProdFinEquiv" -S .' in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 204ms:
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/certificate-genM-witness-v2.md:107:The witness `wOnIdx` matches on the `frameSplitEquiv`/`liftSlotEquiv` role-slot outputs (round-trips
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/statement-cards.md:74:> - **Gloss.** `Fin (schurDim k) ≃ Fin t_k × Fin M_{k+1}` (and the lift analog) via `finProdFinEquiv`;
./expeditions/2026-06-20-aoyagi-full/threads/genm-h2a/statement-card.md:20:>   read `(i,j) = finProdFinEquiv.symm qK`, test `i = j`), and `0` on every other role / off-diagonal
./expeditions/2026-06-20-aoyagi-full/threads/genm-h2a/statement-card.md:24:>   reader `readK` addressing (same `chartIdxEquiv` + `frameSplitEquiv` + `finProdFinEquiv` route).
./expeditions/2026-06-20-aoyagi-full/threads/genm-h2a/statement-card.md:26:>   for `chartIdxEquiv` and `hdesc/hub` for `frameSplitEquiv`); `hN : 0 < routeMAmbient M`.
./expeditions/2026-06-20-aoyagi-full/threads/genm-h2a/codex/leafH-design-prompt.md:14:      `chartIdxEquiv.symm ⟨k, Sum.inl (frameSplitEquiv ... .symm (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i,i))))))⟩`.
./expeditions/2026-06-20-aoyagi-full/threads/22-r1-wedge-design/codex/l2-cov-route-prompt.md:19:The existing (2,2,2) work solved this by building an EXPLICIT measure-preserving enumeration `e222 : Params H222 ≃ᵐ (Fin 8 → ℝ)` (using `finProdFinEquiv` instead of the opaque `equivFin`) + an explicit core `myF222 : (Fin 8→ℝ)→ℝ` + a proven `dlnLoss = myF222 ∘ e222`. That spanned ~10 files (`Case222Algebra`, `ParamsFlat222`, `Case222Resolution`, ...). Replicating this for (3,3,4) is a multi-file subproject.
./expeditions/2026-06-20-aoyagi-full/threads/22-r1-wedge-design/codex/l2-cov-route-prompt.md:22:ROUTE 1 (explicit e334): replicate the (2,2,2) pattern — build `e334 : Params ![3,3,4] ≃ᵐ (Fin 21→ℝ)` explicitly (finProdFinEquiv-style), `myF334`, `dlnLoss = myF334 ∘ e334`, then the wedge + pivotBlowupOn COV + leaf atom on Fin 21. Honest but large.
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/deadleaf-vval-aepos-answer.md:11:Recommended path: prove the extra hypothesis “there exists a nonempty usable interior residual block,” then define a **single scalar `PolyHentry`** by the `Hmat` recursion and use `VvalGen ≥ (Hentry)^2` plus `ae_eval_ne_zero`. If that scalar route becomes cast-heavy, fall back to (ii) and define the full `PolyHmat`/`UPolyGen`. Biggest dependent-width risk: choosing and transporting the witness indices through `frameSplitEquiv`, `rmatPad`, `chainA`, `suffix`, and the `HrGen` reindex without losing definitional simplification.
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/brick-a-prompt.md:18:  `frameSplitEquiv` (K⊕X⊕N⊕E sub-split) + `finProdFinEquiv` (matrix index). `Bmat (k+1) = bmatStack(K,X)
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/structadm-achiever-gap-prompt.md:56:    `frameSplitEquiv M t (k.val+1) (ha.hdesc k.val) (ha.hub k.val)` with `k : Fin L`, I'd write
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:115:  `schurSlotEquiv`/`liftSlotEquiv` (`Fin (schurDim k) ≃ Fin t_k × Fin M_{k+1}` via `finProdFinEquiv`),
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:175:- **`frameSplitEquiv`** — the Schur-frame slot K/X/N/E sub-split (`Fin (Text s·Wext s) ≃ (((K⊕X)⊕N)⊕E)`
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:185:With `bmatStack` + `frameSplitEquiv` + the readers banked, the decoder assembly is:
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:186:1. Per interior `s` (1..L−1): read K/X/N/E matrices via `frameSplitEquiv` (slot `k=s−1`) +
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:187:   `finProdFinEquiv` (entry index) + `chartIdxEquiv.symm` + `x`. `Bmat s = bmatStack K X`; `Nblk s = N`;
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:211:`readSchur`/`readLift`, `bmatStack` (+ block laws), `frameSplitEquiv`, `rmatPad`.
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:216:`schurDim M (fun j => Text M t (j+1)) k = Text(k+1)·Wext(k+1)` by `rfl`, and `frameSplitEquiv M t (k+1)`
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/thread.md:226:- K/X/N/E readers: `frameSplitEquiv M t (k+1)`-inject the role index, `finProdFinEquiv` the (i,j),
./expeditions/2026-06-20-aoyagi-full/threads/36-genM-jacobian-det/codex/structadm-achiever-gap-answer.md:24:frameSplitEquiv M t (k.val + 1)
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/seam-elab-answer.md:36:  (((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2)).prodCongr
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/seam-elab-answer.md:38:      (finProdFinEquiv : Fin (2 * 2) × Fin 2 ≃ Fin ((2 * 2) * 2))).symm.trans
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/seam-elab-prompt.md:60:3. For the explicit `Fin 8 ≃ FlatIdx (fun _:Fin 3 => 2)`: cleanest construction (finProdFinEquiv chain?
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:6258:lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:354:`:= regPivotFinEquiv` (the TRANSPARENT `finProdFinEquiv`/`finSumFinEquiv` enumeration in
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:8745:`finProdFinEquiv`/`finSumFinEquiv`/`finCongr` enumeration replacing the opaque `Fintype.equivFin`.
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:8760:      (Equiv.sumCongr finProdFinEquiv.symm
./expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/frame-factor-target-answer.md:8762:          (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm))))
./expeditions/2026-06-18-voigt-discharge/threads/18-geom-route-general/codex/route-stdout.log:859:lean/.lake/packages/mathlib/Mathlib/Algebra/BrauerGroup/Defs.lean:77:    ⟨reindexAlgEquiv _ _ finProdFinEquiv |>.symm.trans <| compAlgEquiv _ _ _ _|>.symm.trans <|
./expeditions/2026-06-18-voigt-discharge/threads/18-geom-route-general/codex/route-stdout.log:862:lean/.lake/packages/mathlib/Mathlib/Algebra/BrauerGroup/Defs.lean:80:    iso2.mapMatrix.trans <| compAlgEquiv _ _ _ _|>.trans <| reindexAlgEquiv _ _ finProdFinEquiv⟩⟩

codex
The search found the relevant Lean file: `RouteMInteriorLDULeafH.lean`. I’m going to read the local definitions and nearby existing proofs; in this kind of goal, an adjacent proof often shows which normalization route Lean is already happy with.
exec
/bin/bash -lc "sed -n '1,180p' lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLDULeafH.lean" in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
import DLNFibre.DLN.RLCT.Validate.RouteMInteriorLDUContract

/-!
# `RouteMInteriorLDULeafH` — the multi-axis Jacobian exponent vector `lduleafH` (H2a, ∀M-L2)

The fs-INDEPENDENT sub-piece of the R1-LOWER LDU-lensed interior box-divergence: the multi-axis
Jacobian-exponent vector `lduleafH M ha hN : Fin (routeMAmbient M) → ℕ` of the LDU-lensed interior
achiever chart, plus its value at the binding pivot axis.

The exponent vector follows the per-factor determinant bookkeeping of the lensed chart
(`RouteMInteriorLDUContract` header):

* the **radial** blow-up `pivotBlowupOn` contributes `|u_p|^{minAdm−1}` at the pivot axis
  `p = structPivot M hN = ⟨0,_⟩`;
* per Schur boundary `s` (= `k+1`, `k : Fin L`), the lensed K-core diagonal pivot `q_{s,i}` carries
  the **Schur frame** exponent `r_s + c_s` (`schurFrameDeriv_det` gives `|det K|^{r+c}` and the LDU
  lens makes `det K = ∏_i q_i`, banked `kLens_det`) PLUS the **LDU core** exponent `2·(t_s − 1 − i)`
  (`lduCoreDeriv_det` gives `∏_i |q_i|^{2(t−1−i)}`), i.e. `(r_s + c_s) + 2·(t_s − 1 − i)` at the
  K-diagonal flat slot `(s, q_{s,i})`;
* every other (spectator) flat axis carries `0`.

Here the boundary-`s` widths (frame boundary `s = k+1`, `k : Fin L`) are
`t_s = Text M (tach M) (k+2)` (the K-core size),
`r_s = Text M (tach M) (k+1) − Text M (tach M) (k+2)` (the residual rows),
`c_s = Wext M (k+1) − Text M (tach M) (k+2)` (the residual columns) — exactly the `frameSplitEquiv`
role widths.

The construction mirrors the banked interior witness `wOnIdx`/`wInt`
(`RouteMAchieverWitnessInterior`): a `ChartIdx`-indexed placement `lduleafHOnIdx` (K-branch diagonal
entry → the exponent, else `0`) composed with the chart bijection `chartIdxEquiv`, with the pivot
axis OVERRIDDEN to the radial value `minAdm − 1`. The override-at-pivot keeps the radial bookkeeping
separate from the K bookkeeping (the radial axis is read directly as `x ⟨0⟩`, not through
`chartIdxEquiv`), and makes the pivot value `if_pos rfl`.

This file is fs-INDEPENDENT (it never touches the factor list `fs` / `interiorLDU_factors`): it
supplies the two named atoms `lduleafH` and `lduleafH_pivot` that `RouteMInteriorLDUContract`'s
`interiorLDU_leafH` / `interiorLDU_leafH_pivot` are wired to (one-liner
`interiorLDU_leafH := lduleafH`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` target (finite equivalences + ℕ arithmetic; no
analysis). The exponent values are pinned to the per-factor dets by the SEPARATE det-bookkeeping
atom (`ldu_det_bookkeeping`, H2b — not in this file).
-/

namespace DLNFibre.DLN.RLCT

open scoped BigOperators

variable {L : ℕ}

/-! ## The `ChartIdx`-indexed K-diagonal exponent placement -/

/-- **The `ChartIdx`-indexed exponent placement** for the LDU-lensed interior chart. At a frame slot
(`Sum.inl s`), boundary `k : Fin L`, the K-role branch (`Sum.inl (Sum.inl (Sum.inl qK))`) decodes
the matrix index `(i,j) = finProdFinEquiv.symm qK`; on the diagonal `i = j` it returns the per-pivot
exponent `(r_s + c_s) + 2·(t_s − 1 − i)` — the Schur frame `r_s+c_s` (`|det K|^{r+c}`) plus the LDU
core `2(t_s−1−i)` (`∏_i |q_i|^{2(t−1−i)}`) — at boundary `s = k+1` with widths
`t_s = Text M (tach M) (k+2)`, `r_s = Text M (tach M) (k+1) − Text M (tach M) (k+2)`,
`c_s = Wext M (k+1) − Text M (tach M) (k+2)`. Every off-diagonal K entry, the X/N/E roles, and the
lift slot carry `0`. (Mirrors the banked witness `wOnIdx`.) -/
noncomputable def lduleafHOnIdx (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M)) :
    ChartIdx M (tDesc M (tach M)) → ℕ := fun q =>
  match q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>  -- K role
      let ij := finProdFinEquiv.symm qK
      if ij.1 = ij.2 then
        (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))   -- r_s
          + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))         -- c_s
          + 2 * (Text M (tach M) (k.val + 2) - 1 - ij.1.val)           -- 2·(t_s − 1 − i)
      else 0
    | _ => 0  -- X, N, E roles
  | ⟨_, Sum.inr _⟩ => 0  -- lift slot

/-! ## The flat-coordinate exponent vector `lduleafH` -/

/-- **H2a — the multi-axis Jacobian exponent vector** for the LDU-lensed interior chart:
`lduleafH = radial(minAdm−1) at the pivot ⊕ per-boundary[(r_s+c_s) + 2(t_s−1−i)]` on the lensed
K-diagonal flat slots, `0` on spectator axes. The pivot axis `p = structPivot M hN = ⟨0,_⟩` is
overridden to the radial blow-up exponent `minAdm M − 1` (the radial axis is read directly as
`x ⟨0⟩`, not through `chartIdxEquiv`); every non-pivot axis takes the `ChartIdx`-placed K-diagonal
exponent `lduleafHOnIdx`.

(Validated at `(3,3,3,3)`: `|u0|⁵·|u1|⁴·|u4|²·|u9|³` — radial `5 = minAdm−1` at axis `0`; the
`2×2`-core boundary `r+c = 2 → {4, 2}` at the two diagonal pivots; the `1×1`-core boundary
`r+c = 3 → {3}`.) -/
noncomputable def lduleafH (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) : Fin (routeMAmbient M) → ℕ := fun j =>
  if j = structPivot M hN then
    minAdm M - 1
  else
    lduleafHOnIdx M ha (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j)

/-- **H2a — the binding axis carries `minAdm−1`** (the radial blow-up exponent at the pivot). The
pivot override is `if_pos rfl` — `lduleafH M ha hN (structPivot M hN) = minAdm M − 1`. -/
theorem lduleafH_pivot (M : Fin (L + 1) → ℕ) (ha : StructAdm M (tach M))
    (hN : 0 < routeMAmbient M) :
    lduleafH M ha hN (structPivot M hN) = minAdm M - 1 := by
  rw [lduleafH, if_pos rfl]

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '150,230p' lean/DLNFibre/DLN/RLCT/Validate/RouteMChartSlots.lean" in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
  simp only [Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Equiv.refl_symm,
    Equiv.refl_apply, Matrix.of_apply]
  rw [show (Fin.cast (show Text M t k = Text M t (k + 1) + (Text M t k - Text M t (k + 1)) by omega)
        (Fin.cast (show Text M t (k + 1) + (Text M t k - Text M t (k + 1)) = Text M t k by omega)
          (Fin.natAdd _ b)))
        = Fin.natAdd (Text M t (k + 1)) b from by apply Fin.ext; simp,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-! ## The Schur-frame slot K/X/N/E sub-split

The frame slot at GenBlk boundary `s` (size `Text s · Wext s`) sub-splits into the Schur roles
`K` (`Text(s+1)²`), `X` (`r_s·Text(s+1)`), `N` (`Text(s+1)·c_s`), `E` (`r_s·c_s`), where
`r_s = Text s − Text(s+1)`, `c_s = Wext s − Text(s+1)`. The `(((K + X) + N) + E) = Text s · Wext s`
identity is the banked `roleSquare_eq`; the split equiv nests `finSumFinEquiv.symm` left-to-right. -/

/-- **The Schur-frame slot K/X/N/E sub-split equivalence** — `Fin (Text s · Wext s) ≃ (((K ⊕ X) ⊕ N)
⊕ E)` at the role-block sizes, via `roleSquare_eq` + left-nested `finSumFinEquiv.symm`. The decoder's
per-frame role accessor base (`K`, `X`, `N`, `E` blocks of the Schur frame at boundary `s`). -/
def frameSplitEquiv {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s) :
    Fin (Text M t s * Wext M s) ≃
      (((Fin (Text M t (s + 1) * Text M t (s + 1)) ⊕
         Fin ((Text M t s - Text M t (s + 1)) * Text M t (s + 1))) ⊕
        Fin (Text M t (s + 1) * (Wext M s - Text M t (s + 1)))) ⊕
       Fin ((Text M t s - Text M t (s + 1)) * (Wext M s - Text M t (s + 1)))) :=
  (finCongr (roleSquare_eq h1 h2).symm).trans
    ((finSumFinEquiv.symm).trans
      (((finSumFinEquiv.symm).trans
        (((finSumFinEquiv.symm).trans (Equiv.refl _)).sumCongr (Equiv.refl _))).sumCongr
          (Equiv.refl _)))

/-! ## The derived `Rmat` block-pad constructor (the Schur-frame `u`-carrier `[[0,0],[0,E]]`)

The structured decoder's `Rmat s` is the `u`-carrying residual of the Schur frame: the `E_s`
(`r_s × c_s`) block placed BOTTOM-RIGHT of a `Text s × Wext s` zero matrix, so
`C_s = Bmat_s·chainQ(N_s) + u·Rmat_s = [[K, KN],[XK, XKN + uE]]` (the Schur frame). A
`Matrix.fromBlocks 0 0 0 E` padded by `finSumFinEquiv` row/col reindexes. -/

/-- **The Schur-frame `u`-carrier block** `Rmat s = [[0,0],[0,E]]` (`Text s × Wext s`), the `E_s` block
(`r_s × c_s`) in the bottom-right, zeros elsewhere (`Matrix.fromBlocks 0 0 0 E` + `finSumFinEquiv`
row/col reindex to `Text s × Wext s`). -/
noncomputable def rmatPad {L : ℕ} (M : Fin (L + 1) → ℕ) (t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 : Text M t (s + 1) ≤ Text M t s) (h2 : Text M t (s + 1) ≤ Wext M s)
    (E : Matrix (Fin (Text M t s - Text M t (s + 1))) (Fin (Wext M s - Text M t (s + 1))) 𝕜) :
    Matrix (Fin (Text M t s)) (Fin (Wext M s)) 𝕜 :=
  Matrix.reindex
    (finSumFinEquiv.trans
      (finCongr (show Text M t (s + 1) + (Text M t s - Text M t (s + 1)) = Text M t s by omega)))
    (finSumFinEquiv.trans
      (finCongr (show Text M t (s + 1) + (Wext M s - Text M t (s + 1)) = Wext M s by omega)))
    (Matrix.fromBlocks (0 : Matrix (Fin (Text M t (s + 1))) (Fin (Text M t (s + 1))) 𝕜) 0 0 E)

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '430,475p' lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean" in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
              (Sum.inl (Sum.inl (Sum.inl a)))) = Sum.inl (Sum.inl (Sum.inl a))),
      (hasFDerivAt_kLDU_out_K M t ha k _ _ y).fderiv]
    simp only [ContinuousLinearMap.comp_apply, LinearEquiv.apply_symm_apply, matEntryCLM_apply,
      LinearMap.coe_toContinuousLinearMap']
    -- the read direction is the single basis matrix at index `finProdFinEquiv.symm b`
    have hread : (readKL M t ha k)
        (Pi.single (cf.symm ⟨k, Sum.inl ((frameSplitEquiv M t (k.val + 1)
          (ha.hdesc k.val k.isLt) (ha.hub k.val)).symm (Sum.inl (Sum.inl (Sum.inl b))))⟩) (1 : ℝ))
        = Matrix.single (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2 1 := by
      ext p q
      rw [readKL_apply, Matrix.of_apply, readK, Matrix.single_apply]
      by_cases hpq : (finProdFinEquiv.symm b).1 = p ∧ (finProdFinEquiv.symm b).2 = q
      · obtain ⟨hp, hq⟩ := hpq
        rw [if_pos ⟨hp, hq⟩, ← hp, ← hq, Prod.mk.eta, Equiv.apply_symm_apply, Pi.single_eq_same]
      · rw [if_neg hpq, Pi.single_eq_of_ne]
        intro hc
        apply hpq
        have hsig := cf.symm.injective hc
        have h2 := eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
        have h3 := (frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt)
          (ha.hub k.val)).symm.injective ((Sum.inl.injEq _ _).mp h2)
        have h4 : (p, q) = finProdFinEquiv.symm b :=
          finProdFinEquiv.injective (by
            rw [Equiv.apply_symm_apply]
            exact (Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp h3)))
        exact ⟨(congrArg Prod.fst h4).symm, (congrArg Prod.snd h4).symm⟩
    rw [hread]
  -- every NonK chart index is an identity arm of kLDU
  -- every NonK chart index decodes to a non-K frame role or a lift slot (the `kLDU` identity arm)
  set fse := frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) with hfse
  -- the chart index of each NonK case: `inl (fse.symm non-K)` for X/N/E, `inr lift` for the lift
  have hchart : ∀ i, (e.symm (Sum.inr i)).val = (⟨k,
      match i with
      | Sum.inl (Sum.inl (Sum.inl x')) => Sum.inl (fse.symm (Sum.inl (Sum.inl (Sum.inr x'))))
      | Sum.inl (Sum.inl (Sum.inr n)) => Sum.inl (fse.symm (Sum.inl (Sum.inr n)))
      | Sum.inl (Sum.inr ee) => Sum.inl (fse.symm (Sum.inr ee))
      | Sum.inr l => Sum.inr l⟩ : ChartIdx M (tDesc M t)) := by
    intro i
    rw [he, fiberSplit]
    rcases i with ((x' | n) | ee) | l <;> rfl
  have hNonK_id : ∀ i, ∀ x, kLDU M t ha x (cf.symm ((e.symm (Sum.inr i)).val))
      = x (cf.symm ((e.symm (Sum.inr i)).val)) := by
    intro i x
    rw [hchart, hcf, kLDU]
    rcases i with ((x' | n) | ee) | l
    · simp only [Equiv.apply_symm_apply, hfse]

exec
/bin/bash -lc "sed -n '420,470p' lean/DLNFibre/DLN/RLCT/Validate/RouteMUPolyLive.lean" in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
          (MvPolynomial.eval u) (kLDUGen_eval M (tach M) ha u))
    rw [← genBlkFlatLiveGen_eq_live]; exact h
  -- The chain naturality (poly pivot kept SYMBOLIC), then the pivot `eval u (poly-pivot) = u leafPivot`.
  have hchain := chainOfMt_map hmap
    (kLDUGen M (tach M) ha (Xvec (routeMAmbient M)) (leafPivot M ha (by norm_num) h0r h0c))
    (hleStruct M (tach M) ha)
  -- `eval u UPolyLive = sqSumHmat0 (poly chain).map (eval u) = sqSumHmat0 (ℝ chain at pivot eval u poly-pivot)`
  rw [interiorLiveUnit, VvalGen_eq_sqSumHmat0, UPolyLive, sqSumHmat0_map _ (MvPolynomial.eval u),
    hchain, eval_kLDUGen_leafPivot ha h0r h0c u]

/-- **`kLDU` fixes the interior-drop witness** `kLDU (wInt p) = wInt p`. On K-slots `kLDU` reads
`kLens (readK (wInt) k)`; `readK (wInt) k = I` (`readK_wInt`) and `kLens 1 = 1` (`kLens_one`), so the
K-slot is unchanged; off K, `kLDU` is identity. The witness seed (`interiorLiveUnit (wInt) =
VvalGen … (genBlkFlatLive … (wInt)) (wInt)`, the dead-leaf decoder). -/
theorem kLDU_wInt (ha : StructAdm M (tach M)) (p : ℕ) :
    kLDU M (tach M) ha (wInt M ha p) = wInt M ha p := by
  funext q
  rcases hq : chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL q with ⟨k, s⟩
  cases s with
  | inl sfr =>
    rcases hframe : frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) sfr
      with (((qK | qX) | qN) | qE)
    · -- K-branch: `kLens (readK wInt k) ij = (kLens 1) ij = (1:Matrix) ij = readK wInt k ij = wInt q`
      have hK1 : Matrix.of (readK M (tach M) ha (wInt M ha p) k)
          = (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ) := by
        ext a b; rw [Matrix.of_apply, readK_wInt, Matrix.one_apply]
      have hkl : kLens (readK M (tach M) ha (wInt M ha p) k)
          = (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ) := by
        rw [show readK M (tach M) ha (wInt M ha p) k
              = Matrix.of (readK M (tach M) ha (wInt M ha p) k) from rfl, hK1, kLens_one]
      simp only [kLDU, hq, hframe]
      rw [hkl]
      -- `(1:Matrix) ij = readK wInt k ij = wInt q`
      have hone : (1 : Matrix (Fin (Text M (tach M) (k.val + 2))) (Fin (Text M (tach M) (k.val + 2))) ℝ)
          (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2
          = readK M (tach M) ha (wInt M ha p) k (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2 :=
        congrFun (congrFun hK1.symm _) _
      rw [hone, readK, wInt]
      -- `readK wInt k ij = wInt q`: both are `wOnIdx` of a `chartIdxEquiv` slot; the LHS slot decodes
      -- (via `finProdFinEquiv`/`frameSplitEquiv`/`chartIdxEquiv` round-trips) to `⟨k, inl sfr⟩`, and
      -- `chartIdxEquiv q = ⟨k, inl sfr⟩` (`hq`). So both reduce to `wOnIdx ⟨k, inl sfr⟩`.
      simp only [Function.comp_apply, Equiv.apply_symm_apply, hq]
      congr 2
      rw [Prod.mk.eta, Equiv.apply_symm_apply, ← hframe, Equiv.symm_apply_apply]
    · simp only [kLDU, hq, hframe]
    · simp only [kLDU, hq, hframe]
    · simp only [kLDU, hq, hframe]
  | inr sl => simp only [kLDU, hq]

/-- **The LIVE interior unit is nonzero at the interior-drop witness** `interiorLiveUnit (wInt p) ≠ 0`.
Via `kLDU_wInt` (`kLDU` fixes `wInt`), the live unit is `sqSumHmat0` of the live decoder chain

codex
The local definition confirms `lduleafHOnIdx` matches directly on `frameSplitEquiv ... s`, and nearby proofs often avoid retyping the equivalence: they bind it with `set fse := ... with hfse` and then simplify using that binding. That points strongly toward the `set`/`change` route, not a `simp` config tweak.
exec
/bin/bash -lc 'rg -n "diagAxis|interiorLive_leafH|leafH_diagAxis|lduleafH_diagAxis|liveLeafHOnIdx" lean/DLNFibre -S' in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveAtom.lean:46:          ENNReal.ofReal (∏ j, |u j| ^ (interiorLive_leafH ha h0r h0c j))
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveAtom.lean:49:    (leafPivot M ha (by norm_num) h0r h0c) (interiorLive_leafH ha h0r h0c)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveAtom.lean:63:  leafH := interiorLive_leafH ha h0r h0c
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveAtom.lean:64:  leafH_pivot := interiorLive_leafH_pivot ha h0r h0c
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveAtom.lean:70:      leaf_integrand_of_rate (leafPivot M ha (by norm_num) h0r h0c) (interiorLive_leafH ha h0r h0c)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:48:* `interiorLive_leafH` (def, H2) — the multi-axis exponent vector, with `leafH leafPivot = minAdm−1`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:247:noncomputable def liveLeafHOnIdx (ha : StructAdm M (tach M)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:264:`liveLeafHOnIdx`; `0` elsewhere. At `leafPivot` the placement is `0` (the leaf boundary's K-block is
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:266:noncomputable def interiorLive_leafH (ha : StructAdm M (tach M))
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:271:    liveLeafHOnIdx ha (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j)
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:274:theorem interiorLive_leafH_pivot (ha : StructAdm M (tach M))
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:276:    interiorLive_leafH ha h0r h0c (leafPivot M ha (by norm_num) h0r h0c) = minAdm M - 1 := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:277:  rw [interiorLive_leafH, if_pos rfl]
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:299:          else |u j| ^ (interiorLive_leafH ha h0r h0c j) :=
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:305:`|det DB'|` is `interiorLive_BdetMonomial`; the pivot factor folds in via `interiorLive_leafH_pivot` +
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:314:      = ∏ j, |u j| ^ (interiorLive_leafH ha h0r h0c j) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:330:    (fun j => |u j| ^ (interiorLive_leafH ha h0r h0c j))]
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:332:    (fun j => if j = p₀ then (1 : ℝ) else |u j| ^ (interiorLive_leafH ha h0r h0c j))]
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:333:  rw [if_pos rfl, one_mul, interiorLive_leafH_pivot ha h0r h0c]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:21:exponent `(r_0+c_0) + 2(t_0−1−i)` matches `liveLeafHOnIdx`.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:29:* `diagAxis` / `u_diagAxis` / `diagAxis_injective` — the boundary-0 K-diagonal axis API.
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:31:OPEN (handed back — the bounded `liveLeafHOnIdx`-decode product-reindex glue):
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:32:* `leafH_diagAxis` — `leafH (diagAxis i) = (r₀+c₀)+2(t₀−1−i)` (the diagonal `if` fires after the
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:35:* `mem_image_diagAxis_of_leafH_ne_zero` — the off-image collapse (`leafH j ≠ 0 ∧ j ≠ pivot ⟹ j ∈
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:36:  image diagAxis`; the `Sigma.ext` + `fse.symm` reconstruction).
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:38:  `prod_mul_distrib`/`pow_add`, VALIDATED) · the RHS reindex (`Finset.prod_subset` to `image diagAxis`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:91:noncomputable def diagAxis (ha : StructAdm M (tach M)) (i : Fin (Text M (tach M) 2)) :
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:98:/-- `u (diagAxis i) = readK u 0 i i` (the diagonal K-core entry). -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:99:theorem u_diagAxis (ha : StructAdm M (tach M)) (u : Fin (routeMAmbient M) → ℝ)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:101:    u (diagAxis ha i) = readK M (tach M) ha u (0 : Fin 2) i i := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:102:  rw [readK, diagAxis]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:104:/-- `diagAxis` is injective. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:105:theorem diagAxis_injective (ha : StructAdm M (tach M)) : Function.Injective (diagAxis ha) := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:107:  rw [diagAxis, diagAxis] at hij
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:124:/-- `diagAxis i ≠ leafPivot` — the boundary-0 K-diagonal slot is not the (boundary-1) leaf pivot. -/
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:125:theorem diagAxis_ne_leafPivot (ha : StructAdm M (tach M))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:127:    diagAxis ha i ≠ leafPivot M ha (by norm_num) h0r h0c := by
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:128:  rw [diagAxis]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:131:/-- **`leafH` at the diagonal axis** — `interiorLive_leafH (diagAxis i) = (r₀+c₀) + 2(t₀−1−i)`. The
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:132:`if j = leafPivot` is `false` (`diagAxis_ne_leafPivot`); the `chartIdxEquiv` round-trip on `diagAxis i`
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:135:theorem leafH_diagAxis (ha : StructAdm M (tach M))
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:137:    interiorLive_leafH ha h0r h0c (diagAxis ha i)
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:140:  rw [interiorLive_leafH, if_neg (diagAxis_ne_leafPivot ha h0r h0c i)]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:141:  rw [diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]

exec
/bin/bash -lc 'rg -n "set .*frameSplitEquiv|generalize .*frameSplitEquiv|Equiv.apply_symm_apply" lean/DLNFibre/DLN/RLCT/Validate -S' in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDirectMorseP.lean:178:        show S (er (er.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDirectMorseP.lean:584:            show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:56:  rw [← Equiv.apply_symm_apply (regPivotFinEquiv H r hr) b, Equiv.symm_apply_apply,
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:57:    ← regGaugeIdxSplit_symm_inl H r hr hL ((regPivotFinEquiv H r hr).symm b), Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:663:    simp only [ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegSliceFderiv.lean:726:    simp only [ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
lean/DLNFibre/DLN/RLCT/Validate/RouteMStairTwoSided.lean:56:    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:91:        show A1 (σc (σc.symm i)) k = A1 i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:132:  rw [show ((e3_334.symm p).1, (e3_334.symm p).2) = e3_334.symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:151:    rw [show ((e3_334.symm p).1, (e3_334.symm p).2) = e3_334.symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:504:    rw [show ((e3_334.symm p).1, (e3_334.symm p).2) = e3_334.symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:532:    rw [show ((e3_334.symm p).1, (e3_334.symm p).2) = e3_334.symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:622:  rw [this, ← Equiv.apply_symm_apply (zσ p) (Sum.inl ik),
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:623:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:630:  rw [this, ← Equiv.apply_symm_apply (zσ p) (Sum.inr j),
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:631:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteM334Ratiofin.lean:654:  rw [← Equiv.apply_symm_apply (Equiv.sigmaEquivProd (Fin 2) (Fin 2)).symm
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFrameDet.lean:131:    rw [LinearEquiv.apply_symm_apply, hqmk, hqmk]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDepth2.lean:546:        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurDepth2.lean:597:  rw [show ((e2_22.symm p).1, (e2_22.symm p).2) = e2_22.symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:26:(`Equiv.apply_symm_apply` cancels the chartIdxEquiv round-trip; `frameSplitEquiv`/`liftSlotEquiv`
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:321:  rw [readK, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx,
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:322:    Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:330:  rw [readX, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:337:  rw [readN, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:346:  rw [readE, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:356:  rw [readW, wInt, Function.comp_apply, Equiv.apply_symm_apply, wOnIdx]
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:358:  simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:479:      rw [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_eq_self]⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedSquareL2.lean:128:  rw [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMProjV0Gate.lean:167:        rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMProjV0Gate.lean:170:        rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMUPolyLive.lean:461:      simp only [Function.comp_apply, Equiv.apply_symm_apply, hq]
lean/DLNFibre/DLN/RLCT/Validate/RouteMUPolyLive.lean:463:      rw [Prod.mk.eta, Equiv.apply_symm_apply, ← hframe, Equiv.symm_apply_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMEihdFreePoint.lean:113:    rw [LinearEquiv.apply_symm_apply] at h
lean/DLNFibre/DLN/RLCT/Validate/RouteMEihdFreePoint.lean:129:    rw [LinearEquiv.apply_symm_apply] at h
lean/DLNFibre/DLN/RLCT/Validate/RouteMEihdFreePoint.lean:145:    rw [dWdC_eq_eInV1, hd, LinearEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMEihdFreePoint.lean:150:    rw [hd, LinearEquiv.apply_symm_apply] at h
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedDecodeL2.lean:401:        rw [← hsplit, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedDecodeL2.lean:415:        rw [← hsplit, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotProducer.lean:160:    rw [hcle, ContinuousLinearEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectCarve.lean:423:        show S (er (er.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedPerFamily.lean:17:`Equiv.apply_symm_apply` / flat-index readback pattern (the `paramsEquivFlat` `FlatIdx` ordering align).
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:293:  rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:343:        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:509:  rw [← Equiv.apply_symm_apply (Equiv.sigmaEquivProd (Fin a) (Fin b)) (i, j),
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:967:  rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:979:    rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:1346:    rw [MeasurableEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:1426:        show S (er (er.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:1689:  rw [this, ← Equiv.apply_symm_apply (zσG r N hN hr p) (Sum.inl ik),
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:1690:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:1700:  rw [this, ← Equiv.apply_symm_apply (zσG r N hN hr p) (Sum.inr s),
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurFiring.lean:1701:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestLDUReadback.lean:391:  rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestPsiLens.lean:14:This module records those round-trips. They are the `Equiv.apply_symm_apply` / `symm_apply_apply`
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrameRaw.lean:45:    Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.trans_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrameRaw.lean:97:  rw [← rThresholdSplit_symm_inl r a ha k, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrameRaw.lean:102:  rw [← rThresholdSplit_symm_inr r a ha k, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrameRaw.lean:184:    Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.trans_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestFrameRaw.lean:188:  exact (Equiv.apply_symm_apply _ m).symm
lean/DLNFibre/DLN/RLCT/Validate/DeepestPivotFrame.lean:59:    have happ : J.toEquivRange (σ k) = ⟨s k, hmem k⟩ := Equiv.apply_symm_apply _ _
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedChartOpaque.lean:83:    rw [shearMBody, MeasurableEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSmearedChartOpaque.lean:90:    rw [shearMBody, MeasurableEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:47:    Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:162:    Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:175:      Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:382:    rw [MeasurableEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:402:  rw [this, ← Equiv.apply_symm_apply (zσRect m n N hN hm hn hmn pv) (Sum.inl ik),
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:403:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:413:  rw [this, ← Equiv.apply_symm_apply (zσRect m n N hN hm hn hmn pv) (Sum.inr s),
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:414:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurRectAngular.lean:563:        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:95:  simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:178:    rw [kLDU, activeSlotE]; simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:181:    rw [kLDU, leafSlot]; simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean:428:        intro z; rw [readK, Prod.mk.eta, finProdFinEquiv.apply_symm_apply qK,
lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean:273:    simp only [LinearEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean:697:    rw [LinearEquiv.apply_symm_apply] at h
lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean:715:    rw [LinearEquiv.apply_symm_apply] at h
lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean:945:    rw [dWdC_eq_eInV1, hd, LinearEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMHDtotEihd.lean:950:    rw [hd, LinearEquiv.apply_symm_apply] at h
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:1461:    simp only [deepestEPivot, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:1466:       simp only [deepestEPivot, Equiv.apply_symm_apply])
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:1496:    simp only [deepestEFull, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:1501:       simp only [deepestEFull, Equiv.apply_symm_apply])
lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean:1789:    rw [hcle, ContinuousLinearEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatBlockLE.lean:110:    ⟨finSumFinEquiv.symm (Fin.cast hr.symm i), by rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMFlatBlockLE.lean:112:    ⟨finSumFinEquiv.symm (Fin.cast hc.symm j), by rw [Equiv.apply_symm_apply]; apply Fin.ext; simp⟩
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:141:  rw [diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean:142:  conv_lhs => rw [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean:19:  K reads the LDU matrix, the others pass through (via `Equiv.apply_symm_apply` cancellation — the
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean:87:  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean:95:  simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean:103:  simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean:111:  simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLens.lean:119:  simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMCLEConj.lean:134:            ContinuousLinearEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCorank3.lean:521:  rw [show ((e3c3.symm p).1, (e3c3.symm p).2) = e3c3.symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:184:  simp only [Equiv.apply_symm_apply, hfs]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:225:        (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply, hfs])]; exact hid_vanish
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:228:        (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply, hfs])]; exact hid_vanish
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:231:        (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply, hfs])]; exact hid_vanish
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:233:      (fun x => by rw [kLDU]; simp only [hcf, Equiv.apply_symm_apply])]; exact hid_vanish
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:310:    · subst h; rw [Equiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_same]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:427:        (by rw [Equiv.apply_symm_apply] :
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:432:    simp only [ContinuousLinearMap.comp_apply, LinearEquiv.apply_symm_apply, matEntryCLM_apply,
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:443:        rw [if_pos ⟨hp, hq⟩, ← hp, ← hq, Prod.mk.eta, Equiv.apply_symm_apply, Pi.single_eq_same]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:453:            rw [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:459:  set fse := frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) with hfse
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:475:    · simp only [Equiv.apply_symm_apply, hfse]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:476:    · simp only [Equiv.apply_symm_apply, hfse]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:477:    · simp only [Equiv.apply_symm_apply, hfse]
lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean:478:    · simp only [Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestFramedProductPivot.lean:487:so the outer reindex cancels the inner `.symm` (`Equiv.apply_symm_apply`). -/
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegBlockInvertible.lean:148:    · simp only [Matrix.of_apply, Equiv.apply_symm_apply, Sum.elim_inl]
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegBlockInvertible.lean:149:    · simp only [Matrix.of_apply, Equiv.apply_symm_apply, Sum.elim_inr]
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegBlockInvertible.lean:182:      stackRowsCLE_apply, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply]
lean/DLNFibre/DLN/RLCT/Validate/DeepestRegBlockInvertible.lean:304:          ContinuousLinearEquiv.apply_symm_apply _ _
lean/DLNFibre/DLN/RLCT/Validate/FrontPivotWLOG.lean:120:      apply eFront.injective; rw [Equiv.apply_symm_apply]; apply Subtype.ext; apply Fin.ext; rfl
lean/DLNFibre/DLN/RLCT/Validate/DeepestDiffeoBridgeL2.lean:2730:  rw [← Matrix.reindex_symm, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:54:  rw [MeasurableEquiv.apply_symm_apply, ← bridgeCLE_symm_apply,
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:69:  rw [genBlkParamsStruct, bridgeCLE_apply, MeasurableEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMBridgeCLE.lean:79:  rw [radialParams, bridgeCLE_apply, MeasurableEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:265:        show S (σc (σc.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1007:        show S (er (er.symm i)) k = S i k; rw [Equiv.apply_symm_apply]] at this
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1146:  rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1158:    rw [show (((eG r).symm p).1, ((eG r).symm p).2) = (eG r).symm p from rfl, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1328:    rw [MeasurableEquiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1403:  rw [this, ← Equiv.apply_symm_apply (zσG2 r N hN hr p) (Sum.inl ik),
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1404:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1413:  rw [this, ← Equiv.apply_symm_apply (zσG2 r N hN hr p) (Sum.inr s),
lean/DLNFibre/DLN/RLCT/Validate/RouteMSchurCapACarveP.lean:1414:    MeasurableEquiv.piCongrLeft_apply_apply, Equiv.apply_symm_apply]

codex
There is already a partial `leafH_diagAxis` in `RouteMBdetMonomial.lean`, and it has the failing shape plus a `conv_lhs` attempt. I’ll read that exact section before giving the final idiom.
exec
/bin/bash -lc "sed -n '70,155p' lean/DLNFibre/DLN/RLCT/Validate/RouteMBdetMonomial.lean" in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
      = |LinearMap.det (fderiv ℝ (BchartLeaf ha) (kLDU M (tach M) ha x)).toLinearMap|
        * |LinearMap.det (fderiv ℝ (kLDU M (tach M) ha) x).toLinearMap| := by
  have hcomp : (fun y => BchartLeaf ha (kLDU M (tach M) ha y))
      = BchartLeaf ha ∘ kLDU M (tach M) ha := rfl
  rw [hcomp, fderiv_comp x (Bchart_differentiableAt ha _) (differentiable_kLDU M (tach M) ha x)]
  rw [ContinuousLinearMap.coe_comp, LinearMap.det_comp, abs_mul]

/-- The K-core of `kLDU (pbo u)` at boundary `0` is the lens applied to the (pbo-fixed) K-core of `u`. -/
theorem readK_kLDU_pbo (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (u : Fin (routeMAmbient M) → ℝ) :
    Matrix.of (readK M (tach M) ha
        (kLDU M (tach M) ha (pivotBlowupOn (activeM M ha)
          (leafPivot M ha (by norm_num) h0r h0c) u)) ⟨0, by decide⟩)
      = kLens (Matrix.of (readK M (tach M) ha u ⟨0, by decide⟩)) := by
  ext i j
  rw [Matrix.of_apply, readK_kLDU]
  congr 1
  ext a b
  exact readK_pbo_all ha h0r h0c u ⟨0, by decide⟩ a b

/-- The diagonal K-axis of boundary `0` at index `i`: the flat coordinate reading `readK · 0 i i`. -/
noncomputable def diagAxis (ha : StructAdm M (tach M)) (i : Fin (Text M (tach M) 2)) :
    Fin (routeMAmbient M) :=
  (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm
    ⟨(0 : Fin 2), Sum.inl ((frameSplitEquiv M (tach M) ((0 : Fin 2).val + 1)
      (ha.hdesc 0 (by norm_num)) (ha.hub 0)).symm
        (Sum.inl (Sum.inl (Sum.inl (finProdFinEquiv (i, i))))))⟩

/-- `u (diagAxis i) = readK u 0 i i` (the diagonal K-core entry). -/
theorem u_diagAxis (ha : StructAdm M (tach M)) (u : Fin (routeMAmbient M) → ℝ)
    (i : Fin (Text M (tach M) 2)) :
    u (diagAxis ha i) = readK M (tach M) ha u (0 : Fin 2) i i := by
  rw [readK, diagAxis]

/-- `diagAxis` is injective. -/
theorem diagAxis_injective (ha : StructAdm M (tach M)) : Function.Injective (diagAxis ha) := by
  intro i j hij
  rw [diagAxis, diagAxis] at hij
  have h1 := (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL).symm.injective hij
  have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
  have h3 := (frameSplitEquiv M (tach M) ((0 : Fin 2).val + 1) (ha.hdesc 0 (by norm_num))
    (ha.hub 0)).symm.injective ((Sum.inl.injEq _ _).mp h2)
  have h4 := finProdFinEquiv.injective
    ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp ((Sum.inl.injEq _ _).mp h3)))
  exact (Prod.mk.injEq .. ▸ h4).1

/-- **The LHS collapse** — factor 1 · factor 2 (boundary 0) folds to the single per-pivot product:
`|∏ q|^{r+c} · ∏_i |q i|^{2(t−1−i)} = ∏_i |q i|^{(r+c)+2(t−1−i)}`. -/
theorem lhs_collapse (τ r c : ℕ) (q : Fin τ → ℝ) :
    |∏ i, q i| ^ (r + c) * ∏ i, |q i| ^ (2 * (τ - 1 - (i : ℕ)))
      = ∏ i : Fin τ, |q i| ^ ((r + c) + 2 * (τ - 1 - (i : ℕ))) := by
  rw [Finset.abs_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => by rw [← pow_add])

/-- `diagAxis i ≠ leafPivot` — the boundary-0 K-diagonal slot is not the (boundary-1) leaf pivot. -/
theorem diagAxis_ne_leafPivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (i : Fin (Text M (tach M) 2)) :
    diagAxis ha i ≠ leafPivot M ha (by norm_num) h0r h0c := by
  rw [diagAxis]
  exact boundary0_ne_leafPivot ha h0r h0c _

/-- **`leafH` at the diagonal axis** — `interiorLive_leafH (diagAxis i) = (r₀+c₀) + 2(t₀−1−i)`. The
`if j = leafPivot` is `false` (`diagAxis_ne_leafPivot`); the `chartIdxEquiv` round-trip on `diagAxis i`
exposes the boundary-0 K-slot tag, the `frameSplitEquiv`/`finProdFinEquiv` round-trips collapse, and the
diagonal `i = i` fires `if_pos`. -/
theorem leafH_diagAxis (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) (i : Fin (Text M (tach M) 2)) :
    interiorLive_leafH ha h0r h0c (diagAxis ha i)
      = (Text M (tach M) 1 - Text M (tach M) 2) + (Wext M 1 - Text M (tach M) 2)
        + 2 * (Text M (tach M) 2 - 1 - (i : ℕ)) := by
  rw [interiorLive_leafH, if_neg (diagAxis_ne_leafPivot ha h0r h0c i)]
  rw [diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]
  conv_lhs => rw [Equiv.apply_symm_apply]
  rw [finProdFinEquiv.symm_apply_apply, if_pos rfl]

end DLNFibre.DLN.RLCT

exec
/bin/bash -lc "sed -n '235,280p' lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorLiveContract.lean" in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
            = readK M (tach M) ha x k := by
          funext a b; exact readK_pbo_all ha h0r h0c x k a b
        simp only [hmat, hpboq]
      | ⟨k, Sum.inr s⟩ => simp only [hpboq]

/-! ## H2 — the multi-axis Jacobian exponent vector `leafH` -/

/-- **The `ChartIdx`-indexed K-diagonal exponent placement** (the LIVE-leaf analogue of the dead-leaf
`lduleafHOnIdx`, inlined to decouple from the retired `RouteMInteriorLDUContract`). At a frame slot
(`Sum.inl s`), boundary `k`, the K-role branch decodes `(i,j) = finProdFinEquiv.symm qK`; on the
diagonal `i = j` it returns the per-pivot exponent `(r_s + c_s) + 2·(t_s − 1 − i)` (the Schur frame
`r_s+c_s` + the LDU core `2(t_s−1−i)`), `0` off-diagonal / X,N,E / lift. -/
noncomputable def liveLeafHOnIdx (ha : StructAdm M (tach M)) :
    ChartIdx M (tDesc M (tach M)) → ℕ := fun q =>
  match q with
  | ⟨k, Sum.inl s⟩ =>
    match frameSplitEquiv M (tach M) (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s with
    | Sum.inl (Sum.inl (Sum.inl qK)) =>
      let ij := finProdFinEquiv.symm qK
      if ij.1 = ij.2 then
        (Text M (tach M) (k.val + 1) - Text M (tach M) (k.val + 2))
          + (Wext M (k.val + 1) - Text M (tach M) (k.val + 2))
          + 2 * (Text M (tach M) (k.val + 2) - 1 - ij.1.val)
      else 0
    | _ => 0
  | ⟨_, Sum.inr _⟩ => 0

/-- **H2 — the multi-axis Jacobian exponent vector** for the LIVE-leaf ∘ kLDU chart. The binding axis
`leafPivot` carries `minAdm−1` (override); the lensed K-diagonal axes carry the frame+LDU exponents
`liveLeafHOnIdx`; `0` elsewhere. At `leafPivot` the placement is `0` (the leaf boundary's K-block is
empty), so the override introduces the genuine radial exponent without masking a K exponent. -/
noncomputable def interiorLive_leafH (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) : Fin (routeMAmbient M) → ℕ := fun j =>
  if j = leafPivot M ha (by norm_num) h0r h0c then
    minAdm M - 1
  else
    liveLeafHOnIdx ha (chartIdxEquiv M (tDesc M (tach M)) ha.h0 ha.hc ha.hL j)

/-- **H2 — the binding axis carries `minAdm−1`** (the pivot override is `if_pos rfl`). -/
theorem interiorLive_leafH_pivot (ha : StructAdm M (tach M))
    (h0r : 0 < Text M (tach M) 2) (h0c : 0 < Wext M 2) :
    interiorLive_leafH ha h0r h0c (leafPivot M ha (by norm_num) h0r h0c) = minAdm M - 1 := by
  rw [interiorLive_leafH, if_pos rfl]

/-! ## H2 — the chart Jacobian monomial (headline ∘ kLDU) -/


exec
/bin/bash -lc "sed -n '150,190p' lean/DLNFibre/DLN/RLCT/Validate/RouteMKLDUAmbientDet.lean" in /home/ubuntu/workspace/genm-r1lower-wt
 succeeded in 0ms:
      ((readKL M t ha k).toContinuousLinearMap y) :=
    (kLens_hasFDerivAt _).differentiableAt.hasFDerivAt
  exact (matEntryCLM (Text M t (k.val + 2)) i j).hasFDerivAt.comp y (hkl.comp y hread)

/-- **The K-reader kills a single basis vector supported off boundary `k`** — `readK x k` reads only
flat coords in boundary-`k`'s chart slot (`chartIdxEquiv.symm ⟨k, …⟩`), so the standard basis vector
`Pi.single (chartIdxEquiv.symm c') 1` at any `c'` with `c'.1 ≠ k` is read as `0`. -/
theorem readKL_single_off_boundary (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t) (k : Fin L)
    (c' : ChartIdx M (tDesc M t)) (hne : c'.1 ≠ k) :
    readKL M t ha k
        (Pi.single ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm c') (1 : ℝ)) = 0 := by
  ext i j
  rw [readKL_apply, Matrix.of_apply, readK, Matrix.zero_apply]
  apply Pi.single_eq_of_ne
  intro hc
  apply hne
  have hci := (chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm.injective hc
  exact (congrArg Sigma.fst hci).symm

/-- The K-output function identity: at chart index `⟨k, inl s⟩` whose frame-split decode is the K-role
`inl(inl(inl qK))`, `fun x => kLDU x (cf.symm ⟨k, inl s⟩) = fun x => kLens (readK x k) ij.1 ij.2`
(`ij = finProdFinEquiv.symm qK`). -/
theorem kLDU_out_K_fun (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (k : Fin L) (s : Fin (schurDim M (tDesc M t) k.val))
    {qK : Fin (Text M t (k.val + 1 + 1) * Text M t (k.val + 1 + 1))}
    (hfs : frameSplitEquiv M t (k.val + 1) (ha.hdesc k.val k.isLt) (ha.hub k.val) s
      = Sum.inl (Sum.inl (Sum.inl qK))) :
    (fun x => kLDU M t ha x
        ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩))
      = (fun x => kLens (Matrix.of (readK M t ha x k))
          (finProdFinEquiv.symm qK).1 (finProdFinEquiv.symm qK).2) := by
  funext x
  show kLDU M t ha x ((chartIdxEquiv M (tDesc M t) ha.h0 ha.hc ha.hL).symm ⟨k, Sum.inl s⟩) = _
  rw [kLDU]
  simp only [Equiv.apply_symm_apply, hfs]
  rfl

/-- The identity-arm function identity: at any chart index `c` that is NOT a K-role output,
`fun x => kLDU x (cf.symm c) = fun x => x (cf.symm c)`. The hypothesis `hid` packages the
frame-split-decode-is-not-K (or lift) condition as a pointwise equality. -/
theorem kLDU_out_id_fun (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)

codex
Most likely fix: **make `diagAxis` use the exact same `frameSplitEquiv` spine as `liveLeafHOnIdx` will use after matching `k = (0 : Fin 2)`**. Then `simp` can see one equivalence, not two proof-noisy copies.

Change `diagAxis` to:

```lean
(frameSplitEquiv M (tach M) ((0 : Fin 2).val + 1)
  (ha.hdesc (0 : Fin 2).val (0 : Fin 2).isLt)
  (ha.hub (0 : Fin 2).val)).symm
```

instead of the hand-written `0` / `by norm_num` version. Then the proof should be roughly:

```lean
  rw [interiorLive_leafH, if_neg (diagAxis_ne_leafPivot ha h0r h0c i)]
  rw [diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]
  simp only [Equiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
  rw [if_pos rfl]
```

`conv` will not be more tolerant than `rw`; it only changes where rewriting is attempted. `simp` config also will not fix non-defeq `e₁ (e₂.symm X)`.

Fallback: prove proof-irrelevance for `frameSplitEquiv` once, then rewrite one equivalence to the other before `Equiv.apply_symm_apply`.

```lean
private lemma frameSplitEquiv_proof_irrel
    (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 h1' : Text M t (s + 1) ≤ Text M t s)
    (h2 h2' : Text M t (s + 1) ≤ Wext M s) :
    frameSplitEquiv M t s h1 h2 =
      frameSplitEquiv M t s h1' h2' := by
  cases Subsingleton.elim h1 h1'
  cases Subsingleton.elim h2 h2'
  rfl
```

Then after `rw [liveLeafHOnIdx]`, use a local `have hfse : e_live = e_diag := ...` and:

```lean
  simp only [hfse, Equiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
  rw [if_pos rfl]
```

So: use canonicalized definitional shape if you can; otherwise rewrite the two `frameSplitEquiv`s equal first. Avoid `Fin.cases` on `i`; it is unrelated to this failure.
tokens used
51,305
Most likely fix: **make `diagAxis` use the exact same `frameSplitEquiv` spine as `liveLeafHOnIdx` will use after matching `k = (0 : Fin 2)`**. Then `simp` can see one equivalence, not two proof-noisy copies.

Change `diagAxis` to:

```lean
(frameSplitEquiv M (tach M) ((0 : Fin 2).val + 1)
  (ha.hdesc (0 : Fin 2).val (0 : Fin 2).isLt)
  (ha.hub (0 : Fin 2).val)).symm
```

instead of the hand-written `0` / `by norm_num` version. Then the proof should be roughly:

```lean
  rw [interiorLive_leafH, if_neg (diagAxis_ne_leafPivot ha h0r h0c i)]
  rw [diagAxis, Equiv.apply_symm_apply, liveLeafHOnIdx]
  simp only [Equiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
  rw [if_pos rfl]
```

`conv` will not be more tolerant than `rw`; it only changes where rewriting is attempted. `simp` config also will not fix non-defeq `e₁ (e₂.symm X)`.

Fallback: prove proof-irrelevance for `frameSplitEquiv` once, then rewrite one equivalence to the other before `Equiv.apply_symm_apply`.

```lean
private lemma frameSplitEquiv_proof_irrel
    (M t : Fin (L + 1) → ℕ) (s : ℕ)
    (h1 h1' : Text M t (s + 1) ≤ Text M t s)
    (h2 h2' : Text M t (s + 1) ≤ Wext M s) :
    frameSplitEquiv M t s h1 h2 =
      frameSplitEquiv M t s h1' h2' := by
  cases Subsingleton.elim h1 h1'
  cases Subsingleton.elim h2 h2'
  rfl
```

Then after `rw [liveLeafHOnIdx]`, use a local `have hfse : e_live = e_diag := ...` and:

```lean
  simp only [hfse, Equiv.apply_symm_apply, finProdFinEquiv.symm_apply_apply]
  rw [if_pos rfl]
```

So: use canonicalized definitional shape if you can; otherwise rewrite the two `frameSplitEquiv`s equal first. Avoid `Fin.cases` on `i`; it is unrelated to this failure.
