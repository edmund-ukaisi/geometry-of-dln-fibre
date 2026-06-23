# Statement card — `MinAdmMono` (#149 hMono + #143 close): componentwise `minAdm` monotonicity

**File:** `lean/DLNFibre/DLN/RLCT/Validate/MinAdmMono.lean` (rs-grind, branch `fm3/routem`).
**Build:** GREEN, zero `sorry`/`axiom`/`native_decide`. Axioms (headline decls): `[propext,
Classical.choice, Quot.sound]` (the clean-three). `BindingArith.lean` (now `import`s `MinAdmMono`) also GREEN.

## What is proved (Proved, not Assumed/Cited)

The genuine reusable theorem and the binding-arithmetic corollary it was built for:

- `inf'_Mval_mono (M M' : Fin (L+1)→ℕ) (hle : ∀ i, M' i ≤ M i) :`
  `(Adm M').inf' _ (Mval M') ≤ (Adm M).inf' _ (Mval M)`
  — **componentwise monotonicity of the minimal codim**: drop any widths and the minimal `Mval` does not
  increase. The genuine, reusable theorem (pp-rstar cert §"CLEANER alternative").
- `lambdaCore_schurStateRed_le (M) : lambdaCore (schurStateRed M) ≤ lambdaCore M`
  — **hMono (#149)**, the corollary at `M' = schurStateRed M` (`schurStateRed_le : schurStateRed M ≤ M`
  componentwise). This is the named hypothesis of `BindingArith.bind_hnReg`.
- `BindingArith.bind_hnReg_uncond (M) : 0 ≤ bindNReg M` — **`hnReg` now UNCONDITIONAL** (for all `M`, the
  exact `binding_recursion_of_step` form). The monotonicity named-gap is closed; no remaining hypothesis.

## The construction (the load-bearing content)

The transfer `runMinCap M' T` = the **forward running-min of the bound-capped exponent**
`T'_j := min_{k≤j} (min (T_k) (admBound M' k))` (cert's `runningMinCap`). Two obligations:

1. `runMinCap_mem_Adm` — `runMinCap M' T ∈ Adm M'` (admissibility): cap-bound (a), running-min
   weak-decrease (b, `runMinCap_antitone`), last-index-zero (c). Rides only on the cap, NOT on `M' ≤ M`.
2. `Mval_runMinCap_le` — `Mval M' (runMinCap M' T) ≤ Mval M T` (the value drop). Per-term via:
   - `runMinCap_eq_local` — the **characterization** `T'_j = min (T_j) (min (tPrev' j) (M' j.succ))`
     (`le_antisymm`; `≥` direction pushes the `ℕ→ℤ` cast inside `inf'` via `comp_inf'_eq_inf'_comp` +
     `Nat.cast_min`, then `le_inf'` per `k ≤ j`). The load-bearing structural fact.
   - `perterm_drop` — the **clean elementary integer lemma**: with `t' = min t (min a b)`, `a≤ρ`, `b≤w`,
     `t≤ρ`, `t≤w`, then `(a−t')(b−t') ≤ (ρ−t)(w−t)`. Three-way `rcases` on the min; no `nlinarith`.

## Fidelity to the cert (no overclaim)

- pp-rstar cert (`r1-realizability-witness-codex/hmono-minadm-monotone-CERT.md`) adjudicated hMono **TRUE**
  (0/336 non-leaf M) with the running-min-cap transfer. This Lean proof is that transfer.
- **The cert's "false free per-term lemma" trap is AVOIDED, not hit**: the cert flagged that the per-term
  drop is false from `t' ≤ t` alone (1678 ctrexamples) and needs the Case-A/B coupling. My decorrelated
  numeric re-derivation (3M random) found the **exact** sufficient form: `t' = min(t, ρ', W')` (the
  characterization), under which the drop is `0/2M`-clean WITHOUT a case split on a local width-drop — a
  cleaner route than the cert's Case-A/B. The characterization (`runMinCap_eq_local`) is where the running
  structure enters; `perterm_drop` is then context-free.
- Anchors (cert §Anchors): `nReg(2,2,2)=minAdm(2,2,2)−minAdm(1,1,2)=3−1=2`, `nReg(3,2,3)=5−2=3` — match
  the committed `RouteMNReg.nRegOf_M222=2`, `nRegOf_M323=3`. So hMono holds on both anchors.

## What this closes / what it feeds

- **#149 (hMono): CLOSED, sorry-free.** **#143 (G-a recursion arithmetic): CLOSED** — all 5 hypotheses of
  fm3's `binding_recursion_of_step` (`@routem-ga`) are now dischargeable with NO named gap:
  `harith_step`=`bind_harith_step`, `harith_base`=`bind_harith_base` (gated `degenChild := isLeafNode ∘
  schurStateRed`), `hdrop`=`bind_hdrop`, `hlam`=`bind_hlam`, `hnReg`=`bind_hnReg_uncond`.
- Controller wiring needed: add `import DLNFibre.DLN.RLCT.Validate.MinAdmMono` to `DLNFibre.lean`
  (single-writer; rs-grind does not edit it). `BindingArith` already imports it.
- Local copies `T_le_tPrev`/`T_le_Msucc` (the `private` `ResolutionAtlas` lemmas, re-proved verbatim) — if
  crux2 de-privates the originals, these can be dropped.

## Caveat (next to the claim)

`degenChild`-consistency: `isLeafNode M → isLeafNode (schurStateRed M)` (child-nonleaf ⟹ node-nonleaf,
verified 0/336, a corollary of hMono — `minAdm M = 0 ⟹ minAdm(schurStateRed M) = 0`). The integrator must
supply this for the `degenChild := isLeafNode ∘ schurStateRed` instantiation; it is a `≤`-on-`minAdm`
consequence of `inf'_Mval_mono`, ready to add if the `binding_recursion_of_step` application needs it.
