# L2 (b)-route DECIDING CALL — B (front-pivot WLOG) is the sound, less-Lean route

Re-adjudicated with the refined cost info (A's pointwise (b) rests on TWO unbuilt several-hundred-LoC
pieces: the corrected Pπ-telescope + FACT2). **Verdict: B (front-pivot WLOG) is SOUND and DECISIVELY
less-Lean.** It avoids both unbuilt A' pieces — for a front pivot, `pivotThr J' = rThr`, no Pπ, the clean
telescope applies, and (b) is an EXACT equality. Decorrelated Codex (xhigh) independently reached the same
verdict. All B soundness checks exact (sympy). Read-only.

## B is SOUND — the three checks (exact) + the soundness subtlety (resolved)

`Π` = a column permutation bringing `B`'s rank-`r` pivot columns to the FRONT `{0..r-1}`. The param change
`τ_Π : A ↦ (A with last layer ·Π)`.

1. **Exact loss identity** (sympy, L=2, generic): `dlnLoss H B (A) = dlnLoss H (B·Π) (τ_Π A)`. Because
   `∏(τ_Π A) = (∏A)·Π` and `‖M − B‖²_F = ‖(M−B)·Π‖²_F = ‖∏(τ_Π A) − B·Π‖²_F` (Π orthogonal).
2. **`τ_Π` is measure-preserving:** `A_{L-1} ↦ A_{L-1}·Π` is a column permutation = a coordinate
   permutation of the last layer's entries ⇒ `|det| = 1` ⇒ MP. (Other layers fixed.)
3. **rank + front-pivot:** `rank(B·Π) = rank(B) = r` (Π invertible); by choice of Π, `B·Π`'s first `r`
   columns are `B`'s pivots ⇒ `B·Π` has FRONT pivot ⇒ the internal `J'` (from `B·Π`'s pivot frame) is
   front ⇒ `pivotThr J' = rThr` ⇒ (b) is the EXACT equality `∑deepestEFull² = Sreg`.

**The soundness subtlety (Codex Q1, resolved via the headline's form).** `rlctAt` is local:
`rlctAt(loss B) w0(B) = rlctAt(loss B·Π) (τ_Π w0(B))`. The two deepest points `deepestPoint(B)` and
`deepestPoint(B·Π)` are `Classical.choice` — NOT literally `τ_Π`-equivariant. BUT the headline is NOT
stated at a single deepest point — it is the INFIMUM over the optimal set:

    aoyagi_learning_coefficient : (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ofReal (aoyagiLambda …)

(`Skeleton.lean:1725`; `optimalSet` = the loss-zero set, `Loss.lean:60`). `τ_Π` is a GLOBAL MP
homeomorphism mapping `optimalSet H B` bijectively to `optimalSet H (B·Π)` (the loss-zero sets correspond
exactly, by the loss identity), and preserving each point's local `rlctAt` (banked MP germ-invariance).
So the INFIMUM is preserved — choice-independent, no deepest-point equivariance needed. This is the clean
global-min bridge Codex flagged, and it is EXACTLY the headline's `⨅`-form.

## B is decisively less-Lean than A' (cost ranking)

| | A' (pointwise comparability) | B (front-pivot WLOG) |
|---|---|---|
| (b) | UNBUILT Pπ-telescope (clean telescope inapplicable, hS1' refuted) + UNBUILT FACT2 + Frobenius | EXACT equality (front J' ⇒ pivotThr=rThr; the clean `endpoint_telescoping_eq` APPLIES) |
| new geometry | several hundred LoC (the Pπ-telescope is the genuine bulk) | NONE — reuses `deepest_gauge_construction(B·Π)` verbatim |
| transfer | — | loss identity (mechanical) + MP (`|det Π|=1`) + banked `rlctAtOn_comp_homeomorph` |

A' is the unbuilt geometric bulk; B is standard algebraic transport reusing the existing front-pivot
chart. **B wins decisively.** (The earlier preference for A' assumed its (b) was "pointwise via banked
machinery"; the formaliser correctly found the machinery was the ASSEMBLY GIVEN the two unbuilt pieces.)

## Build-ready spec for B (statements + homes + dependency order)

### (1) `front_pivot_perm_exists` — Π bringing B's pivots to front
    theorem front_pivot_perm_exists (H r) (B : Matrix (Fin (H 0)) (Fin (H (Fin.last L))) ℝ)
        (hB : B.rank = r) :
      ∃ (Π : Equiv.Perm (Fin (H (Fin.last L)))),
        (B.submatrix id Π).rank = r ∧
        -- the first r columns of B·Π are a rank-r set (front pivot):
        (∀ J' : Fin r ↪ Fin (H (Fin.last L)), J' = frontEmbed → (B·Π is front-pivot for J'))
Home: a new low-level module `DLN.RLCT.FrontPivotPerm` (or near `DeepestPivotFrame`). Built from `B`'s
column rank-r witness (the same pivot-set machinery `deepestPoint_frame_pivot_exists` uses) + `Equiv.Perm`.
Routine linear algebra (pick `r` independent columns, permute to front).

### (2) `dlnLoss_colPerm_eq` — the exact loss identity
    theorem dlnLoss_colPerm_eq (H) (B) (Π : Equiv.Perm (Fin (H (Fin.last L)))) (A : Params H) :
      dlnLoss H B A = dlnLoss H (B.submatrix id Π) (paramColPermLast H Π A)
where `paramColPermLast` is `τ_Π` (last layer's output columns permuted by Π). Proof: `∏(τ_Π A) =
(∏A)·(perm matrix)`; `‖M−B‖² = ‖(M−B)·P‖²` (P a permutation = orthogonal, Frobenius-invariant). Home:
`DLN.RLCT.Foundations.Loss` (extends the loss API). Mechanical (`Matrix.submatrix`/`Finset.sum_equiv`).

### (3) `paramColPermLast_measurePreserving` — τ_Π is MP
    theorem paramColPermLast_measurePreserving (H) (Π) :
      MeasurePreserving (paramColPermLast H Π) volume volume
Proof: `τ_Π` is a coordinate permutation of `Params H` (permutes the last layer's column-indexed entries),
`|det| = 1`. Home: `Foundations` (with the `paramsEquivFlat`/volume API). Use `MeasurePreserving` of a
`MeasurableEquiv` that permutes coordinates (`volume_preserving_*` / `MeasurePreserving.comp` on the
finite-product measure).

### (4) `optimalSet_colPerm_image` + `rlct_infimum_colPerm_eq` — the transfer
    theorem rlct_infimum_colPerm_eq (H) (B) (hB) (Π) :
      (⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w)
        = (⨅ w ∈ optimalSet H (B·Π), rlctAt H (dlnLoss H (B·Π)) w)
Proof: `τ_Π` (as a homeomorphism `Params H ≃ₜ Params H`, MP by (3)) maps `optimalSet H B` bijectively to
`optimalSet H (B·Π)` (by (2): `loss B (A) = 0 ⟺ loss (B·Π) (τ_Π A) = 0`), and `rlctAt H (dlnLoss H B) w =
rlctAt H (dlnLoss H (B·Π)) (τ_Π w)` at each `w` (banked `rlctAtOn_comp_homeomorph`, `S1Fubini.lean:54` —
MP homeomorph germ-invariance; lift `rlctAtOn → rlctAt`). Then `⨅`-over-bijection-with-equal-values are
equal (`iInf` congruence / `Equiv`-reindex of the infimum). Home: near `aoyagi_learning_coefficient`
(`Skeleton`) or a new `DLN.RLCT.ColPermInvariance`.

### (5) headline transfer — `aoyagi_learning_coefficient` for general (non-front) B
    -- the existing aoyagi_learning_coefficient is PROVED for B·Π (front pivot ⇒ (b) exact);
    -- for general B: rw [rlct_infimum_colPerm_eq H B hB Π] then apply the front-pivot proof to B·Π.
The L2 producer `hproducer` then only ever runs with a FRONT `J'` (pivotThr=rThr) ⇒ (b) EXACT, no
comparability, no Pπ, no FACT2. The S5a/S5b/S5c/(d,e) coupled-𝓝 sub-lemmas (hproducer-decomp-cert Part 2)
are UNCHANGED and still needed; only the (b)-atom simplifies from comparability to EXACT equality.

## Dependency order
(1) front_pivot_perm_exists → (2) dlnLoss_colPerm_eq → (3) paramColPermLast MP → (4) rlct_infimum_colPerm_eq
(uses 2,3 + banked `rlctAtOn_comp_homeomorph`) → (5) headline transfer (uses 4 + the front-pivot-B·Π
headline proof, where (b) is exact). The producer sub-lemmas S5a/b/c/(d,e) are orthogonal (built once,
front-J' instance).

## Π-frame caveat — fully AVOIDED (Codex Q3 confirms)
The fresh-chart route (invoke `deepest_gauge_construction(B·Π, internal-front-J')`) computes the chart's
own frames for `B·Π` — Π is NEVER absorbed into an existing `QL`, so the "QL need not commute with Π"
caveat does not arise. Residual obligation: only that `B·Π` is a valid rank-r target with front pivot
(check (1)/(3)) — which it is.

## Scope / what's banked vs new
- BANKED: `rlctAtOn_comp_homeomorph` (the MP germ-invariance, `S1Fubini.lean:54`), `deepest_gauge_construction`
  (reused for B·Π), `optimalSet`/`aoyagi_learning_coefficient` `⨅`-form (already global-min, choice-independent),
  the front-pivot chart where (b) is exact.
- NEW (B's cost): (1) front-pivot perm existence (routine LA), (2) the loss colPerm identity (mechanical),
  (3) τ_Π MP (coordinate permutation), (4) the `⨅`-transfer (iInf-over-bijection + the banked germ-invariance),
  (5) the one-line headline `rw`. NO new gauge-chart geometry.

## Net
**B is the deciding L2 (b) route — sound + decisively less Lean.** It reduces (b) to an EXACT equality
(front pivot) + a global MP-invariance transfer through the headline's existing `⨅ optimalSet` form,
avoiding A's unbuilt Pπ-telescope + FACT2. The Π-frame caveat is fully avoided by the fresh-chart route.
The producer's S5a/b/c/(d,e) coupled-𝓝 structure (hproducer-decomp-cert Part 2) is unchanged.

## Files
- `/tmp/b_verify.py` (the three exact B checks + caveat resolution). `codex/b-wlog-{prompt,answer}.md`
  (the decorrelated consult, B-decisive). The earlier A'-pointwise `hproducer-decomp-cert.md` is
  SUPERSEDED for the (b)-route (its Part-2 producer decomposition stands; the (b)-atom becomes exact).
