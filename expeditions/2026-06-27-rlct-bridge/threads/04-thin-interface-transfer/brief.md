# Thread 04 — Wave 1a: thin cited interface + expose the transfer T

**Type:** lean-formaliser (tide). **Base:** `origin/dev` (= `e2fbf7fb`); branch
`expedition/rlct-bridge-04-thin-interface`. **Cross-base (L2):** the controller's recon commits are
docs-only — no Lean delta — so no merge of `expedition/rlct-bridge` needed; branch clean from
`origin/dev`.

## The quest this serves

Replace the monolithic Cited axiom `RlctInterface.cited_aoyagi_dln` (`rlct(lossDLN) = ½·codim mult⁻¹(B)`)
with a **thin cited analytic interface + genuinely-proved DLN geometry**. This tide builds the SCAFFOLD
into which the upper bound (R2), lower bound (R3), and transfer (T) land.

## Ground truth (verified by controller grep — do NOT assume more)

- The monolith: `structure RlctInterface` at `lean/DLNFibre/DLN/RlctPayoff.lean:288`, carrying an opaque
  `rlct : (Tuple (k:=ℝ) d → ℝ) → ℝ` (line 291) + the single field `cited_aoyagi_dln` (line 297):
  `∀ B r, 0<N → B.rank=r → r≤… → rlct (lossDLN d B) = ((codimRepCanonical (fibre (k:=K) d (B.map ι))).toNat : ℝ)/2`.
- Downstream consumers (must keep compiling, re-derived from the new interface):
  `rlct_lossDLN_zero_eq_half_codimFibre_via_aoyagi` (311), `…_iInf_orbitCodim_via_aoyagi` (323),
  `…_cCodim_via_aoyagi` (339), `rlct_lossDLN_d222_zero_eq_three_halves_via_aoyagi` (373);
  `RlctPayoffGeneral.lean` (`rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi`, line 120) and
  `BundleShiftDischarge.lean`.
- **There is NO `monomial_rlct`, NO `aoyagiLambda`, NO resolution/Skeleton scaffold.** The analytic side
  is greenfield. (Banked geometry you DO build on: `codimRepCanonical`, `cCodim`,
  `Aoyagi.lambda`/`codimRepCanonical_fibre_eq_two_aoyagiLambda` = the proved `codim = 2λ` formula-match,
  `realizerD` + `codimRepCanonical_orbitRankLocus_realizerD` in `Core.ThetaComponentCount`/`ClosureBridge`.)
- **The trap to delete:** `RlctInterface`'s docstring lines 267–272 say *"No from-scratch real↔complex
  codimension base-change lemma is needed."* That is the hidden transfer T. Exposing it is the point.

## Target (this tide)

1. **`ThinRlctInterface`** — carries the opaque `rlct` map + the GENERAL cited analytic theorems as named
   fields (true for all functions, each cited to its source), NOT the DLN equality:
   - **C1** rlct of the standard nondegenerate quadratic: `rlct (fun x ↦ ∑_{i<c} (x i)²) = c/2` (Watanabe;
     the smooth-block value). State at the precise generality you can use downstream.
   - **C2** Watanabe universal upper bound: `rlct (∑ fᵢ²) ≤ ½·codim_ℝ(zero-set)` (cite Lin/Watanabe).
   - **C3** monomial-extraction / resolution lower bound: given a normal-crossing log-principalization
     datum of the loss IDEAL with divisor data `(kⱼ,hⱼ)`, `rlct ≥ ⨅ⱼ (hⱼ+1)/(2kⱼ)` (the log-canonical /
     Varchenko inequality). NB: of the IDEAL, not the set (R0: the set-only form is FALSE).
2. **The transfer T — EXPOSED, proved if reachable.** The DLN equality currently fuses the analytic rlct
   over ℝ with `codimRepCanonical` over alg-closed `K`. Factor it: `rlct(real loss) = ½·codim_ℝ(real
   fibre)` (analytic, from C1/C2/C3) and `codim_ℝ(real fibre) = codimRepCanonical(fibre over K)` (the
   transfer T). **Prove T via the rational `realizerD`** (each top-dim minimising component has a rational
   ∴ real point ⟹ real points Zariski-dense ⟹ dims agree) IF reachable; if it hits genuine new
   real-algebraic-geometry depth, make T an EXPLICIT named carried field `transfer_real_complex` (clearly
   "to be proved in rung T") — never re-bury it in a citation. Report the obstruction precisely.
3. **Compose** `cited_aoyagi_dln` as a DERIVED theorem from `ThinRlctInterface` + T + the banked geometry,
   with the upper bound (R2) and lower bound (R3) entering as EXPLICIT named hypotheses/inputs for now
   (so the cited boundary is honestly {C1,C2,C3,T?} + the R2/R3 holes, and the build stays green/sorry-free
   — R2/R3 fill in Wave 2). Re-derive ALL downstream theorems from the new interface; delete the
   "no base-change needed" docstring.

## Discipline / gates

- Green via `scripts/lb DLNFibre`, sorry-free (`scripts/sorries`), axiom-clean `#print axioms`
  (`[propext, Classical.choice, Quot.sound]` — NO new `axiom`; the cited content is STRUCTURE FIELDS, not
  global axioms, exactly as the current monolith).
- **name = content (L4, existential here):** no `rlct_…` theorem may assert `≥½codim`/the equality while
  secretly assuming C3 for a resolution it doesn't exhibit, nor bury T. Separate Proved / Cited; caveats
  next to claims. Each cited field's docstring names its source.
- **Report a DESIGN PROPOSAL first** (the exact field statements + T's proof status + the composition
  skeleton) in `thread.md` and to `main` BEFORE finalizing — the controller holds the seam taste and will
  review against bedrock. Then green-gate + commit on the thread branch and report.
- Commit + green-gate BEFORE reporting ready (L2). The controller integrates from worktree disk.
