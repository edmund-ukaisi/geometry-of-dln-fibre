# Fidelity review — (α) codim = minAdmRec (Finding B(2))

Reviewer: `genm-deepcodim-review` (controller-spawned, independent; deepatlasA is the tide author, no self-review).
Function: **fidelity** (report-only — no edit to the target module).

- **Target.** branch `origin/genm-deepatlas` @`7b006cb95`, module
  `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeepCodim.lean`, theorem
  `DeepAtlas.codimRepCanonical_productRankLocusLE_eq_minAdmRec`.
- **Card.** `expeditions/2026-06-20-aoyagi-full/threads/genm-deepatlas/statement-card-codim.md`.

## Verdict: SURVIVED — FAITHFUL

No fidelity defect. The Lean statement + hypotheses faithfully discharge Finding B(2) ("CRrec =
geometric κ_k") as a pure codimension equality over an algebraically closed char-0 field, with the
ℝ/ℂ residual named (not faked) and no analytic/RLCT content smuggled in. Independent decorrelated
Codex (gpt-5.6-sol, xhigh, conclusion withheld) concurred FAITHFUL on all five scrutiny points
(`codex/fidelity-answer.md`).

## The six scrutiny points

1. **Faithful assembly — OK.** The proof chains exactly the four named banked lemmas + `Int.toNat_natCast`,
   no vacuous/`sorry`-papered step. Goal-state trace:
   `codimRepCanonical (productRankLocusLE d r)`
   → `((cCodim d r h_dr).toNat : ℕ∞)` [`codimRepCanonical_productRankLocusLE_eq_cCodim_enat`]
   then `hkey : (cCodim d r h_dr).toNat = minAdmRec (dminus d r)` via
   `cCodim d r → cCodim (dminus d r) 0` [`cCodim_rankShift`, reversed]
   `→ (minAdm (dminus d r) : ℤ)` [`minAdm_eq_cCodim`, reversed]
   `→ minAdm (dminus d r)` [`Int.toNat_natCast`] `→ minAdmRec (dminus d r)` [`minAdmRec_eq_minAdm`],
   closes by rfl at `(minAdmRec (dminus d r) : ℕ∞)`. All four lemmas verified present with composing
   signatures (`Core/SigmaCodim.lean:101`, `Core/CTheta.lean:377`, `MinAdmCCodim.lean:315`,
   `RouteMLayerSplit.lean:395`).

2. **Hypotheses correct & roughly minimal — OK.**
   - `hN : 1 ≤ N` is **truth-necessary**, not proof-convenience: at `N = 0`, `d : Fin 1 → ℕ`,
     `mult` of the empty tuple is the `d₀×d₀` identity (rank `d₀`), so for `r < d₀` (allowed by `hr`)
     the locus is **empty** ⟹ `codimRepCanonical = ⊤`, while `minAdmRec` on `Fin 1` `= 0`. LHS `⊤` ≠
     RHS `0` — the equality is FALSE at `N = 0`. `1 ≤ N` correctly excludes this and keeps the geometric
     locus nonempty (the zero product gives rank `0 ≤ r`), so codim is finite.
   - `hr : ∀ i, r ≤ d i` is the admissible shifted-width range `r ∈ [0, min_i d_i]`; needed by
     `cCodim_rankShift` and equivalent to `kostantPartitions d r` being nonempty (`corner_le_dim_of_mem`).
     Slightly conservative — excludes `r > min_i d_i` (whole space, codim 0), which is honest scoping,
     not overclaim.

3. **ℕ∞ cast — OK.** Equality at `ℕ∞`, RHS a `Nat.cast`. LHS never `⊤` under the hypotheses (banked
   geometric lemma equates it to `((cCodim d r h).toNat : ℕ∞)` with `cCodim ≥ 0` banked). `r = min_i d_i`
   edge (`dminus` has a `0` entry, whole space): RHS `= 0` — eval-confirmed `minAdmRec (dminus d222 2) = 0`,
   matching whole-space codim `0`. No `⊤`/`⊥`/`0` slip.

4. **Residual honesty — OK.** Docstring + card name the **ℝ/ℂ codim bridge for this locus as UNBANKED
   residual** (a separate lane), co-located with the claim. Imports are all `Core`/combinatorial
   (`SigmaCodim`, `CTheta`, `CCodimCornerMono`, `MinAdmCCodim`, `RouteMLayerSplit`) — no analytic/RLCT
   module. Conclusion is `codimRepCanonical = minAdmRec` — pure codimension; **no `rlct = ½·codim`
   content**.

5. **Non-vacuity — OK.** In-file `example` at `d = ![2,2,2]`, `r = 0` (zero-product locus — a genuine
   proper subvariety). Eval-confirmed `minAdmRec (dminus d222 0) = 3` = Lehalleur–Rimányi's `C = 3`
   (`![2,2,2] r=1 → 1`, `r=2 → 0`). `codimRepCanonical` is `Ideal.height (vanishingIdeal …)` = codim of
   the Zariski closure; the rank-`≤r` locus is closed, so this is the genuine geometric codim.

6. **Axioms — force-fresh clean-three, INDEPENDENTLY VERIFIED.** Fresh worktree @`7b006cb95`, deleted
   the target olean and re-elaborated from source, then `#print axioms`:
   `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`/`Lean.ofReduceBool`.
   Full library build green (`3699/3699`). Confirms deepatlasA's assertion.

## Minor (out of fidelity scope — integration note for controller)
- Module is standalone (NOT aggregator-wired). My `scripts/lb <module>` invocation compiled the whole
  library (3699 jobs) **and** the module in the same run without a name clash, but that does not fully
  rule out an aggregator name-clash on wiring (the module is not imported by `DLNFibre.lean`). At
  integration: green-gate full `lake build DLNFibre` with the module wired, and add the theorem to
  `AxCheck.lean` for the standing force-fresh axiom guard.
