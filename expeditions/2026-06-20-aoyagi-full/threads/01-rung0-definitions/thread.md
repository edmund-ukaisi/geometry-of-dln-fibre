# Thread 01 — Rung 0: goal skeleton + foundational definitions

- **Type:** explore → design (pen-and-paper seat `pp`). **No Lean** in this thread.
- **Status:** in-progress. **Reports to:** controller.
- **Why first / why it matters:** every later rung stands on these definitions. Conceptual slop here
  (a definition that compiles but denotes the wrong invariant) poisons the whole tower and is exactly
  what a green build cannot catch. Get the *math* of the definitions exactly right, faithful to Aoyagi
  Definition 1, and cross-checked against numerical ground truth, before any Lean is written.

## Controller's architecture (the seat completes & pressure-tests this; flag any infidelity)

**(a) Parameter space + loss.** Widths `H : Fin (L+1) → ℕ`; layer `s : Fin L` is a matrix
`Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`; `prod` = the matrix product; parameter space ≅ ℝ^N,
`N = Σ_s H_s·H_{s+1}`. `dlnLoss B A = ∑_{i,j} ((prod A − B) i j)²` (square-Frobenius). 
`optimalSet H B = { A | prod A = B }` (the fibre). (Aoyagi's input-covariance Σ_X≻0 drops out via
Lemma 1 — record this, don't carry Σ_X.)

**(b) `rlctAt` (the crux — Aoyagi Def 1).** For `F : ℝⁿ → ℝ` and a point `w*`:
`rlctAt F w* = sSup { c : ℝ≥0 | ∃ U ∈ 𝓝 w*, IntegrableOn (fun w ↦ |F w|^(−(c:ℝ))) U volume }`
(value in ℝ≥0∞). The set of admissible `c` is a down-set; the sup is the threshold. Equivalent to the
bump-function version of Def 1 for the sup (a bump is sandwiched between positive multiples of `1_U`).
**Faithfulness to check:** φ-independence; that this matches Def 1's "largest pole of the zeta
function" reading; measure-zero handling where F=0.

**(c) `rlctOrderAt` (θ — secondary, analytically harder).** Order of the largest pole of
`z ↦ ∫_U |F|^z φ` at `z = −λ`. Design it faithfully; if the analytic definition is disproportionate,
note the fallback: land the combinatorial `θ = a(ℓ−a)+1` and name the analytic-multiplicity seam.

**(d) `aoyagiλ` (total, robust).** Define the singular core via the **minimisation**, total by
construction: `2·λ_core(M) = sInf { Mval(T) : T admissible }`, where
`Mval(T) = (M¹−t¹)(M²−t¹) + Σ_{j=2}^L (t^{j−1}−t^j)(M^{j+1}−t^j)` and "admissible" = Aoyagi's Def-4
partial-order constraints (pin the exact predicate: the `H_1 ≥ … ≥ H_ℓ = 0`, `S_1<…<S_{ℓ+1}`,
`H_j ≤ M^{S_{j+1}}` reparametrisation, p.22). Full `aoyagiλ H r = [−r²+r(H¹+H^{L+1})]/2 + λ_core(M)`,
`M^{(s)} = H^{(s)} − r`. Then **prove `λ_core = ½(Σ_{i}qᵢ² − Σ_k mₖ²)`** (clean form; `q` = balanced
ℓ-split of `P = Σ mₖ`, `m` = the relevant set) **and** `= ` Aoyagi's printed Theorem-2 expression where
Def 3 selects a set. (Handles the Def-3 ill-definedness trap by making the *definition* the
always-total minimisation.)

**(e) S2 — the ONE cited interface (chart-level normal-crossing → RLCT).** Target shape: if a
neighbourhood of `w* ∩ {F=0}` is covered by finitely many charts `φ_i : V_i → U_i` with
`F(φ_i u) = unit_i(u)·u^{2k_i}` and `|det Dφ_i(u)| = unit'_i(u)·u^{h_i}` (monomial×nonvanishing), then
`rlctAt F w* = min_i min_j (h_{i,j}+1)/(2k_{i,j})` (and the order is the max count achieving it).
**Pin the minimal faithful hypotheses** (what "cover" must mean, properness/measurability, the bump) so
that R1 can *feed* it and the cited content is exactly the irreducible monomial-integral fact — nothing
more, nothing less.

**(f) Goal skeleton.** `theorem aoyagi_learning_coefficient (H r B) (hB : B.rank = r) :
(⨅ w ∈ optimalSet H B, rlctAt (dlnLoss B) w) = (aoyagiλ H r : ℝ)` — plus the named-statement
placeholders for S1, S2(cited), L1, L2, D1, R1, A1, A2 that assemble into it.

## Tasks for the `pp` seat

1. Read `brief.md`, Aoyagi Def 1 + the resolution/arithmetic pages (paper 2023 pp.5–6, 14–27), and
   confirm/repair each definition above against the *source* (page images where `M^{(s)}` vs `M(S)` or
   pole-order subtleties bite). Produce `design-spec.md` (in this thread dir): each definition
   Lean-ready (precise type + content), the S2 hypotheses pinned, the admissible-vector predicate pinned,
   the goal skeleton with every named statement.
2. **Cross-check against numerical ground truth** (we have λ/θ for L2 (2,2,2)=3/2,1; (2,1,2)=1,2;
   (1,2,2)=1,2; L3 (2,2,2,2)=3/2,3; etc.): does `aoyagiλ` (via the minimisation) reproduce them? Does the
   clean form = printed form on these? Report a table.
3. **Pin the Def-3 regime:** characterise exactly when Def-3 selects a unique relevant set, and confirm
   the minimisation `λ_core` is well-defined and equals the clean form everywhere (independent of Def 3).
4. Fire a **decorrelated `local-codex-consult`** (highest effort) on the *faithfulness* of the `rlctAt`
   and `rlctOrderAt` definitions to Aoyagi Def 1 / standard RLCT theory — does the integral-sup def match
   the zeta-pole def; is the chart-level S2 statement the standard, correctly-hypothesised one. Report
   where Codex agrees/disagrees (and judge its algebra independently).
5. Flag honestly any definition you could not make both faithful and Lean-ready, with the specific
   obstruction.

**Output:** `design-spec.md` + a tight summary to the controller. No Lean. Scratch in /tmp. Commit to
your worktree branch; controller merges. Do NOT edit other repo files; do NOT write to `~/.claude`
global memory (in-repo only).
