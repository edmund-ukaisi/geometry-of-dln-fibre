# Review — S1-good "plan (A)" decomposition (F + D bricks) — VERDICT: CONTRACT-SOUND

**Reviewer** (fidelity + vacuity red-team), aoyagi-full Stage 2, `genm-sj5-domination`. **Date:** 2026-07-13.
**Target:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeeperFlagCore.lean` (MODIFIED working tree, green —
`scripts/lb DLNFibre.…RouteMSJDeeperFlagCore` exit-0, 8367 jobs). READ-ONLY on Lean/git. Decorrelated
Codex (xhigh, my conclusion withheld): `codex/s1A-decomposition-{prompt,answer}.md` — CONCURS on all six
points.

**Verdict: CONTRACT-SOUND.** The two brick statements (`exists_headSplitFrame` = F, `headSplit_domination`
= D) are each a TRUE, non-vacuous, cert-faithful correct-statement `sorry`; F's output tuple is passed
verbatim as D's frame hypotheses and they genuinely compose to a true `deeperFlag_spineToCore`; the
headline fold is sound; `hpos` is genuinely proved; the axiom footprint is exactly as expected.
**Integrate + spawn the F/D tides** — with the two proof-obligation notes below carried into the D
contract (they are proof guidance, NOT statement repairs).

## What was verified

**1. F↔D interface — semantically matched, not merely type-compiling (CONFIRMED).** F is called
(assembly l.706) with `X = Params (redChain (t+j) M)`, `M₂ = dropHead(redChain (t+j) M) 0 = M 2`,
`n = dropHead(…)(Fin.last L) = M_last`, `m = min(M 1)(M_last) − j`, `ε' = ε/√(M₁·M₂)`,
`Zdeep = deeperFlagZdeep M (t+j)`. Every element of F's output tuple — types of `Zf`/`U_sf`, `hUs`
(orthonormality), `hrank` (`m ≤ rank`), `hfloor` (PSD floor at `ε'`), and crucially the good-set clause
`weakEigCount ε' (Zdeep z) ≤ M₂ − m → Zf z = Zdeep z` — matches D's frame hypotheses **exactly** (D
l.522–534). The good-set threshold is the correct encoding of "≥ m singular values of `Zdeep` are ≥ ε'"
(among M₂ Gram eigenvalues, ≤ M₂−m below ε'² ⟺ ≥ m at/above). D's internal Ky-Fan derivation
(`σ_i(A₀ Zdeep) ≤ σ_1(A₀) σ_i(Zdeep)`, `σ_1(A₀) ≤ √(M₁M₂)` on the box) lands in **precisely** this
condition on the shell for `j < r`, and `hagree` converts it to `Zf = Zdeep`. `m`, `ε'`, `M₂`, `n` agree
across F and D via the assembly. Codex Q3/Q6 concur (count arithmetic checked).

**2. F non-vacuity + cert-faithful (CONFIRMED, matches s1-spine-headsplit §B.3).** The three ∀z conjuncts
(rank ≥ m, PSD floor, agreement) are jointly satisfiable by the intended piecewise construction: on
`G`, `Zf = Zdeep` (rank ≥ m and floor from the top-m spectral frame, since z∈G ⟺ ≥ m eigenvalues ≥ ε'²);
off `G`, fixed full-rank `V` + fixed `U_s0`, with the agreement implication **vacuously true** (false
antecedent). `hmM₂ : m ≤ M₂` and `hmn : m ≤ n` are exactly what the off-G fixed `V`/`U_s0` need. The
measurable m-frame is Borel functional calculus (`𝟙_{[ε'²,∞)}` Borel) — genuine labour, true. Codex
Q1/Q2 SOUND.

**3. D non-vacuity + cert-faithful (CONFIRMED).** `hpiv : minAdm(redChain (t+j) M) ≤ (t+j)·tailMinWidth M`
is **exactly** the pivot-admissibility gate `minAdm(M') ≤ u·ρ` the `s1-Chle` cert §4/§6 requires for
`C_hle < ⊤` (`redChain u M = (u, M₂,…,M_last)` drops M₁; `tailMinWidth M = min(M₁,…,M_last) = ρ`). It
correctly EXCLUDES the cert's unsound witness `M=(3,3,4,4)` at `u=2`: `minAdm(2,4,4)=7 > 2·min(3,4,4)=6`,
so `hpiv : 7 ≤ 6` is false (Codex independently recomputed the (2,4,4) recursion candidates 8,7,8 →
minAdm=7). It is SATISFIABLE at the anchor `(3,3,3)@u=2`: `minAdm(2,3)=6 = 2·3` (marginal equality). The
clean data `k=![1]`, `jc=![minAdm−1]`, `d=1` gives `monomialThreshold = ½·minAdm` (assembly `hbeta`,
equality), consistent with the cert. Codex Q5 SOUND.

**4. Assembly soundness (CONFIRMED, not gerrymandered).** D's conclusion `shellSpineIntegrand ≤ C_hle ·
deeperFlagCoreIntegrand (k=![1], jc=![minAdm−1])` is passed directly as S1's `hle` clause (`?_ … hdom`);
`k`/`jc` match. The headline `deeperFlag_shell_le` fold `C := C_hle · C_L1` is a clean
`mul_le_mul_left' hcore` + `mul_assoc.symm`, with `ENNReal.mul_lt_top hChle hCfin`; L1 is consumed at the
rescaled floor `ε'` (`hε'` passed as L1's `hε`), `cornerComparator_adm` supplied from `hd`/`i₀`/`hbeta`.

**5. `hpos` honest (CONFIRMED — clean-three verified).** `deeperFlagCore_decLoss_pos_ae` is genuinely
proved: `decLoss v z = |v 0|²·frobSq(prod(redChain u M) z)`, `|v 0| ≠ 0` a.e. ({0} null), and
`frobSq(prod z) ≠ 0` a.e. via `corePoly ≠ 0` (all reduced widths ≥ 1, where `ht1` is load-bearing:
`redChain u M 0 = t+j ≥ 1` — the t=j=0 fix flagged by the prior review) pulled back along the
measure-preserving `paramsEquivFlat`. Not a disguised assumption.

**6. Axiom footprint (VERIFIED via forced-elaboration `#print axioms`, not build exit-0):**
- `exists_headSplitFrame` (F): `[propext, sorryAx, Classical.choice, Quot.sound]` ✓
- `headSplit_domination` (D): `[propext, sorryAx, Classical.choice, Quot.sound]` ✓
- `deeperFlagCore_decLoss_pos_ae`: `[propext, Classical.choice, Quot.sound]` — CLEAN-THREE ✓
- `deeperFlag_shell_core_le` (L1): `[propext, Classical.choice, Quot.sound]` — CLEAN-THREE ✓
- `deeperFlag_spineToCore` (assembly): `[propext, sorryAx, Classical.choice, Quot.sound]` — carries
  sorryAx (transitively via F, D)
- `deeperFlag_shell_le` (headline): `[propext, sorryAx, Classical.choice, Quot.sound]` — carries sorryAx

## Proof-obligation notes for the D tide (guidance, NOT statement defects)

- **D must branch at the saturated shell `j = r`.** The shell⊆G containment holds only for `j < r`
  (where `weakEigCount ε Z_full = j` exactly). At `j = r`, `u = min(M₀,M₁)`, so `(a,b) = ((M₀−M₁)₊,
  (M₁−M₀)₊)` and `min(a,b) = 0` (empty corank block if `b=0`, or zero corner exponent if `a=0`) — the
  corank weight is then identically 1 regardless of `Z_deep`'s rank, so containment is NOT needed there.
  D's proof MUST use this degeneration at `j = r` and MUST NOT assert the (false) containment there. The
  statement is TRUE across all `j ≤ r`; only the proof splits. (I initially suspected this was a
  soundness defect — a divergent LHS against a finite fake-`V` RHS — but `min(a,b)=0` defuses it; Codex
  Q4 independently confirmed both the defusion and the branch obligation.)
- **`C_hle` finiteness is per-exponent.** D asserts `∃ C_hle < ⊤` at the given `c'`; within the strict
  convergent range (`c' − ab/2 < u·ρ/2`, delivered by `hpiv` since `u·ρ ≥ minAdm(M')`) `C_hle` is
  genuinely finite. This is the same `∃ C < ⊤, LHS ≤ C·RHS` domination form as the already-PROVEN
  clean-three L1 (`deeperFlag_shell_core_le`), so no additional exponent hypothesis is required. D does
  not (and need not) assert a constant uniform up to the critical endpoint — the marginal-anchor
  equal-rate ratio (`s1-Chle` §4, Codex Q5 [INFERENCE]) is only relevant if a downstream consumer needs
  endpoint uniformity, which the mountain does not here.

## Precision findings (report-only, minor)

- **Module docstring (l.59–61) overclaims axiom-cleanliness of "the whole S1-good assembly".**
  `deeperFlag_spineToCore` (the assembly theorem) and `deeperFlag_shell_le` (headline) carry `sorryAx`
  (verified), because they `obtain` from F and D. Only L1, the S3 bricks, and
  `deeperFlagCore_decLoss_pos_ae` are genuinely clean-three. The phrasing conflates "no literal `sorry`
  in the assembly's own tactic block" with "axiom-clean" — the exact trap `lean/CLAUDE.md` flags (use
  forced `#print axioms`, not build exit-0). Suggest: state that F, D, and everything depending on them
  (`deeperFlag_spineToCore`, `deeperFlag_shell_le`) carry `sorryAx`; the clean-three results are L1 / S3 /
  `deeperFlagCore_decLoss_pos_ae`.
- **`AxCheck.lean` (~l.1213–1216) comment is stale.** It says `deeperFlag_shell_le` "carries a TRACKED
  sorryAx = exactly the one isolated (□)-rung `deeperFlag_spineToCore` (S1)". After plan (A) there are now
  TWO rungs (F + D), and `deeperFlag_spineToCore` is itself an assembly over them, not a leaf sorry.

## Bottom line

CONTRACT-SOUND. The F/D brick statements are the right two contracts; they compose faithfully to a true
`deeperFlag_spineToCore`, and the headline is a sound fold. Integrate and spawn the two dedicated tides,
carrying the `j = r` branch obligation into the D contract. The two precision findings are report-only
docstring/comment fixes (no signature change, no math change).
