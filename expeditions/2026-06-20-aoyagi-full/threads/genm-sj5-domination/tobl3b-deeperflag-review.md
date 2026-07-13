# T-Obl3b `RouteMSJDeeperFlagCore` review — VERDICT: **DEFECT (broken-by-case t=j=0)**. L1 + S3 bricks + axiom footprint CLEAN; S1's statement is a wrong-statement sorry — fix before integrating.

**Seat:** reviewer (fidelity + vacuity red-team), aoyagi-full Stage 2. **Date:** 2026-07-13.
**Target:** `lean/DLNFibre/DLN/RLCT/Validate/RouteMSJDeeperFlagCore.lean` (green, 1 sorry = S1).
READ-ONLY on Lean. Build re-run green (8363 jobs, exit 0; sole `sorry` warning at the S1 decl).
Axiom footprint verified by force-elaborated `#print axioms`. Decorrelated Codex consult fired
(xhigh, my conclusions withheld): `codex/tobl3b-deeperflag-review-{prompt,answer}.md`.

---

## ★ The defect (state it LOUDLY)

**`deeperFlag_spineToCore` (S1) is FALSE at `t = j = 0`** (more generally whenever `t + j = 0`),
so the isolated sorry is a **wrong-statement sorry** — the case the sorry gate says to fix first.

Mechanism (verified in Lean, `/tmp` scratch, both facts green):
- `redChain u M 0 = u` by `rfl` — the residual chain's LEADING width is the cut value `u = t+j`,
  NOT the freed-corner height `M 0 − u`.
- At `u = 0` the comparator's generator index type `ι = Fin (redChain 0 M 0) × Fin (redChain 0 M last)
  = Fin 0 × _` is **empty**, and `SJDecoration.decLoss = carrier.loss = ∑_{i : ι} (gen)² = 0`.
  Confirmed: `(cornerComparator (![0,1]) k jc).decLoss v z = 0` for all `v, z`.
- S1's existential body carries the conjunct
  `hpos : ∀ᵐ z ∈ paramsBoxM (redChain u M) 1, ∀ᵐ v ∈ unitBox d, 0 < (cornerComparator …).decLoss v z`.
  With `decLoss ≡ 0` this is `∀ᵐ z, ∀ᵐ v, 0 < 0`, i.e. `∀ᵐ, False`, which needs a null a.e. filter —
  but `volume.restrict (paramsBoxM (redChain 0 M) 1)` and `volume.restrict (unitBox d)` (`d ≥ 1` by
  `hd`) both have positive total measure. So `hpos` is **unsatisfiable for every choice** of
  `M₂,m,n,d,k,jc,Zf,…` (the empty-`ι` loss is 0 regardless of `k,jc,d`). The ∃ is therefore FALSE.
- Witness `(t,j)`: `ht : t ≤ min(M0)(M1)` and `hj : j ≤ min(M0−t)(M1−t)` both admit `t = j = 0`
  for **any** `M` (e.g. `M ≡ 1` on `Fin 4`), so the false instance is always reachable.

**Root cause:** S1 (and the headline) omit the lower bound **`1 ≤ t`** that the real spine cut carries
(`RouteMSJDecoratedPeelStep.innerCorankDescent_lt_top` takes `ht : 1 ≤ t`; the front cover
`sjBoundaryPeel` sums `t` from 1). The prose already says "at a legal binding cut `t★`" (binding cuts
are ≥ 1) — the bound was dropped from the hypotheses only.

**Minimal repair:** add `(ht1 : 1 ≤ t)` to BOTH `deeperFlag_spineToCore` and `deeperFlag_shell_le`
(the headline inherits the defect — it takes the same `ht/hj` and destructures S1). Then `u = t+j ≥ 1`,
so `redChain u M 0 = u ≥ 1`, `ι` nonempty, and (with positive layer widths) `hpos` becomes satisfiable.
Secondary caveat: if a DEEP layer can have width 0 (`M i = 0`, `i ≥ 2`), `prod (redChain u M) ≡ 0` even
for `u ≥ 1`, again killing `hpos`; in-context all `M i ≥ 1`, but the controller may want to state that
(or `1 ≤ minAdm (redChain u M)` / a nondegeneracy hyp) explicitly.

## Decorrelation note (Codex reached the same verdict via a flawed instance — I corrected it)

Codex independently concluded "S1 false as stated" and identified the same mechanism (empty-product ⟹
`hpos` impossible). BUT its exhibited instance `t=1, j=0` is WRONG: it conflated the freed-corner dim
`M0−u = 0` with the residual leading width `redChain 1 M 0 = u = 1`. At `u = 1` the residual chain is
`(1,1,1)`, `prod` is a scalar product NOT identically zero, and `hpos` IS satisfiable — so Codex's stated
instance does not break S1. The genuine failing instance is `u = 0` (`t=j=0`), which I pinned and
verified in Lean. Verdicts converge; the arithmetic was decorrelated-corrected.

---

## What SURVIVES (clean — these are not the problem)

**1. L1 `deeperFlag_shell_core_le` — FAITHFUL, non-vacuous, non-circular. CONFIRMED.**
- `deeperFlagCoreIntegrand` is the GENUINE off-sector-core: its inner `∫_{A_cor∈matBox (M1−u) M₂ 1}
  ∫_{Γ∈sΓf z} (decLoss v z + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'}` is EXACTLY what
  `shell_corankOffSector_le_unif` bounds (`w := decLoss v z` the real pivot energy). NOT gerrymandered
  to match the RHS: the LHS inner is an `A_cor,Γ` double integral of `(w+frobSq)^{−c'}`; the RHS is
  `(w)^{−(c'−ab/2)}` with NO `A_cor,Γ` — genuinely different objects, with the freed-corner-peel +
  PSD-weak-elimination + strong-block-finiteness content between them.
- `w := decLoss` is legitimate: `cornerComparator_decLoss` proves
  `decLoss v z = commonDivisor(v)²·frobSq(prod (redChain u M) z)` — the real pivot energy.
- `∃ C < ⊤` is genuine: `C = deeperFlagUnifConst …`, finite by `deeperFlagUnifConst_lt_top` in the
  convergent regime `a < m−b+1` (NOT the vacuous `C = ⊤`).
- The RHS `.integral` matches the collapsed integral **definitionally** — `SJDecoration.integral D e
  = ∫_z ∈ D.dom, ∫_u ∈ unitBox D.d, ofReal((∏|u|^{D.jac}) · (D.decLoss u z)^{−e})` unfolds, for
  `D = cornerComparator (redChain u M) k jc`, to L1's collapsed target (`D.dom = paramsBoxM (redChain u M)
  1`, `D.d = d`, `D.jac = jc`). The final `le_refl` typechecks (green build). This is the standard
  decorated integral the decorated IH controls — the correct RHS.

**2. `hpos` — an HONEST a.e. side-condition (in the intended `u ≥ 1` regime).** `{decLoss = 0}` is a
genuine null set when `prod (redChain u M)` is not identically zero (coordinate-hyperplane monomial
zeros ∪ a proper algebraic subvariety). It is NOT a disguised assumption of the conclusion (the
conclusion is a domination, not a positivity). Its unsatisfiability at `u = 0` is precisely the S1
defect above, not a flaw in `hpos` as a hypothesis of L1 (L1 itself is sorry-free and honest).
Refinement (Codex Q2, concur): honest **under nondegeneracy** — the missing guard is exactly `1 ≤ t`.

**3. Non-vacuity of S1 in-regime is fine (once `1 ≤ t` is added).** L1 caps
`deeperFlagCoreIntegrand ≤ C · comparator.integral(e)` whenever S1's constraints (incl. `hconv`) hold,
so the "degenerate RHS = ⊤" escape is blocked **whenever `comparator.integral(e) < ⊤`** — which the
downstream decorated IH supplies below threshold (`cornerComparator_adm` + `flagShift_lt_carrierThreshold`).
Codex Q3(a) correctly refines: `C < ⊤` alone does NOT give `C · I < ⊤` when `I = ⊤`; so S1's
non-vacuity is CONDITIONAL on the comparator being finite (downstream IH), and vacuous above threshold.
The headline's `hc'` regime + the recursion's `c' < carrierThreshold` keep it in-regime. Constraint
consistency (`hconv` jointly with `hbm, hmM`, shell PSD/rank) holds via existential freedom over
`M₂,m,n` (Codex Q3(b): `m = M₂ = n = a+b`, `U_sf = I`, `Zf = εI` ⟹ `a < m−b+1 = a+1`, shell PSD = 0).

**4. FIDELITY of the headline `deeperFlag_shell_le` — CONFIRMED (modulo the boundary defect).**
- LHS = the LITERAL spine integrand: `shellSpineIntegrand M (t+j) κ ε (min(M0−t)(M1−t)) ⟨j,_⟩ c'` is the
  `innerCorankDescent` freed-Γ triple **verbatim** (`freedSchurLoss` / `outerDom` / `schurShift` /
  `genBox` / `blockSplitEquiv` / `prod (tailChain M)` — the real spine objects), at cut `u = t+j`, with
  the outer domain `paramsBoxM (tailChain M) 1` INTERSECTED with `{A' | prod (tailChain M) A' ∈
  singularShell ε r ⟨j⟩}`. A subset restriction of the genuine integrand — NOT a convenient reshape.
  (Caveat, correctly scoped by the certs: the link from the actual hole `innerCorankDescent` at cut `t`
  to `∑_j shellSpineIntegrand` at cuts `t+j` is the shell-cover assembly — future work, not in this file.)
- RHS = the comparator reduction with the comparator ADMISSIBLE via `cornerComparator_adm` (real: needs
  `hd, hbeta`, both genuinely supplied). Exponent bookkeeping correct: `peelCharge M u = (M0−u)(M1−u)`,
  matching `shell_corankOffSector_le_unif`'s `−(c'−ab/2)`.
- Composition `S1 ∘ L1` sound: the intermediate `deeperFlagCoreIntegrand M (t+j) k jc Zf Ccrossf sΓf c'`
  is IDENTICAL in S1's output and L1's input (`hle.trans hcore` typechecks; note `deeperFlagCoreIntegrand`
  takes `Zf Ccrossf sΓf`, not `U_sf` — matches).

**5. Axiom footprint — CONFIRMED (forced `#print axioms`).**
- `[propext, Classical.choice, Quot.sound]`: `strongBlock_lintegral_le_unif`,
  `strongBlock_unif_const_lt_top`, `shellCorankWeight_le_unif`, `deeperFlagUnifConst_lt_top`,
  `shell_corankOffSector_le_unif`, `deeperFlag_shell_core_le` (L1).
- `[propext, sorryAx, Classical.choice, Quot.sound]`: `deeperFlag_spineToCore` (S1),
  `deeperFlag_shell_le` (headline). Exactly one `sorryAx`, isolated to S1 as claimed.

---

## Recommendation

**Do NOT integrate as-is.** The isolated sorry is a wrong-statement sorry (false at `t+j=0`). Route the
one-line fix — add `(ht1 : 1 ≤ t)` to `deeperFlag_spineToCore` and `deeperFlag_shell_le` (spine-faithful;
`innerCorankDescent_lt_top` already carries it) — then re-audit that the statement is satisfiable across
the corrected range (it is, per the certs' ADMITS mechanism for `1 ≤ j` binding cuts + existential
freedom at the `j=0` borderline). After the fix the module is a sound tracked isolated (□)-rung: L1, the
S3 bricks, the headline structure, and the axiom footprint are all clean.
