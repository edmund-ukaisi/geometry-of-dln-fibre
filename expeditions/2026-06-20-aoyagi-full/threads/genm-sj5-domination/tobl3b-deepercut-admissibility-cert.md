# T-Obl3b deeper-cut admissibility cert — the (S,J) spine ADMITS peeling at the deeper binding cut `t★+j` per shell `S_j`; NO measure-disintegration wall

**Seat:** pen-and-paper OBSTRUCTION-vs-witness adjudication (labour-vs-wall determinant for the T-Obl3b
mountain), genm-sj5-domination, Stage 2. **Date:** 2026-07-13. **NO Lean, NO build.** Exact structural
reasoning over the REAL Lean defs of the spine (`def`/`theorem` signatures quoted below). Decorrelated
`local-codex-consult` (xhigh, my ADMITS conclusion WITHHELD — prompt framed "adjudicate either
direction"): `codex/tobl3b-deepercut-{prompt,answer}.md`.

**Consumed / read (defs, not re-derived):**
`RouteMSJDecoratedRec` (`DecoratedStepHyp`, `DecoratedBaseHyp`, `DecoratedDescent`,
`decoratedBoxThresholdFinite_of_decoratedStep`, `routeMBoxThresholdFinite_of_decoratedDescent`);
`RouteMSJDecorated` (`SJDecoration`, `SJDecoration.integral`, `DecoratedBoxThresholdFinite`,
`carrierThreshold`, `carrierThreshold_shift`, `SJDecoration.trivial`,
`decoratedBoxThresholdFinite_trivial_iff`); `RouteMLayerSplit` (`redChain`, `minAdm`, `minAdmRec`);
`RouteMSJShellCharge` (`freedCorner_eq_peelCharge`, `deeperCut_le`, `flagCharge_ge`,
`flagShift_lt_carrierThreshold`); `RouteMSJShellCover` (`singularShell`, `singularShell_iUnion`,
`lintegral_le_sum_finCover`, `weakEigCount`); `RouteMSJCornerComparator` (`cornerComparator`,
`cornerComparator_decLoss`, `cornerComparator_adm`, `exists_cornerComparator_adm`);
`RouteMSJResolution` (`sjBoundaryPeel`, `gammaPeelIntegral`, `routeMLayerBoxIntegral_front_split`,
`eFront`); `RouteMSJDecoratedPeelStep` (`innerCorankDescent_lt_top`, `gammaPeelIntegral_lt_top_of_descent`,
`decoratedPeelStep_proof`); the just-delivered `tobl3b-cornershift-chart-cert.md` (the corrected
mechanism whose one open question this cert settles) + `tobl3b-reformulation-cert.md` §3.

---

## ★ VERDICT — ADMITS. State it LOUDLY.

**The (S,J) T-peel spine ADMITS peeling at the DEEPER binding cut `t★+j` on shell `S_j`.** The cut is
NOT fixed by the recursion's structure — it is a FREE per-shell parameter the step's proof instantiates.
No measure-disintegration theorem is required: the deeper-cut re-peel is realisable entirely from banked
pieces + the OWED analytic labour (OWED-1/2/3 of the cornershift cert). **This turns the T-Obl3b mountain
into LABOUR, not a wall.** Confidence HIGH; decorrelated Codex concurs at 99% (§7).

The verdict rests on THREE structural facts of the ACTUAL Lean spine, each a `def`/`theorem` signature:

**FACT I — the recursion descends by ARITY, and `redChain t M` drops ONE layer for EVERY cut `t`.**
```
def redChain (t : ℕ) (M : Fin (L+1+1+1) → ℕ) : Fin (L+1+1) → ℕ :=
  Fin.cons t (fun i : Fin (L+1) => M i.succ.succ)      -- = (t, M₂, …, M_L)
```
`redChain t M : Fin (L+1+1) → ℕ` — arity `L+1+1`, one less than `M`'s `L+1+1+1` — for **ALL** `t`. The
cut value only sets the new leading width. So `redChain (t★+j) M` is a valid one-shorter chain for
**every** `j` (`0 ≤ j ≤ r`), all of the SAME arity.

**FACT II — the step's IH is UNIVERSALLY quantified over one-shorter chains (and admissible decorations).**
```
def DecoratedStepHyp (adm …) : Prop :=
  ∀ (L) (M : Fin (L+1+1+1) → ℕ),
    (∀ (M' : Fin (L+1+1) → ℕ) (D' : SJDecoration M'), adm (L+1) M' D' → DecoratedBoxThresholdFinite D')
    → ∀ (D : SJDecoration M), adm (L+1+1) M D → DecoratedBoxThresholdFinite D
```
The IH `(∀ M' D', adm → DecoratedBoxThresholdFinite D')` ranges over **every** one-shorter chain `M'`
and **every** admissible decoration `D'`. Nothing in the driver
(`decoratedBoxThresholdFinite_of_decoratedStep`, plain arity `Nat.strong_induction_on`) restricts a step
invocation to a SINGLE reduced chain. Combined with FACT I: the IH may be instantiated at
`redChain (t★+j) M` **independently for each `j`, within ONE step invocation** — a different reduced chain
per shell, all legitimately in scope. This is the decisive structural fact.

**FACT III — the freed corner `Γ` is a LIVE integration variable in the hole; the corner charge is NOT
yet committed.** The per-chart integral the spine actually operates on (`innerCorankDescent_lt_top`,
after the banked Schur-weld+shear `gammaPeelIntegral_schurShearFree_eq`) is the freed-`Γ` TRIPLE integral
```
∫_{A' ∈ paramsBoxM (tailChain M) 1}          -- OUTER: A' produces the deep product Z = prod(tailChain M)A'
  ∫_{x ∈ outerDom t (M₀−t) (M₁−t) 1}
    ∫_{Γ ∈ {Γ | Γ + schurShift x ∈ genBox …}}  -- the freed (M₀−t)×(M₁−t) corner, STILL AN INTEGRAND
      (freedSchurLoss x Γ ((prod (tailChain M) A').submatrix (blockSplitEquiv κ) id))^{−c'}
```
`Γ` is un-integrated — the corner-charge `½(M₀−t)(M₁−t)` is a Gaussian integral that has NOT been
evaluated. So the spine has **NOT committed to the full `a×b` corner peel**: within the hole the proof is
free to re-organise the `Γ`/corank-block integral per shell (a sub-corner Gaussian peel + PSD elimination
at the deeper cut) — exactly the "stratify `Z` FIRST, peel at `t★+j` per shell" order the cornershift
cert requires, and the opposite of the divergent "peel full `a×b` at `t★` then stratify."

---

## 1. The cut is a FREE parameter — the exhibited cut-choice mechanism (gating OWED-3)

The step must prove `DecoratedBoxThresholdFinite D` = `∀ c' < carrierThreshold M, D.integral c' < ⊤`,
which admits ANY valid proof. The admissible per-shell deeper-cut proof, entirely from banked structure:

**(0) Front cover fixes the front cut `t★` as ONE term.** `sjBoundaryPeel M c' hc'` bounds the box
integral by `∑_{t=1}^{min(M₀,M₁)} ∑_{ρ,κ} gammaPeelIntegral M t ρ κ c'` (banked). The binding cut `t★`
(from `sjChargeBudget_binding`/`exists_binding_cut`) is one term `t = t★`; finiteness of the OTHER terms
is the same argument at a different `t`. So the labour is: `gammaPeelIntegral M t★ ρ κ c' < ⊤`.

**(1) Shell-stratify the OUTER `A'` (banked, measurability-FREE).** In the hole's `∫_{A'}` integral,
apply
```
lintegral_le_sum_finCover (S := singularShell ε r) (hcov := singularShell_iUnion ε r) :
  ∫⁻ A' in box, F A'  ≤  ∑_{j : Fin (r+1)} ∫⁻ A' in singularShell ε r j, F A'
```
where `singularShell ε r j = {Z | min (weakEigCount ε Z) r = j}` pulled back along
`A' ↦ prod (tailChain M) A'` (an exhaustive cover of the `A'`-domain, `singularShell_iUnion = univ`).
**No shell need be measurable** (`RouteMSJShellCover` docstring; `lintegral_mono_set` +
`lintegral_union_le` are measurability-free). The shell restriction stays in the ORIGINAL tail
coordinates `A'` — the measure is NEVER pushed forward onto `Z`.

**(2) On shell `S_j`, peel at the deeper cut `u = t★+j` — the cut CHOICE, banked charge.**
`deeperCut_le` (`t★+j ≤ min(M₀,M₁)` for `j ≤ r`) makes `u` a legal cut;
`freedCorner_eq_peelCharge` (`(M₀−t★−j)(M₁−t★−j) = peelCharge M (t★+j)`) and
`flagCharge_ge` (`minAdm M ≤ (M₀−t★−j)(M₁−t★−j) + minAdm (redChain (t★+j) M)`) bank the charge; the
deeper-cut Gaussian sub-corner peel frees a `(M₀−t★−j)×(M₁−t★−j)` corner (charge `½(a−j)(b−j)`), and
PSD-monotonicity (`det_le_det_of_posSemidef_sub`, generalising `uniformWenn_le`) eliminates the `j` weak
`Z`-directions with a uniform `ε^{−(a−j)(b−j)}` factor. **This is where OWED-1/OWED-2 land** (cornershift
§5: `uniformWenn_proj_le`, `strongBlock_lintegral_lt_top` — the reduced weight at shrunk dims
`(a−j,b−j,M₂−j)`, strictly convergent `a−j < M₂−b+1` by `detGram_lintegral_lt_top`).

**(3) Dominate onto the reduced comparator on `redChain (t★+j) M`.** The shell-`j` piece is bounded by
`const(ε)·(cornerComparator (redChain (t★+j) M) k jc).integral (c' − ½(a−j)(b−j))`
(banked `cornerComparator_decLoss` = `commonDivisor(u)²·frobSq(prod(redChain u M))`; drop nonneg residual
via `lintegral_mono`).

**(4) Close by the IH at `redChain (t★+j) M`.** `cornerComparator (redChain (t★+j) M) k jc` is
`adm`-admissible on the one-shorter chain `redChain (t★+j) M` (`cornerComparator_adm`,
`exists_cornerComparator_adm`), so the DECORATED IH (FACT II) gives
`DecoratedBoxThresholdFinite (cornerComparator (redChain (t★+j) M) k jc)`; the shifted exponent sits
strictly inside the reduced threshold by
`flagShift_lt_carrierThreshold : c' < carrierThreshold M ⟹ c' − ½·peelCharge M u < carrierThreshold (redChain u M)`.
**Different `j` ⟹ different reduced chain `redChain (t★+j) M` ⟹ separate, legitimate IH invocation
(FACT II).**

The realising banked structures, named: **cut-choice** = `deeperCut_le` + `freedCorner_eq_peelCharge` +
`flagCharge_ge`; **domain stratification** = `singularShell` + `singularShell_iUnion` +
`lintegral_le_sum_finCover`; **descent target** = `cornerComparator (redChain (t★+j) M) k jc` +
`cornerComparator_adm`; **threshold** = `flagShift_lt_carrierThreshold` + `carrierThreshold_shift`; **IH**
= the universal `DecoratedStepHyp` antecedent. The ONLY unbanked pieces are OWED-1/2/3 (steps 2–3),
which the cornershift cert already scoped as bounded LABOUR on `uniformWenn_le`/`det_le_det_of_posSemidef_sub`/`detGram_lintegral_lt_top`.

## 2. Why NO measure-disintegration is required (the wall does NOT materialise)

The Codex Q4 worry (cornershift cert) — "without permission to change the cut, an additional
measure-disintegration theorem is required" — is DISSOLVED, because the cut CAN be changed (FACTS I–III).
The three places a disintegration could hide, and why each is ordinary measure theory:

- **Outer shell subadditivity** (step 1): `∫_{A'} ≤ ∑_j ∫_{A'∈S_j}` is finite subadditivity over an
  exhaustive cover (`lintegral_le_sum_finCover`), measurability-free. NOT disintegration; NOT integration
  over the ordered singular values of `Z` (which Mathlib v4.29 genuinely lacks — and does not need here).
- **Shared deep-tail** (step 3): `Params (tailChain M) ≅ [M₁×M₂] × Params(M₂,…,M_L)` and
  `Params (redChain u M) ≅ [u×M₂] × Params(M₂,…,M_L)` share the deep-tail factor `Params(M₂,…,M_L)`
  (both via the banked measure-preserving `eFront`/`piFinSuccAbove`). The domination is established
  per-fixed-deep-tail `W = prod(M₂,…,M_L)` (a finite-dim matrix inequality in the ORIGINAL coordinates
  `Y, A_cor, Γ` vs `X`) and integrated against the shared factor by ordinary nonnegative Tonelli. This
  is a PRODUCT factorisation (Fubini), NOT a conditional-measure / Rokhlin disintegration.
- **Corner-shrink `(a,b)↦(a−j,b−j)`** (step 2): realised by a Gaussian SUB-CORNER peel (an honest
  integral producing charge) + PSD Loewner monotonicity (a pointwise-a.e. `≤`) + measure-preserving
  right-orthogonal transport (banked) — NOT a row/column-deleting change of variables (the cornershift
  cert already refuted the CoV reading; `measurePreserving_rowsEquiv` cannot delete rows). A DOMINATION
  `≤`, not a variable identification, so no pushforward.

At NO point is the tail measure pushed forward onto `Z`, nor is a conditional measure along the fibres of
`A' ↦ Z` constructed. The wall statement one would have needed — *"a disintegration of `volume` on
`Params(tailChain M)` over the map `A' ↦ (ordered singular values of prod(tailChain M) A')`, with a
measurable family of conditional measures"* — is **not invoked**. (Mathlib v4.29 does have
`MeasureTheory.Measure.disintegration` / conditional kernels, but they are not adjacent to
singular-value fibres and are NOT needed.)

## 3. The build-order the tide OWES — LIVE decorated route, NOT the dead plain hole

**Caveat (load-bearing for the tide).** Two routes coexist in the tree:
- `RouteMSJDecoratedPeelStep.innerCorankDescent_lt_top` takes the **PLAIN** IH
  `hIH : ∀ M', RouteMBoxThresholdFinite M'` and its docstring says "the decoration is discharged HERE,
  never carried into the IH." This is the route `RouteMSJDecoratedRec` §7.5 audit **Q2 declared DEAD**:
  at a zero-slack binding cut the plain reduced-chain IH has NO budget for the extra monomial/Gram weight.
- `RouteMSJDecoratedRec.DecoratedDescent` (decorated IH + `cornerComparator`) is the **LIVE** route.

The per-shell deeper-cut mechanism (§1) hands a DECORATED comparator
(`cornerComparator …` carrying `commonDivisor(u)²`) to the DECORATED IH — so it fits the LIVE route and
resolves Q2 (the monomial weight rides in the decoration, not the IH's slack). **The tide must build
OWED-3 (`deeperFlag_shell_le`) in the `DecoratedStepHyp adm` framing, closing on the decorated IH via
`cornerComparator_adm`, NOT re-open the dead plain hole `innerCorankDescent_lt_top`.** The shell mechanism
does not revive the plain route (a plain IH has no home for the `H⁻⁴`/monomial weight) — it confirms the
decorated route is the correct and admissible one.

## 4. Adversarial steelman that I could NOT sustain (recorded for the reviewer)

*"To use the comparator IH you must relate LHS variables `(A_cor : b×M₂, Γ : a×b)` at cut `t★` to the RHS
variable `X : (t★+j)×M₂` at cut `t★+j`; these have different dimensions, so the matching is a
dimension-changing CoV = a pushforward/disintegration."* — REFUTED: the comparator enters by DOMINATION
(`≤`), not variable identification. OWED-1/2 bound the LHS corank-block integral ABOVE by
`ε^{−(a−j)(b−j)}·C_box·[det-Gram at shrunk dims]`; that shrunk-dim weight (times the SHARED deep-tail
factor) IS the comparator integrand. The dimension drop is produced by a Gaussian sub-corner integral +
Loewner `≤` + a measure-preserving orthogonal transport (all banked/OWED), never by a measure CoV that
deletes rows. The steelman's premise is the exact CoV reading the cornershift cert already killed.

## 5. Decorrelated Codex verdict (my ADMITS conclusion WITHHELD from the prompt)

`codex/tobl3b-deepercut-{prompt,answer}.md` (xhigh; the exact spine defs + the banked facts + the
sub-questions supplied; the prompt framed "adjudicate decisively, either direction" — my ADMITS
conclusion NOT fed in). **Codex CONCURS, decorrelated, at 99%:**
- **VERDICT: ADMITS** ("structure permits the per-shell deeper-cut descent").
- **Q1 [fact+inference]:** the IH is universal over one-shorter chains + admissible decorations; each
  `redChain (t★+j) M` has the required arity; "the IH may be instantiated independently for every `j`;
  the recursion imposes no single-chain or linear-use restriction." (= my FACT I+II.)
- **Q2 [fact+inference]:** shell subadditivity is "ordinary domain monotonicity and finite subadditivity,
  not disintegration or integration over singular values." (= my §2 bullet 1.)
- **Q3 [fact+inference]:** the shared `Params(M₂,…)` factor ⟹ "standard nonnegative Tonelli/Fubini …
  No conditional measures along fibres of the product map are needed." (= my §2 bullet 2.)
- **Q4:** "No. … Nothing requires pushing the measure to `Z`, conditioning on `Z`, or constructing
  Rokhlin conditional measures." (= my §2.)
- **Flip condition (Codex §6):** the verdict would flip ONLY if the per-shell domination existed *only*
  after pushing tail measure forward to `Z` and required fibrewise conditional measures, rather than an
  inequality in the ORIGINAL product coordinates. This matches the single caveat I isolated (§2 bullet 2 /
  §4); the exhibited mechanism (§1) stays in original coordinates, so the flip does not trigger.
No inference of mine was fed in; the concurrence is decorrelated.

---

## Close

- **Firmest result (exact structural + decorrelated).** ADMITS. The (S,J) spine peels at the deeper cut
  `t★+j` per shell `S_j` because (I) `redChain t M` drops one layer for EVERY cut `t`, (II) the
  `DecoratedStepHyp` IH is universally quantified over one-shorter chains + admissible decorations — so
  `redChain (t★+j) M` is a legitimate, independent IH target for every `j` within one step invocation —
  and (III) the freed corner `Γ` is a LIVE integration variable in the hole, so the corner charge is not
  committed and the "stratify-Z-first, peel-at-`t★+j`-per-shell" order is realisable. No
  measure-disintegration is required; the deeper-cut re-peel is banked cut-choice + banked
  measurability-free shell cover + banked comparator/IH + OWED-1/2/3 LABOUR. **The T-Obl3b mountain is
  LABOUR, not a wall.**
- **Most likely to break it.** The flip condition Codex named: if the per-shell domination could be
  established ONLY by pushing the tail measure forward onto `Z` and constructing conditional measures
  along the singular-value fibres. The exhibited mechanism avoids this (it dominates in the original
  `(A', A_cor, Γ)` coordinates, per-fixed-deep-tail, by Tonelli) — but the reviewer/formaliser should
  confirm OWED-1's `uniformWenn_proj_le` really lands the shell-`j` Loewner bound POINTWISE-a.e. in `A'`
  with a `U_s` whose `Z`-dependence does not obstruct the (uniform-in-`U_s`) `strongBlock_lintegral_lt_top`
  bound. If OWED-1/2 secretly needed a measurable `Z ↦ U_s(Z)` eigenprojection selector, a small
  measurability lemma (not a disintegration) would be owed — still labour.
- **Next.** Dispatch the tide to build **OWED-3 (`deeperFlag_shell_le`) in the `DecoratedStepHyp adm`
  framing** — assembly = shell cover (`lintegral_le_sum_finCover`+`singularShell_iUnion`) → deeper-cut
  freed-corner peel + OWED-1 (`uniformWenn_proj_le`) → OWED-2 (`strongBlock_lintegral_lt_top`) → drop
  residual → `cornerComparator (redChain (t★+j) M)` + `cornerComparator_adm` → decorated IH, threshold by
  `flagShift_lt_carrierThreshold`. Do NOT re-open the dead plain-IH hole `innerCorankDescent_lt_top`.
  Before the mountain build, a pen-and-paper pin of OWED-1's pointwise-a.e. Loewner bound (the
  `U_s(Z)`-selector measurability) would close the one residual noted above.
