# S0 reduced-core-fidelity cert — the freedSchurLoss residual is NOT the reduced decLoss (equality REFUTED; domination CLOSES)

**Seat:** pen-and-paper VERIFICATION (genm-sj5-recon S0, PRE-tide, gates the #5 `DecoratedStepHyp` N4′
peelOp/weld tide). **Date:** 2026-07-12. **NO Lean, NO build.** Exact algebra (sympy, exact rationals).
**Anchor:** `(3,3,2,2) →_{t★=2} (2,2,2)`, the regression in `RouteMSJAdm.lean:220-258`.

**Read:** `recon-map.md` (this thread, N4′ crux + §6 reduced-core fidelity); the LANDED `gammaPrimeClause`
(`RouteMSJAdm.lean:134-145`); `freedSchurLoss_inner_peel_le` (`RouteMSJInnerDescent.lean:166`);
`freedSchurLoss` / `schurShift` (`RouteMSJChartShear.lean:139-152`); `freedSchurLoss_absorption` +
`_smul` (`RouteMSJDecoratedPeelCore.lean`); `pivotEnergy_inverse_free` (`RouteMSJInnerDescent.lean:94`);
`joint-corner-cert.md §6″`; `genm-sj4-recon/p0-gamma-clause-cert.md` (the units-free tied γ').

---

## ★ HEADLINE (the load-bearing finding, decorrelated-confirmed)

**The literal S0 fidelity claim is REFUTED, but this is a #5 SPEC CORRECTION, not a #5 wall.**

The banked brick's output base
`Base = w + frobSq(C·Q̃ₚ·(1 − P_{Q_b}))`, `w = frobSq(P·Q̃ₚ)`, `P_{Q_b} = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`
**does NOT equal** a genuine `redChain=(2,2,2)` carrier loss `D'.decLoss` in the clean γ' form
`commonDivisor(u)²·frobSq(Γ'·Z_tail')`. `Base` is a **RATIONAL** function of the deeper (tail)
parameters — the corank residual carries the Gram inverse `(Q_bQ_bᵀ)⁻¹` (denominator `‖Q_b‖²`, which
vanishes exactly on the rank-drop boundary of the units sector) plus a `det(P)` from `P⁻¹` — whereas a γ'
decLoss is a **polynomial** bilinear form `frobSq(Γ'·Z_tail')` with a **tied** tail `Z_tail' = A₃`. The
right-multiplied projection `(1 − P_{Q_b})(A₃)` breaks both the bilinear structure and the tail-tie. So
"the freedSchurLoss residual IS the reduced-chain carrier loss, in P⁻¹-free pivot form" is **FALSE as an
equality**.

**BUT** the peel still CLOSES, by DOMINATION on the units sector, not by a weld-equality:

* drop the nonneg residual: on the atom branch `c' > ab/2` and where `w > 0`,
  `Base^{−(c'−ab/2)} ≤ w^{−(c'−ab/2)}` (Base ≥ w ≥ 0, negative exponent);
* bound the Gram divisor: on `{Q_bQ_bᵀ ≽ c·I}`, `det(Q_bQ_bᵀ)^{−a/2} ≤ c^{−ab/2}` (a CONSTANT — it is
  NOT a monomial, so it must NOT "ride into `jac'`");
* the clean comparator `w = frobSq(Γ'·A₃)`, `Γ' = [P|B₁₂]·A₂` (the top-pivot-rows product),
  `Z_tail' = A₃` (TIED), **IS the γ' reduced-product loss**, whose threshold is EXACTLY
  `carrierThreshold(2,2,2) = 3/2`. So the peeled integrand is dominated by `const · D'.integral(c'−ab/2)`
  for a genuine γ'-admissible `D'` with `D'.decLoss = commonDivisor(u)²·frobSq(Γ'·A₃)`.

**The correct N4′ IH pattern (decorrelated Codex-concurred):** (1) CONSTRUCT an actually-admissible `D'`
whose loss is `w` (the clean bilinear); (2) apply the decorated IH to `D'`; (3) close the parent by an
EXTERNAL pointwise integral comparison `parent integrand ≤ const · D'`. **Calling the IH directly on a
decoration whose loss is `Base`, or whose `jac` weight contains `det(Q_bQ_bᵀ)^{−a/2}`, is UNSOUND** (that
object is not admissible). The recon's S2 "carrier→matrix weld `decLoss D' = Base`" and its "Gram-divisor
→ `jac'` threading" are the two mis-specified steps; both must be replaced by the comparator/domination.

---

## The anchor arithmetic (exact, Lean-def recursion — `/tmp/s0_minadm.py`)

`M = (3,3,2,2)`: binding cut `t★ = 2` (`bindingCut`, least `t` achieving the `minAdm` fold), corank widths
`a = M₀−t★ = 1`, `b = M₁−t★ = 1`, `peelCharge = a·b = 1`, `minAdm(M) = 4`, `carrierThreshold(M) = 2`.
`redChain 2 M = (2,2,2)`: `minAdm = 3`, `carrierThreshold = 3/2`.
Fold: `minAdm(M) = peelCharge + minAdm(redChain) = 1 + 3 = 4` (binding, zero-slack).

---

## The peel geometry (exact — `/tmp/s0_schur.py`, `/tmp/s0_schur2.py`)

Front layer `A₁ : 3×3` block-partitioned by `t★=2`: rows `3 = t(2)+a(1)`, cols `3 = t(2)+b(1)` →
`A₁ = [[P,B₁₂],[C,D]]`, `P:2×2` (invertible chart), `B₁₂:2×1`, `C:1×2`, `D:1×1`. Tail
`Z_tail = A₂·A₃ : 3×2`, row-split → `Q_p:2×2` (pivot rows), `Q_b:1×2` (corank row), `q = M₃ = 2`.
Shear `Γ := D − C·P⁻¹·B₁₂` (`schurShift x = C·P⁻¹·B₁₂`), `Q̃ₚ := Q_p + P⁻¹·B₁₂·Q_b`.

* **CHECK 1** `freedSchurLoss x Γ Q = frobSq(A₁·A₂·A₃)` under `D = Γ + schurShift x` — **TRUE**. (This is
  the banked `schurLoss_of_blockSplitD_symm_shift`; the parent decLoss = freedSchurLoss equality is sound.)
* **CHECK 2** `Base = w + frobSq(C·Q̃ₚ·(I − P_{Q_b})) = min_Γ freedSchurLoss` — **TRUE** (least-squares
  elimination of the freed corner `D`; `Base` is the corner-minimised loss). Confirms the brick's base.

### DELIVERABLE 1 — residual is NOT the reduced γ' decLoss (equality REFUTED)

* **CHECK 3** the denominator of `Base` is the Gram `Q_b·Q_bᵀ = ‖Q_b‖²` (× `det(P)` from `P⁻¹`).
  With `Q_b = A₂_cor·A₃` and outer blocks numeric, the corank-residual entry `r₀₀(A₃)` has denominator
  `‖A₂_cor·A₃‖²`, a nontrivial polynomial in `A₃` — so **`Base` is RATIONAL, not polynomial, in the tail
  `A₃`.** By contrast the pivot energy `w = frobSq(P·Q̃ₚ)` has denominator `1` (P⁻¹-free / polynomial),
  matching `pivotEnergy_inverse_free`.
* A γ' decLoss requires residuals `= (Γ'·Z_tail')` entries — **bilinear** in `(Γ', A₃)` with the tail
  **tied** to `A₃`. The corank residual `C·Q̃ₚ·(1 − P_{Q_b})` has the projection `(1 − P_{Q_b})` acting on
  the RIGHT and depending rationally on `A₃` — it is neither bilinear nor of the form (row)·`A₃`. The
  arbitrary-`coeff` freedom of a generic carrier does NOT help: the γ' clause rigidly fixes residuals to
  entries of `Γ'·Z_tail'` with tied `Z_tail'`.
* **Verdict: `Base ≠ D'.decLoss` for any γ' `D'`.** REFUTES the literal S0 claim.

*(Codex nuance, its inference — recorded, not relied on.)* On the Gram-nondegenerate chart `q = A₂_cor·A₃
≠ 0` there IS a tail-DEPENDENT invertible change of the active block `G₀ ↦ G'` (via the orthonormal frames
of `q,r`) with `Base = ‖G'·A₃‖²_F` EXACTLY γ'-form, tied tail `A₃`. This is NOT an output of the peel; it
is an extra CoV whose active-Jacobian `det S_h = √(1+‖CP⁻¹‖²)` is a spectator-dependent (bounded on a
compact pivot chart, but **non-monomial**) density, and no single such chart extends through `q = 0`. So
even the exact-equality reshape needs unbuilt machinery — it does not rescue the literal weld.

### DELIVERABLE 2 — reduced-adm producibility (clean-`w` comparator YES; Base/`g^{−1/2}` NO)

* **CHECK (`/tmp/s0_schur2.py`)** `w = frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·A₂·A₃) = frobSq(Γ'·A₃)`,
  `Γ' = [P|B₁₂]·A₂` (2×2), denominator `1` — **TRUE**. So `w` is a CLEAN bilinear γ' loss, tied tail `A₃`.
  `A₂_top ↦ G₀=[P|B₁₂]·A₂` is invertible on the chart (P invertible), so `Γ'` is a free active block.
* The **comparator decoration** `D'` with `D'.decLoss = commonDivisor(u)²·frobSq(Γ'·A₃)` satisfies
  `adm (2,2,2) D'`, clause-by-clause:
  - γ' provenance: residuals `= (Γ'·A₃)` entries, bilinear, `Z_tail' = prod(dropHead(2,2,2)) = A₃` tied. ✓
  - dims `minAdm ≤ a'·M'₁`: `3 ≤ 2·2 = 4` (`Γ'` has `a' = 2` rows). ✓
  - α (pSimultaneous) + δ≡0 (uniform support): all generators share the radial `commonDivisor`. ✓
  - β (threshold): via `carrierThreshold_shift` (below). ✓
  - genuineCarrier: after the absorption CoV `(P,B₁₂,A₂) → Γ'` and `A₃ = A₂'`; `C` appears ONLY in the
    dropped residual, so it integrates out as a bounded factor. ✓ (this CoV is N4′'s measure work.)
* **The `Base`-decoration is NOT admissible** (rational loss, no γ' form), and **`det(Q_bQ_bᵀ)^{−a/2}`
  cannot be part of `D'.jac`**: holding the exceptional coords `u` fixed it VARIES with the tied tail, so
  it is not a monomial `∏|u_ℓ|^{jac_ℓ}` (decorrelated-Codex-confirmed). It becomes monomial only after a
  FURTHER sector CoV (e.g. `t = z·v` gives `(z²+t²)^{−1/2} = |z|^{−1}(1+v²)^{−1/2}`) — not part of this
  peel. On the sector it is instead a BOUNDED CONSTANT `≤ c^{−ab/2}` (per fixed-ε subcover).

### DELIVERABLE 3 — exponent-shift composition (exact — CONFIRMED)

`carrierThreshold_shift`: `carrierThreshold(M) − ½·peelCharge = 2 − ½ = 3/2 = carrierThreshold(2,2,2)`
(binding equality, zero-slack). So `c' < 2 = carrierThreshold(3,3,2,2) ⟹ c' − ½·peelCharge = c' − ½ < 3/2
= carrierThreshold(2,2,2)` STRICTLY — the shifted exponent lands inside the reduced IH range. Composes
exactly with the reduced budget `minAdm(2,2,2) = 3 ≤ a'·M'₁ = 2·2`. **Soundness of dropping the residual:**
`w = frobSq(reduced product)` has threshold EXACTLY `minAdm(redChain)/2`, and the freed block carries
`½·peelCharge` via the shift; charges ADD to `½·minAdm(M)`, so dropping the (corner-optimised, ≥ 0)
residual — the safe upper-bound direction — loses NO threshold. This holds at all widths (`w = reduced
product loss`, residual always the droppable corner leftover).

### DELIVERABLE 4 — decorrelated Codex verdict (conclusion withheld in the prompt)

`codex/s0-fidelity-{prompt,answer}.md` (xhigh; exact objects + F1–F5 facts supplied, my refute/domination
conclusion WITHHELD). **Codex CONCURS on both faces:**
- **Q1** — "not literally a γ′-loss"; independently re-derives the rational form
  `Base = ‖A‖² + (xt−yz)²/(z²+t²)`, "genuinely rational, direction-dependent as `(z,t)→0`"; "arbitrary
  rational carrier coefficients do not help because the γ′ clause fixes the residuals to the entries of
  `G'A`." Adds the tail-dependent reshape (its inference; the non-monomial Jacobian caveat above).
- **Q2** — "does not hold at the reduced-IH handoff": `g^{−1/2} = ‖q‖^{−1}` "cannot equal a monomial
  `∏|u_ℓ|^{j_ℓ}`"; monomial only "after another sector decomposition." Endorses the domination
  `g^{−1/2}·Base^{−e} ≤ c^{−1/2}·w^{−e}`, `w = ‖G₀A₃‖²` γ'-form tied tail `A₃`, comparator admissible.
- **The sharpened IH pattern (Codex, verbatim intent):** "(1) construct an actually admissible decoration
  with loss `w`; (2) apply the IH to it; (3) use the external pointwise integral comparison. Calling the
  IH directly on a decoration whose loss is `Base`, or whose jacobian weight contains `g^{−1/2}`, is not
  justified." This IS the spec correction. No inference of mine was fed to Codex; the concurrence is
  decorrelated.

---

## Close

- **Firmest result.** The literal S0 fidelity (`Base = D'.decLoss`, γ' clean, P⁻¹-free) is **REFUTED** by
  exact algebra: `Base` carries the Gram inverse `(Q_bQ_bᵀ)⁻¹` (right-multiplied projection `1 − P_{Q_b}`)
  and is RATIONAL in the tied tail `A₃`, whereas a γ' decLoss is a polynomial bilinear `frobSq(Γ'·A₃)`.
  The clean bilinear part `w = frobSq(Γ'·A₃)`, `Γ' = [P|B₁₂]·A₂`, tail `A₃` tied, IS the γ' reduced-product
  loss (threshold `3/2`). The peel CLOSES on the units sector by DOMINATION (drop nonneg residual + bound
  Gram divisor by a constant), handing the decorated IH a genuine γ'-admissible comparator `D'`
  (`decLoss = commonDivisor²·frobSq(Γ'·A₃)`) — NOT `Base`. Exponent shift composes exactly. Decorrelated
  Codex concurs on all of it and sharpens the IH pattern.
- **This is a #5 SPEC CORRECTION, not a #5 obstruction.** N4′ must NOT (i) prove the weld-equality
  `decLoss D' = Base` (false), nor (ii) thread `det(Q_bQ_bᵀ)^{−a/2}` into `jac'` (not a monomial). It MUST
  build: construct-clean-`w`-admissible-`D'` → decorated IH → external pointwise `≤` comparison, with the
  units-sector supply (`w > 0`, `Q_bQ_bᵀ ≽ c·I`) and the off-sector `{w = 0} ∪ {rank-drop}` into the arity
  recursion.
- **Most likely to break it.** (1) The GENERAL γ'-parent (not the trivial→first-peel anchor): the peel then
  acts on the parent's free front block `Γ_D` (`a_D×M₁`, `a_D ≥ 2`) with `Z_tail,D = prod(dropHead M) =
  A₂A₃`, and the reduced comparator `w`, absorption CoV, and accumulated-`jac` carry are structurally
  analogous but UNVERIFIED at that generality — the anchor exhibits the fidelity gap fully, but the
  general-parent absorption Jacobian is the next check. (2) The absorption CoV `(P,B₁₂,A₂) → Γ'` measure
  factorisation (the `|det P|^{−M₂}` Jacobian, banked-ish via `mulLeftₚ`) integrating `C` out as a bounded
  factor — the genuineCarrier `D'` producibility rides on it. (3) The finite-subcover uniform-constant
  assembly for `det(Q_bQ_bᵀ)^{−a/2} ≤ c^{−ab/2}` (per-ε, no null-deletion — Codex Q3, still owed).
- **Next.** Hand this to the N4′ tide as the corrected S2/N4′(iii) spec (comparator/domination, NOT
  weld-equality; Gram divisor bounded-on-sector, NOT jac'-threaded). Then verify the general-γ'-parent peel
  (`Γ_D` front block) reproduces the clean-`w` comparator + tied tail — a short follow-on pen-and-paper on
  a γ'-resolved `(3,3,2,2)` parent (e.g. the P0-cert width-3 witness lifted one layer up) before committing
  the general step. **[Done in §S0.5 below.]**

---

## S0.5 — general γ'-parent (the P0 witness lifted to `(3,3,2,2)`): domination CONFIRMED, tide-ready

**Charge (continuation):** the #1 most-likely-to-break flagged above — verify the domination survives when
the front is NOT the trivial single layer `A₁` but a γ'-RESOLVED parent's FREE front block `Γ_D` (`a_D ≥ 2`,
tied tail `Z_tail,D = prod(dropHead M) = A₂·A₃`), with a shared radial `commonDivisor²` and an accumulated
`jac`. Same exact-algebra + decorrelated-Codex discipline. **Verdict: CONFIRMED — no new obstruction; the
general-parent peel is the trivial anchor modulo a shared radial (rides through as `m²`) and the `jac` carry
(monomial, threshold-exact).**

**The parent (landed tied γ', `RouteMSJAdm.lean:134-181`).** `D` over `M=(3,3,2,2)`, d≥1:
`decLoss(u,z) = commonDivisor(u)²·frobSq(Γ_D·(A₂A₃))`, `Γ_D` a FREE `a_D×3` front block (`eΓ z .1`),
`Z_tail,D = A₂A₃` (`= prod(dropHead M)`, tied), `commonDivisor = |u₀|^{k}` (`k = sharedDivisorExp`),
`jac = ![jac₀]`. **`a_D = M₀ = 3` is forced** — `ρ : ι ≃ Fin a_D × Fin(M last)` and the residuals are the
`a_D×(M last)=a_D×2` entries of `Γ_D·Z_tail`; faithfully carrying the full `M₀×M last = 3×2` DLN product
(genuineCarrier `ν = Fin 3 × Fin 2`) forces `a_D = 3` (the dims clause `minAdm ≤ a_D·M₁` gives only the
weaker `a_D ≥ 2`). Block-partition `Γ_D = [[P,B₁₂],[C,D_D]]` (P:2×2 invertible chart, B₁₂:2×1, C:1×2,
D_D:1×1), tail `A₂A₃` row-split `[Q_p;Q_b]`, shear `Γ = D_D − C·P⁻¹·B₁₂` (Jacobian 1).

### (1) clean-`w` comparator survives (CONFIRMED — `/tmp/s0_schur2.py`, Codex Q1 concurs)

`w = frobSq(P·Q̃ₚ) = frobSq([P|B₁₂]·A₂·A₃) = frobSq(Γ'·A₃)`, `Γ' = [P|B₁₂]·A₂ = P·X + B₁₂·r`
(writing `A₂ = [X;r]`), **polynomial, P⁻¹-free, exactly the tied-tail γ' form for `(2,2,2)`** (reduced tail
`A₃ = prod(dropHead(2,2,2))`). The corank rows `C` occur ONLY in the nonneg rational residual. So
`Base^{−(c'−ab/2)} ≤ w^{−(c'−ab/2)}` (drop residual, `c'>ab/2`, `w>0`), and the comparator handed to the IH
is `D'.decLoss = commonDivisor(u)²·frobSq(Γ'·A₃)` (carrier indexed `Fin 2 × Fin 2`, residuals the entries
of `Γ'·A₃`) — **NOT** the rational `Base`. Replacing the literal `A₁` by the free block `Γ_D` introduces NO
new algebraic step: the block-partition + shear are identical, and `Γ_D` is a genuine independent Lebesgue
coordinate block (the landed `eΓ : Z ≃ᵐ (matBox front) × Params(dropHead M)` is `MeasurePreserving` with
product-box `dom` — this DISCHARGES Codex's one caveat, that "free block" be genuine coordinate freeness,
not merely syntactic).

### (2) absorption CoV with free `Γ_D`; `C` integrates out bounded (CONFIRMED chartwise — Codex Q2 concurs)

For fixed `(P,B₁₂,r)` the absorption `X ↦ Γ' = P·X + B₁₂·r` is an AFFINE BIJECTION (`P` invertible),
`X = P⁻¹(Γ' − B₁₂·r)`, Jacobian `dX = |det P|^{−2} dΓ'` (`X` has `M₂ = 2` columns). On a pivot chart
`|det P| ≥ δ` this is a bounded spectator-dependent unit; after dropping the residual the integrand is
independent of `C`, whose bounded-box integral is a constant. Likewise the Gram `det(Q_bQ_bᵀ)^{−a/2} ≤
δ'^{−ab/2}` bounded on the units sector `Q_bQ_bᵀ ≽ δ'`. **Neither `|det P|^{−2}` nor the Gram divisor is
inserted into the reduced `jac`** — both are bounded chart units, bounded EXTERNALLY (enlarging the
transformed domain to a fixed box if needed). This yields an admissible comparator integral (NOT an exact
measure-preserving identity with the banked output). **Sharp caveat (Codex, folded in):** `P` invertible +
`Q_b ≠ 0` POINTWISE are INSUFFICIENT — the bounds must be UNIFORM (the finite-subcover / uniform-constant
assembly, per-ε, no null-deletion — still the owed measure work, same as the anchor).

### (3) shared radial + accumulated `jac` carry (CONFIRMED monomial + threshold-exact — `/tmp/s0p5_*.py`, Codex concurs)

The radial `commonDivisor² = |u₀|^{2k}` factors through the freed-MATRIX-block integral as a constant
multiplier (the freed `Γ` lives in `Z`, not in `u`): after integrating `Γ` the `u₀` power is
`|u₀|^{jac₀ − 2kc'}`. Setting the reduced radial exponent `jac'₀ = jac₀ − k·peelCharge` gives
`|u₀|^{jac'₀}·(|u₀|^{2k}·w)^{−(c'−ab/2)} = |u₀|^{jac₀−2kc'}·w^{−(c'−ab/2)}` — an EXACT match, and
`(jac'₀+1)/(2k) = (jac₀+1)/(2k) − peelCharge/2`, i.e. `axisRatio(jac'₀,k) = carrierThreshold(redChain)`
whenever `axisRatio(jac₀,k) = carrierThreshold(M)` (since `minAdm(redChain) = minAdm(M) − peelCharge`).
Verified exact over `(3,3,2,2)→(2,2,2)` (`k=1,2`), `(2,2,2)→` peel, and deep-sharing widths (`→11/2`,
`→17/2`); `jac'₀ = k·minAdm(redChain) − 1 ≥ 0` always. **The carry is purely a `u₀`-exponent shift — no
non-monomial weight (Gram divisor, absorption Jacobian) sneaks into `jac'`.** This is `carrierThreshold_shift`
realised at the decoration/monomial level.

### S0.5 close

- **Firmest.** The general γ'-parent peel is the trivial anchor UP TO (i) a shared radial `commonDivisor²`
  (factors through as `m²`, Codex-confirmed via `(m²·Base)^{−c'} = m^{−2c'}·Base^{−c'}`) and (ii) the `jac`
  carry `jac'₀ = jac₀ − k·peelCharge` (monomial, reproduces the reduced threshold exactly). The clean-`w`
  comparator `D'.decLoss = commonDivisor²·frobSq(Γ'·A₃)` (`Γ' = [P|B₁₂]·A₂`, tail `A₃` tied) is genuinely
  γ'-admissible; `C` integrates out bounded after dropping the residual. Decorrelated Codex concurs on all
  three (Q1 survives, Q2 survives chartwise, radial+`jac` monomial+threshold-exact); its lone caveat
  (coordinate-freeness of `Γ_D`) is DISCHARGED by the landed `eΓ` MP-split + product-box `dom`. **The
  corrected N4′ spec (comparator/domination) is confirmed at full γ'-parent generality — tide-ready.**
- **Most likely to break (residual, for the tide to green-gate).** (1) **Deeper chains `L > 1`** (peel not
  adjacent to the width-2 leaf, e.g. `(3,3,3,2,2)`): the tail `prod(dropHead M)` is a longer product and the
  absorption absorbs the next layer — structurally analogous but UNVERIFIED beyond `L=1`; the natural next
  boundary. (2) The **uniform-lower-bound subcover** (`|det P| ≥ δ`, `Q_bQ_bᵀ ≽ δ'`) — Codex's "pointwise
  invertible/nonzero is insufficient"; the finite-subcover uniform-constant assembly is the owed measure
  work (shared with the anchor's §Most-likely (3)). (3) The **tide must green-gate that the landed `eΓ` is
  genuinely `MeasurePreserving` with a product-box `dom`** — the discharge of Codex's coordinate-freeness
  caveat rides on it (it holds by inspection of `RouteMSJAdm.lean:138-141`, but the peelOp must PRESERVE it,
  the ρ-Equiv/split production obligation, `#4`-gated).
- **Net.** No general-parent obstruction. The single genuinely-new construction (N4′) is: peelOp producing
  the clean-`w` comparator `D'` + the domination `∫_Γ freedSchurLoss^{−c'} ≤ const · [D'.integral(c'−½peelCharge)]`
  on the sector, with the radial/`jac` carry (monomial, banked `carrierThreshold_shift`). The math does NOT
  wall at generality; the corrected spec (construct-comparator → IH → pointwise `≤`) stands.
