# h2 INDEPENDENT confirm (obstruction seat, decorrelated) — VERDICT: REFUTE the ADDITIVE bound; the FOLDED form survives

**Direction:** obstruction. Independently set up from the Lean definitions (NOT pp's scripts).
**Bottom line:** the load-bearing bound **as stated** — `|frobSq(Rcore) − coreΦ| ≤ Ccore·Sreg`
UNIFORMLY on S5a ∩ 𝓝(w0) — is **FALSE** (non-uniform; `Ccore → ∞` on a reachable family of curves
where `cond(P00) = 1` exactly). pp's "O(Sreg), bounded constant" headline does **not** hold on the bare
S5a domain. HOWEVER the *downstream* object the producer actually needs — the FOLDED multiplicative
comparability `Sreg + frobSq(Rcore) ≍ Sreg + coreΦ` — **DOES** hold uniformly (γ → 1), via a DIFFERENT
mechanism than pp's (the gap is charged to `coreΦ`, not to `Sreg`).

This is an **escalation on the stated additive lemma / route** (the producer's `|frobSq Rcore − coreΦ|
≤ C·Sreg` charge and the bridge's `hRem : frobSq(R−S0S1) ≤ Crem·Sreg²` are both FALSE on S5a), but
**NOT** a refutation of the headline folded comparability or the RLCT conclusion — the route must be
repaired to the multiplicative form.

---

## What I pinned from the definitions (independent of pp / the dispatcher)

- `Mw = reindex(rThr, pivotThr J)(P0·(prod(A w) − B)·QL)`; blocks `(P00−1, P01, P10, P11) = toBlocks Mw`.
  **`P00 = (1,1)-block of Mw + 1`** (`FrontPivotProducer.eventually_P00_invertible`, lines 173-198) —
  the **corner-shifted +1 pivot** → identity at w0 (NOT the bare `(1,1)` block, which → 0). pp's earlier
  blow-up was exactly the wrong (bare) pivot; the +1 pivot is confirmed correct.
- `Rcore = P11 − P10·⅟P00·P01` (the (1,1)-Schur complement).
- `Sreg = (∑(P00−1)² + ∑P01²) + ∑P10²` (`DeepestGaugeConstruction.lean:1808`, :2143).
- `coreΦ = deepestCoreF (deepestCoreAbsorb (split w)).2.1 = frobSq(∏_s S'_s)` EXACTLY, with frame-free
  per-layer cores `S'_s = T_s − Z_s·(1+X_s)⁻¹·Y_s` (`deepestCoreF_coreAbsorb_eq_prodSchur`, :1940;
  `schurCorrection`, `DeepestSchurShift.lean:135`). `(X_s,Y_s,Z_s)=(readX,readY,readZ)` the gauge reads.
- Exact ring identity (`schur_product_ldu`, `DeepestSchurComparability.lean:144`): with the framed cores
  `S_s = T_s − Z_s·⅟A_s·Y_s` and `K = Z1·⅟P00·Y0`,  `Rcore = S0·(1−K)·S1`,  `Rcore − S0·S1 = −S0·K·S1`.
- **Framed = frame-free** because the deepest-point layer is the corner `fromBlocks(1,0,0,0)`, so a
  deviation gives layer `s = fromBlocks(1+readX_s, readY_s, readZ_s, T_s)`, i.e. `A_s = 1+X_s`,
  `Y_s=readY_s`, `Z_s=readZ_s` ⇒ `S_s = S'_s` and `coreΦ = frobSq(S0·S1)` (matches the bridge's `hCore`).
- The frame-stripping (`endpoint_telescoping_eq`, `reindex_fromBlocks_reads_eq_deviation`) is BANKED in
  the producer body, so `Mw`'s blocks ARE the per-layer gauge-read block product `C0·C1` — the curves
  below are genuine paths in `split`-space (reg/spec gauge reads + core reads are independent slots of
  `DeepestSplit = (nReg) × (flatDim M) × (nGauge)`).

## Kill-conditions — every one, fired or cleared

1. **Generic order (cleared, a fortiori holds).** Exact sympy (rational num/den lead-power) +
   log-log numeric fit, clean-corner: **gap = Θ(eps⁶) = Θ(Sreg³)** (`Sreg = Θ(eps²)`), with some
   directions higher (eps⁷/eps⁸/eps¹⁰). Structure: `S0,S1=O(eps)`, `K=O(eps²)`, `D=−S0KS1=O(eps⁴)`,
   `frobSq(D)=O(eps⁸)`, cross `⟨S0S1,D⟩=O(eps⁶)`. So **generically the additive bound holds with huge
   room** (`gap/Sreg → 0`). Codex independently derived the identical `Θ(Sreg³)`.
   **Settles pp's flip-flop: the GENERIC order is Sreg³, not Sreg, not Sreg².**

2. **Blow-up on S5a (FIRED — REFUTES the additive bound's uniformity).** There is a reachable family of
   curves with **`cond(P00) = 1` exactly** (deepest interior of S5a) on which `gap/Sreg → const ≠ 0`,
   and the const is **UNBOUNDED** (scales `~1/a²`). Codex's scalar curve (independently re-verified
   EXACTLY in sympy, `/tmp/h2confirm/codex_curve.py`):
   r=M=1, `A0=1, A1=1−t², Y0=Z1=T0=T1=t, Y1=−t²+at³, Z0=−t²/(1−t²)` ⇒
   `P00=1, P10=0, P01=at³`, `Sreg=a²t⁶`, `G=2t⁶`, `G/Sreg → 2/a²`.
   I **generalised** it to all r,M (`/tmp/h2confirm/refute_scan3.py`): keep cores/K-drivers
   `T0,T1,Y0,Z1 = Θ(t)`; set `A1 = I − Y0·Z1` so **`P00 = I` exactly**; null `P10` via `Z0=−T0Z1⅟A1`;
   shrink `P01` to `Θ(t³)` via `Y1`. Then `Sreg=Θ(t⁶)` but cores stay `Θ(t)`, cross `⟨B,D⟩=Θ(t⁶)`, so
   `G/Sreg → const`. Measured (t→1e-4, cond=1.00): r1M111→11.5, r1M211→91, r1M222→608, r2M221→92,
   r1M321→460; and `G/Sreg ~ C/a²` UNBOUNDED (a=0.1→287, a=0.03→3188, a=0.01→28690).
   **⇒ no single finite `Ccore` works on S5a∩𝓝(w0). The additive bound is NON-UNIFORM.**

3. **Bridge input hypothesis (FIRED).** The abstract bridge `germ_charge_of_schur_factorization`
   (`DeepestGermCharge.lean:50`) requires `hRem : frobSq(R−S0S1) ≤ Crem·Sreg²` (QUADRATIC charge). On
   the refuting curve `frobSq(D)/Sreg² → ∞` like t⁻⁴ (4.8e6 → 5.8e18 over 4 decades, cond=1). So the
   bridge's PREMISE is also false on S5a — the whole stated chain rests on a false premise there.

4. **Is S5a (bounded ⅟P00) the right/sufficient domain? (NO.)** `cond(P00) ≤ M` is NECESSARY (keeps `K`
   pole-free) but **NOT sufficient** for the additive bound. The failure is a *denominator* effect:
   `Sreg` stops measuring the full small parameter when `P00−1, P01, P10` cancel below the hidden core
   scale. (Codex's framing, independently reproduced.) Corner-clean (front pivot + `hcorner`) is needed
   for the GENERIC `Θ(Sreg³)` order but is ALSO insufficient against these cancellation curves.

5. **Front-pivot dependence (cleared as not the fix).** The curves are at the front pivot already;
   front-pivot WLOG does not exclude them. A separate frame-stress (`/tmp/h2confirm/frame_stress.py`)
   showed: corner-CLEAN frames (honouring `hcorner`) give gap `O(Sreg²)`; corner-DIRTY frames (violating
   `hcorner`) give gap `Θ(Sreg)` with a true nonzero constant — **this is the likely source of pp's
   "scale-invariant ~0.011" O(Sreg) reading: pp was in the corner-dirty / non-`hcorner` regime.**

6. **Does the FOLDED form survive? (YES — cleared, the repair.)** The producer's *final* conjuncts are
   the FOLDED multiplicative `Sreg+frobSq(Rcore) ≍ Sreg+coreΦ` (:2144-2155). On the refuting curve the
   two-sided folded distortion `max(L/R,R/L) = 1.000000`; an adversarial search over block-scale
   exponents (`/tmp/h2confirm/refute_scan3.py` extended) gives worst folded charge
   `|frobSq Rcore − coreΦ|/(Sreg+coreΦ) ≈ 0` and worst `|frobSq Rcore − coreΦ|/coreΦ ≈ 8e-6` at t=1e-3,
   decaying `Θ(t²)`. Reason: `coreΦ = frobSq(S0S1) = Θ(t⁴)` DOMINATES both `Sreg=Θ(t⁶)` and the gap
   `Θ(t⁶)`; and `frobSq(K) → 0` on S5a (worst 1.6e-11), so
   `|frobSq Rcore − coreΦ| ≤ η(w)·coreΦ`, `η → 0`. **The gap is charged to `coreΦ`, NOT to `Sreg`.**

## The verdict, precisely scoped

- **REFUTE** (uniform additive form, bare S5a): `∃ Ccore, ∀ᶠ w∈S5a∩𝓝(w0), |frobSq Rcore − coreΦ| ≤
  Ccore·Sreg` is **FALSE**. Witness: the `P00=I` cancellation curves (kill-cond 2), reachable, cond=1,
  `Ccore` unbounded ~`1/a²`. The bridge premise `hRem ≤ Crem·Sreg²` is false there too (kill-cond 3).
- **CONFIRM** (the folded form the build actually needs): `Sreg + frobSq Rcore ≍ Sreg + coreΦ` holds
  uniformly with γ → 1 near w0 (kill-cond 6) — because `|frobSq Rcore − coreΦ| ≤ η·coreΦ` with η→0 on
  S5a (driven by `frobSq K → 0`), and `coreΦ ≤ Sreg + coreΦ`.
- **ORDER (settled):** generically `gap = Θ(Sreg³)`; the additive `O(Sreg)` reading is the corner-dirty
  artifact, and even corner-clean the additive bound fails non-uniformly on cancellation curves.

## The CORRECT repair (exact, verified; what the formaliser should target)

The clean route does NOT put `Sreg` on the RHS. Using the BANKED S5c pieces
(`schur_core_germ_comparability` (iii)+(iv), `DeepestSchurComparability.lean:287`), with `B=S0·S1`
(`= coreΦ`'s product), `D=Rcore−B=−S0·K·S1`:

    frobSq(Rcore) = coreΦ + 2⟨B,D⟩ + frobSq(D)        (iii, exact)
    |⟨B,D⟩| ≤ √(coreΦ·frobSq(D))                       (iv, Cauchy–Schwarz, exact)
  ⇒ **|frobSq(Rcore) − coreΦ| ≤ 2·√(coreΦ·frobSq(D)) + frobSq(D)**   (EXACT — verified 0 violations / 20000)

Then the folded conjuncts close from **`frobSq(D) → 0` and `coreΦ` bounded** alone (no `Sreg` charge):
`|gap| → 0`, so `|gap| ≤ η·(Sreg+coreΦ)` with η→0, giving the producer's `Sreg+frobSq Rcore ≍ Sreg+coreΦ`
at γ=1+η. Verified: `frobSq(D)/coreΦ → 0` on S5a (worst 1.6e-11 at t=1e-3; decays Θ(t²) even on the
cancellation curves), driven by `frobSq(D) ≤ frobSq(S0)·frobSq(K)·frobSq(S1)`
(`schur_core_remainder_frobeniusSq_le`, banked) with `frobSq(K)→0` on S5a (`K=Z1·⅟P00·Y0`, ⅟P00 bounded,
`Y0,Z1 → 0`).

**CAUTION (a wrong repair I tried and rejected):** the *naive* `|gap| ≤ (2√frobSq(K)+frobSq(K))·coreΦ`
is **FALSE** (1251/20000 violations) — `frobSq(D) ≤ coreΦ·frobSq(K)` does NOT hold (sub-multiplicativity
is factor-wise `frobSq S0·frobSq K·frobSq S1`, not `coreΦ·frobSq K`; the product `S0·S1` can cancel). Use
the `√(coreΦ·frobSq(D))` form, not a `√frobSq(K)`-times-coreΦ form.

## Most likely thing to break the verdict / next step

- The `germ_charge_of_schur_factorization` bridge (`DeepestGermCharge.lean`) must be **replaced**: its
  `hRem : frobSq(R−S0S1) ≤ Crem·Sreg²` premise is FALSE on S5a (kill-cond 3), and its conclusion (the
  additive `≤ C·Sreg`) is the refuted form. The new bridge takes `hRemRel : frobSq(D) ≤ small` and
  `hCoreBdd : coreΦ ≤ Mc`, concluding `|gap| ≤ (2√(Mc·small)+small)` (absolute, →0), then folds.
- Residual risk to the REPAIR: confirm `frobSq(D) → 0` is `∀ᶠ` on S5a in Lean — it is
  (`frobSq(D) ≤ frobSq S0·frobSq K·frobSq S1`, all three factors → 0 / bounded on S5a). And confirm
  `coreΦ`'s `S0,S1` are literally the same framed cores as in `Rcore = S0(1−K)S1` (true by the corner
  identity `A_s = 1+X_s`) — the formaliser should re-derive, not inherit.
- The headline RLCT conclusion is NOT threatened: the folded comparability (hence the squeeze, hence
  `rlct ≤ ½·codim` reading) survives. What is threatened is only the producer's STATED additive route +
  the current bridge module.

## Artifacts (re-runnable, my own; NOT pp's)
- `/tmp/h2confirm/confirm_core.py` — block-product harness, 5 shapes, gap/Sreg & /Sreg².
- `/tmp/h2confirm/order_fit.py` — log-log order fit (gap~Sreg³).
- `/tmp/h2confirm/symbolic_order3.py` — EXACT sympy lead-power (gap=eps⁶, Sreg=eps², gap=Sreg³).
- `/tmp/h2confirm/codex_curve.py` — EXACT re-verification of Codex's scalar refuting curve.
- `/tmp/h2confirm/refute_scan3.py` — generalised `P00=I` cancellation refutation (all r,M).
- `/tmp/h2confirm/frame_stress.py` — corner-clean (O(Sreg²)) vs corner-dirty (O(Sreg)) frames.
- Codex consult: `codex/h2-confirm-order-prompt.md` / `h2-confirm-order-answer.md` (decorrelated, xhigh;
  independently derived `Θ(Sreg³)` generic + the cancellation-curve refutation).
