# h2 build-ready repair spec — re-architect the FOLD PROOF (statement unchanged)

**Scope:** the additive intermediate `|frobSq(Rcore) − coreΦ| ≤ C·Sreg` (the producer's residual
`sorry` at `DeepestGaugeConstruction.lean:~2173`, route line :2142) is **FALSE on the real chart domain**
— refuted by a *reachable* curve (settled below, item 5). It must be removed. The producer's two FOLDED
conjuncts `hcore_le`/`hcore_ge` (the `Sreg + Score ≍ Sreg + coreΦ` pair, :2144-2155) are **TRUE** and
**uniform** on S5a; re-prove them WITHOUT the additive charge. `deepest_loss_squeeze`'s statement and
its whole body (:2794-2964) are **unchanged** — it consumes only `hcore_le`/`hcore_ge` (:2932, :2960),
never the additive lemma.

Notation: `Sreg = ‖P00−1‖² + ‖P01‖² + ‖P10‖²`; `Score = frobSq(Rcore) = ‖P11 − P10·⅟P00·P01‖²`;
`coreΦ = deepestCoreF (deepestCoreAbsorb (split w)).2.1`; `D = Rcore − S0·S1`; `B = S0·S1`;
`S_s, K` the per-FACTOR framed cores / off-pivot correction from `rcore_schur_factor_of_corner_split`
(`Rcore = S0·(1−K)·S1`, `K = (G1)₂₁·⅟P00·(G0)₁₂`).

---

## 1. The re-stated 2681 intermediate (the new sub-lemma to formalise)

Replace `|frobSq(Rcore) − coreΦ| ≤ C·Sreg` by the **exact, verified coreΦ-relative charge** (the S5c
difference split, already banked as `schur_core_germ_comparability` (iii)+(iv),
`DeepestSchurComparability.lean:287`):

    |frobSq(Rcore) − coreΦ|  ≤  2·√(coreΦ · frobSq(D))  +  frobSq(D)            (★)   [D = Rcore − S0·S1]

(★) is EXACT (verified 0 violations / 20000 random S0,S1,K; the chain is `frobSq(Rcore) = coreΦ +
2⟨B,D⟩ + frobSq(D)` from (iii), and `|⟨B,D⟩| ≤ √(coreΦ·frobSq(D))` from (iv) Cauchy–Schwarz). It needs
`coreΦ = frobSq(B)` (the exact core match `hCore`, true by the corner identity `A_s = 1+X_s` ⇒ the
producer's `S_s` = the frame-free `S'_s` in `coreΦ`; `deepestCoreF_coreAbsorb_eq_prodSchur`, :1940).

**Do NOT** use the tempting `|gap| ≤ (2√frobSq(K)+frobSq(K))·coreΦ` — it is **FALSE** (1251/20000
violations: `frobSq(D) ≤ coreΦ·frobSq(K)` does not hold; sub-multiplicativity is factor-wise
`frobSq(S0)·frobSq(K)·frobSq(S1)`, and `B = S0·S1` can cancel). Route through `√(coreΦ·frobSq(D))`.

The germ input is then `frobSq(D) → 0`, NOT `frobSq(D) ≤ Crem·Sreg²` (the latter is also FALSE on the
chart — `frobSq(D)/Sreg² → ∞` like t⁻⁴ on the refuting curve).

## 2. How (★) produces the folded sandwich — the new γ₁/γ₂ witness

The squeeze needs `hcore_ge : Sreg + coreΦ ≤ γ₁·(Sreg + Score)` and
`hcore_le : Sreg + Score ≤ γ₂·(Sreg + coreΦ)` with a SINGLE γ₁,γ₂ on a nbhd `U` (verified: a uniform
γ ≈ 1 works on all of S5a incl. BOTH cancellation mechanisms — worst two-sided fold distortion 2.58, →1).

**The charge must use the `(Sreg + coreΦ)` denominator, NOT `coreΦ` alone** (this is load-bearing — see
the CAUTION). Define the **folded** charge:

    |Score − coreΦ|  ≤  η(w)·(Sreg + coreΦ),   η(w) := 2·u(w) + v(w),                  (♦)
      u(w) := √(coreΦ·frobSq(D)) / (Sreg + coreΦ),   v(w) := frobSq(D) / (Sreg + coreΦ).

(♦) follows from (★) by dividing by `(Sreg + coreΦ)`. Both `u, v → 0` as `w → w0` on S5a (VERIFIED over
the full adversary set incl. product- and reg-cancellation: worst `v = 7e-11`, worst `u = 7.5e-6` at
t=1e-2, both decaying to 1e-21 / 2.6e-12 at t=1e-4). So `η → 0`.

From `|Score − coreΦ| ≤ η·(Sreg + coreΦ)`:
- `Sreg + Score ≤ (Sreg + coreΦ) + |Score − coreΦ| ≤ (1+η)·(Sreg + coreΦ)`  ⇒ **`hcore_le`, γ₂ = 1+η**.
- `Sreg + coreΦ ≤ (Sreg + Score) + |Score − coreΦ| ≤ (Sreg + Score) + η·(Sreg + coreΦ)` ⇒
  `(1−η)·(Sreg + coreΦ) ≤ Sreg + Score`  ⇒ **`hcore_ge`, γ₁ = (1−η)⁻¹** (valid once `η ≤ ½`, eventual).

**Witness replacing `⟨1, 1+C, 1+C, 1, 1, …⟩`:** pick any fixed `γ` with `1 < γ` (e.g. `γ₁ = γ₂ = 2`),
valid on the sub-nbhd `U' = {η(w) ≤ ½} ∩ S5a` (a 𝓝, since `η → 0`). So the producer returns
`γ₁ = γ₂ = 2`, NOT a `1+C` tied to the dead additive constant. **`Sreg` enters the sandwich only
additively, identically on both sides AND in the charge denominator** — the gap is charged to
`(Sreg + coreΦ)`, which is protected on BOTH adversary families:
  * reg-cancellation (Sreg → 0, coreΦ = Θ(t⁴) dominant): the gap Θ(t⁶) ≤ η·coreΦ, η→0;
  * product-cancellation (coreΦ → 0 faster, Sreg = Θ(t²) dominant): the gap ≤ η·Sreg, η→0.
Neither denominator alone suffices; their SUM does.

## 3. Which banked lemma the build calls

- **NOT `germ_charge_of_core_charge`** (`DeepestGermCharge.lean:136`): it merely renames the additive
  charge (`hCore_germ : |coreΦ − frobSq R| ≤ Ccore·Sreg` ⇒ same, modulo |·|). Its hypothesis IS the
  refuted bound — it does not help. **`germ_charge_of_schur_factorization`** (:50) is also dead — its
  `hRem : frobSq(R−S0S1) ≤ Crem·Sreg²` premise is FALSE on the chart.
- **DO call** `schur_core_germ_comparability` (`DeepestSchurComparability.lean:287`) for (iii)+(iv) — it
  already delivers exactly the `frobSq R = coreΦ + 2⟨B,D⟩ + frobSq D` split and the Cauchy–Schwarz
  `⟨B,D⟩² ≤ coreΦ·frobSq D`. (★) is a 3-line corollary of it (`Real.sqrt`, `abs_add_le`, `abs_le`).
- **DO call** `rcore_schur_factor_of_corner_split` (`DeepestBlockDecomp.lean:207`) for the `hR :
  Rcore = S0·(1−K)·S1` factorization (with the +1 corner pivot), supplying the `D = Rcore − S0·S1`.
- **NEW lemma needed** (the abstract bridge, ~30 LoC, network-free — replaces
  `germ_charge_of_schur_factorization`): name e.g. `fold_comparability_of_core_relative`:

      (w0 : ι) (Sreg coreΦ Score : ι → ℝ) (D : ι → Matrix m0 m2 ℝ)
      (hSregNN : ∀ w, 0 ≤ Sreg w) (hcoreNN : ∀ w, 0 ≤ coreΦ w)
      (hsplit : ∀ᶠ w, |Score w − coreΦ w| ≤ 2*√(coreΦ w * frobSq (D w)) + frobSq (D w))   -- (★)
      -- the TRUE eventual: the gap, normalised by (Sreg+coreΦ), → 0 (item 4):
      (hcharge : ∀ᶠ w, |Score w − coreΦ w| ≤ (1/2) * (Sreg w + coreΦ w))
      ⊢ ∃ γ₁ γ₂, 0 < γ₁ ∧ 0 < γ₂ ∧ ∀ᶠ w,
           Sreg w + coreΦ w ≤ γ₁*(Sreg w + Score w) ∧ Sreg w + Score w ≤ γ₂*(Sreg w + coreΦ w)

  with witness `γ₁ = γ₂ = 2`. (From `|Score−coreΦ| ≤ ½(Sreg+coreΦ)`: upper `Sreg+Score ≤ (3/2)(Sreg+coreΦ)
  ≤ 2(Sreg+coreΦ)`; lower `(Sreg+Score) ≥ (1/2)(Sreg+coreΦ)` ⇒ `Sreg+coreΦ ≤ 2(Sreg+Score)`.)
  `(★)` is only an INTERMEDIATE feeding `hcharge`; the bridge can take `hcharge` directly.

## 4. The charge input `hcharge : |Score − coreΦ| ≤ ½·(Sreg + coreΦ)` ∀ᶠ (the one true residual)

`D = Rcore − S0·S1 = −S0·K·S1` (banked `schur_core_remainder_identity`), so
`frobSq(D) ≤ frobSq(S0)·frobSq(K)·frobSq(S1)` (banked `schur_core_remainder_frobeniusSq_le`). On S5a:
- `S_s = T_s − Z_s·⅟A_s·Y_s` continuous, `S_s(w0) = 0` ⇒ `frobSq(S0), frobSq(S1) → 0`.
- `K = Z1·⅟P00·Y0`, `⅟P00` bounded on S5a (`eventually_P00_invertible` + inverse continuity), `Y0,Z1 → 0`
  ⇒ `frobSq(K) → 0`. So `frobSq(D) → 0` (∀ᶠ) absolutely.

**The provable charge uses the `(Sreg + coreΦ)` denominator (NOT `coreΦ` alone).** Via (★),
`|Score − coreΦ| ≤ 2√(coreΦ·frobSq D) + frobSq D`. It suffices to show BOTH
  `frobSq(D) ≤ ⅛·(Sreg + coreΦ)`   and   `√(coreΦ·frobSq D) ≤ ⅛·(Sreg + coreΦ)`   ∀ᶠ,
giving `|Score − coreΦ| ≤ (2·⅛ + ⅛)·(Sreg+coreΦ) = ⅜·(Sreg+coreΦ) ≤ ½·(Sreg+coreΦ)`. Both VERIFIED to
→ 0 over the full adversary set (worst `frobSq(D)/(Sreg+coreΦ) = 7e-11`, worst
`√(coreΦ·frobSq D)/(Sreg+coreΦ) = 7.5e-6` at t=1e-2; → 1e-21 / 2.6e-12 at t=1e-4).

**CAUTION — the `coreΦ`-only denominator is WRONG.** `frobSq(D) ≤ coreΦ/16` is FALSE under PRODUCT
cancellation: take `M1 ≥ 2`, `S0·S1 = 0` (e.g. `S0 = εT0 = ε[1,2]`, `S1 = εT1 = ε[2;−1]`, `T0·T1 = 0`),
then `coreΦ = 0` but `frobSq(D) = frobSq(S0·K·S1) > 0` ⇒ `frobSq(D)/coreΦ = ∞`. (Verified — ratio 1e20+.)
This is reachable (T_s are free core coords). It does NOT break the FOLDED form, because there
`Sreg = Θ(t²)` dominates the Θ(t⁴) cores; the `(Sreg+coreΦ)` denominator absorbs it.

**The one genuine residual obligation for the formaliser — and a route WITH A HOLE to avoid.**
The clean target is the DIRECT charge `(♦) : ∀ᶠ w on S5a, |Score − coreΦ| ≤ ½·(Sreg + coreΦ)`. Verified
ROBUST under BOTH cancellations (prodcancel: 0.61→3.3e-4; generic: 1.1e-3→1.1e-7; both Θ(t²)→0).

**HOLE (do NOT use):** the tempting route `frobSq(D) ≤ frobSq(K)·frobSq(S0)·frobSq(S1)` (banked
sub-mult.) + "factor out frobSq(K) → 0, bound the rest" **FAILS** — EVERY candidate
`frobSq(D)/(frobSq(K)·denom)` has an UNBOUNDED constant under product-cancellation (verified: 1e6→1e10
for denom = `Sreg+coreΦ`, `Sreg+Score`, `coreΦ`, `Score` — all blow up like t⁻²). Reason: when `S0·S1`
cancels, `frobSq(S0)·frobSq(S1)/(Sreg+coreΦ)` is unbounded (1e6→1e10), so factoring `frobSq(K)` loses a
correlated higher-order cancellation. The crude sub-multiplicative bound is NOT enough.

**What IS true and clean:** `frobSq(D)/(Sreg+coreΦ) → 0` directly (worst 7e-11 at t=1e-2, Θ(t²)→0), and
`(♦)` directly. But the PROOF of `(♦)` needs the genuine leading-order structure, not the banked
sub-mult pieces alone. **Recommended decomposition for the formaliser:**
  - `Score − coreΦ = 2⟨B,D⟩ + frobSq(D)` (banked (iii)). Charge each:
    `frobSq(D) ≤ frobSq(D)` trivially, and the cross `|⟨B,D⟩| ≤ √(coreΦ·frobSq D)` (banked (iv)).
  - So `(♦)` reduces to: **`frobSq(D) ≤ ⅛(Sreg+coreΦ)`** (R1) and **`√(coreΦ·frobSq D) ≤ ⅛(Sreg+coreΦ)`**
    (R2), both ∀ᶠ on S5a. R2 follows from R1 + `coreΦ → 0`-or-bounded via AM-GM
    (`√(coreΦ·frobSq D) ≤ ½(ε·coreΦ + ε⁻¹·frobSq D)`), so **R1 is the load-bearing residual.**
  - R1 (`frobSq(D) ≤ ⅛(Sreg+coreΦ)` ∀ᶠ) is the TRUE remaining geometric content. It does NOT reduce to
    ANY "factor out the K-energy" bound: `frobSq(S0·K·S1) ≤ C·frobSq(K)·(denom)` blows up under product
    cancellation for denom ∈ {coreΦ, Score, Sreg+coreΦ, Sreg+Score} (1e6→1e10), AND the operator-norm
    `frobSq(S0·K·S1) ≤ ‖K‖²_op·coreΦ` is FALSE too (48 violations, →1e17) — because `K` is sandwiched
    INSIDE `S0·K·S1`, so it re-aligns factors that cancel in `S0·S1` (= coreΦ). **No norm-factoring route
    closes R1.** R1 is TRUE because of a CORRELATED higher-order cancellation (when `S0·S1` cancels,
    `Sreg` or the deviation structure compensates), which needs the genuine LEADING-ORDER (Taylor) germ
    analysis in the chart coordinates, tying `frobSq(D)`, `Sreg`, and `coreΦ` to the same small parameter.

**Honest status of the repair:** items 1–3, 5 are SETTLED and decorrelated-confirmed (the additive route
is dead on a reachable chart curve; the folded statement and squeeze survive; the bridge shape is
`(♦) ⇒ γ₁=γ₂=2`). Item 4's residual `(♦)`/R1 is TRUE (verified numerically, robust under both
cancellations, Θ(t²)→0) but its clean Lean PROOF is NOT pinned — **every crude factoring route (Frobenius
sub-mult, operator-norm) has a hole.** R1 is a genuine germ-analysis lemma (leading-order Taylor in the
chart, NOT abstract block algebra). **RECOMMENDATION:** before the formaliser commits, a follow-up
pen-and-paper pass should pin the leading-order proof of R1 (or restate the bridge to take `(♦)` as a
named hypothesis discharged by a dedicated germ lemma `core_germ_charge : ∀ᶠ w, |Score − coreΦ| ≤
½(Sreg+coreΦ)`, proven by Taylor). The bridge + folded conjuncts + squeeze wiring (items 1–3) can be
built immediately against that hypothesis; R1 is the isolated remaining `sorry` (CORRECT statement, the
genuine open content) — strictly smaller and better-scoped than the refuted additive `sorry`.

## 5. CRITICAL reachability check — SETTLED: the counterexample IS reachable, re-architecture IS needed

Built at the RAW PARAMETER level (raw layers `W0(t), W1(t)`, actual product, actual
`dlnLoss = ‖W0 W1 − B‖²`), identity endpoint frames (corner-clean, the producer's interior-trivial
regime), `cond(P00) = 1.00` exactly (`/tmp/h2confirm/chart_reachability.py`):

| shape | t=1e-4: Sreg | coreΦ | gap/Sreg | loss/(Sreg+coreΦ) |
|---|---|---|---|---|
| r1 H322 | 1.16e-26 | 1.02e-17 | **91.4** | 1.0000 |
| r1 H333 | 1.31e-25 | 4.90e-15 | **608** | 1.0000 |
| r2 H433 | 2.01e-25 | 1.03e-16 | **23.6** | 1.0000 |

The curve (`A1 = A0⁻¹(I − Y0·Z1)` ⇒ `P00 = I` exactly; `Z0` nulls `P10`; `Y1` shrinks `P01` to Θ(t³)):
- **IS a genuine chart path** — the reg/gauge reads are free independent coordinates
  (`regGaugeSlotEquiv` is a homeomorphism; `RegGaugeIdx = Σ_s ((X_s)⊕(Y_s)⊕(Z_s))` has all blocks for
  both layers, `DeepestSplitReindex.lean:322`). The "reg slot reads only the boundary generators
  `X_0,Y_1,Z_0`" (`:373-428`) but `X_1, Y_0, Z_1` are free SPECTATOR coords — and `P00,P01,P10` are
  PRODUCT blocks that depend on the spectators, so the spectators shrink `Sreg` without being charged.
- **breaks the additive bound:** `gap/Sreg → const`, unbounded in the tuning scale λ (`~2/λ²`); with
  `P01 = 0` (λ = 0) it fails POINTWISE (`Sreg = 0`, gap > 0). [Codex decorrelated, `xhigh`, independently
  confirmed reachability + the λ=0 pointwise failure: `codex/h2-reachability-answer.md`.]
- **the squeeze SURVIVES on this very curve:** `loss/(Sreg + coreΦ) → 1.0000`.

**Verdict:** the chart does NOT exclude the curve; the additive route is dead on the real domain; the
re-architecture (items 1–2) is required. The failure is enabled by the spectator status of `Y0, Z1`
(they build `K = Z1·⅟P00·Y0` un-charged by `Sreg`) and `X1` (cancels `P00` at no reg cost) — Codex's and
my independent diagnosis agree exactly.

---

## Build checklist (for the formaliser)
1. State + prove `(★)` as a corollary of `schur_core_germ_comparability` (~3 lines: sqrt + abs). [READY]
2. State + prove the abstract bridge `fold_comparability_of_core_relative` (item 3 NEW lemma, ~30 LoC),
   taking `hcharge : ∀ᶠ w, |Score − coreΦ| ≤ ½(Sreg+coreΦ)`, witness `γ₁=γ₂=2`. Replaces
   `germ_charge_of_schur_factorization`; delete the dead bridge + its `hRem`. [READY — pure inequality algebra]
3. **The residual (item 4):** discharge `core_germ_charge : ∀ᶠ w on S5a, |Score − coreΦ| ≤ ½(Sreg+coreΦ)`
   = `(♦)`. **NOT READY — genuine germ-analysis open content.** Every norm-factoring route has a hole
   (verified). Needs leading-order Taylor in the chart. **Recommend a follow-up pen-and-paper pass to pin
   the leading-order proof BEFORE the formaliser commits; until then this is the single isolated `sorry`
   (correct statement).** It is strictly smaller/better-scoped than the refuted additive `sorry`.
4. In the producer, replace the `sorry` + `refine ⟨1, 1+C, 1+C, 1, 1, …⟩` with the bridge's
   `γ₁=γ₂=2` output feeding `hcore_le`/`hcore_ge`. Wire `D` from `rcore_schur_factor_of_corner_split`
   (`D = Rcore − S0·S1`, `S_s` its cores), `coreΦ = frobSq(S0·S1)` from `deepestCoreF_coreAbsorb_eq_prodSchur`. [READY once 2,3 land]
5. `deepest_loss_squeeze` (:2794) UNCHANGED — re-build to confirm it still consumes `hcore_le`/`hcore_ge`. [READY]

## Artifacts (re-runnable; mine, not pp's)
- `/tmp/h2confirm/chart_reachability.py` — raw-parameter-level curve: reachable, additive broken, squeeze survives.
- `/tmp/h2confirm/refute_scan3.py`, `codex_curve.py` — the P00=I cancellation refutation (abstract + exact).
- `/tmp/h2confirm/symbolic_order3.py` — exact generic order (gap = Θ(Sreg³) off the cancellation set).
- Codex: `codex/h2-confirm-order-prompt|answer.md` (order), `codex/h2-reachability-prompt|answer.md` (reachability).
- `(★)` and the bridge verified: see `/tmp/h2confirm/` (0/20000 violations on (★); 1251/20000 on the wrong variant).
