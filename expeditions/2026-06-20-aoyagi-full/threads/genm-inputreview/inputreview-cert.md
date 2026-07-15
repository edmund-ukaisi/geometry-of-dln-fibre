# Brick-D input fidelity review — three consumed modules — VERDICT: **all three SURVIVED**

**Function.** Decorrelated fidelity review (own `local-codex-consult`, xhigh) of the three un-reviewed Brick D
input modules the capstone assembly will consume. Read-only on `origin/genm-sj5-brickdcont`; cross-read
against `genm-incidencepp/incidence-cert.md` §3/§3b. No build (branch assumed green; verified sorry/axiom
absence by grep, and all Mathlib lemma signatures used were confirmed against the local Mathlib checkout).

**Scope of "fidelity" here (report-only):** does each Lean statement match the informal claim in the cert —
no overclaim (esp. iff-vs-sufficiency, aggregate-vs-per-stratum), no vacuity, name denotes exactly what is
proven? I did not rewrite any mathematics.

**Bottom line.** All three faithfully state their claims; naming is precise; no overclaim, no vacuity. One
**advisory for the assembly** (not a defect in these modules): the exponent module's gate is a division-free
integer inequality, so any consumer forming `T1_q = (minAdm−ab)/2` and `C_{ℓ,s}/2` must divide in `ℝ`/`ℚ`, not
`ℕ` floor division (Codex flag; the modules themselves contain no division). Sorry/axiom/`native_decide`
absent in all targets and in the banked deps (`RouteMLayerSplit`, `Lambda`).

---

## Target 1 — `RouteMSJIncidenceChart4Polar.lean` — **SURVIVED**

Three theorems, all faithful to cert §3b(4) (`∫(‖H̃‖²+τ²)^{−q}dH̃ ≍ τ^{ub−2q}`, `τ=‖YW‖`).

- **`chart4_polar_scaling`** proves the EXACT identity `∫⁻(‖H‖²+τ²)^{−q} = ofReal(τ^{N−2q})·∫⁻(‖V‖²+1)^{−q}`.
  - *Exponent + direction correct.* Haar CoV `H = τ·V`: `dH = τ^N dV`, `‖H‖²+τ² = τ²(‖V‖²+1)`, integrand factor
    `τ^{−2q}`, net `τ^{N−2q}`. The Lean uses `Measure.map_addHaar_smul` at `r = τ⁻¹` with Jacobian
    `|((τ⁻¹)^N)⁻¹| = τ^N` (confirmed via `finrank_euclideanSpace_fin = N`). Matches.
  - *This is STRONGER than the cert's `≍`* — the constant `K` is named, not absorbed. Not an overclaim: a
    precise equality where the cert wrote a comparability. Good.
  - *No `q`-hypothesis (any real `q`) is sound.* Lower-integral CoV needs no integrability. When `K = ⊤`, the
    scale `ofReal(τ^{N−2q})` is strictly positive and finite, so RHS `= ⊤` too — no `0·⊤` ambiguity, identity
    holds in every case. Not vacuous.
- **`chart4_unit_lintegral_lt_top`** proves `K = ∫⁻(‖V‖²+1)^{−q} < ⊤` when `(N:ℝ) < 2q`.
  - *Correct threshold, sufficiency only.* Reuses Mathlib `integrable_rpow_neg_one_add_norm_sq` (confirmed
    signature: `(finrank ℝ E : ℝ) < r ⟹ Integrable (1+‖x‖²)^{−r/2}`) at `r = 2q`, exponent `−(2q)/2 = −q`,
    `finrank = N`. At infinity `∫ r^{N−1−2q}dr` converges iff `2q > N`, so `N/2` is the exact `q`-threshold.
  - *No iff overclaim.* Name is `_lt_top` (proves `< ⊤`); statement is a one-directional implication. The
    docstring explicitly states necessity (`K<⊤ ⟹ 2q>N`) is NOT formalised. Name denotes exactly what's proven.
  - *Not vacuous.* `2q > N` satisfiable (e.g. `q = N+1`).
- **`chart4_Htilde_fibre_lt_top`** (`τ>0, 2q>N ⟹ fibre < ⊤`) is the faithful composition of the two.
- **`N = ub`?** The module is parametric in `N`; the docstring correctly identifies `N = u·b` for the
  application. Binding `N := ub` is an assembly-side concern (documented), not a defect here.

**Codex (decorrelated):** FAITHFUL. Independently derived `τ^{N−2q}`, confirmed `2q>N` convergence, confirmed
sufficiency-not-iff, confirmed unrestricted-`q` soundness (positive finite scale ⟹ no `0·⊤`). Noted `N=0`
edge (integral finite for all `q`; `2q>0` still a valid sufficient condition) — no issue.

---

## Target 2 — `RouteMSJIncidenceGluing.lean` — **SURVIVED**

Two theorems, faithful to cert §3b "null-overlap gluing".

- **`lintegral_lt_top_of_finite_cover`** (`Fintype`): `μ(D\⋃C)=0` + `∀i, ∫⁻_{C i} f < ⊤` ⟹ `∫⁻_D f < ⊤`.
  Statement matches the claim exactly. Proof chain: `lintegral_mono_set'` (via `ae_le_set.mpr hcover`:
  `D ≤ᵐ ⋃C`) → `lintegral_iUnion_le` → `tsum_fintype` → `ENNReal.sum_lt_top`.
- **`lintegral_lt_top_of_finset_cover`** (`Finset`): the `↥s`-subtype reduction to the `Fintype` core; the
  `⋃ i:(s:Set ι), C i = ⋃ i∈s, C i` reindex is correct.

Fidelity checks, all clear:
- *No hidden / too-strong hypothesis.* There is **no** measurability hypothesis on `C`, `D`, or `f`. This is
  sound and makes the lemma MORE general (not a hidden gap): the key step `∫⁻_{⋃C} f ≤ ∑' ∫⁻_{C i} f` is
  Mathlib's unconditional `lintegral_iUnion_le [Countable β]` (proved via `restrict_iUnion_le`, valid for
  arbitrary sets and arbitrary `f : α → ℝ≥0∞`; `Fintype ⟹ Countable`). Confirmed against the local checkout.
- *Not vacuous; no secret exact-cover.* Coverage is only up-to-null (`μ(D\⋃C)=0` ⟹ `D ≤ᵐ ⋃C`), exactly the
  claim — it does NOT require `D ⊆ ⋃C` literally. Hypotheses satisfiable.
- *Atlas-parameterization is honest.* Cells + coverage are hypotheses; the docstring's claim that the lemma is
  robust to any `genm-bltj` verdict (bltj reshapes `C`/`hcover`, never this gluing logic) is accurate — bltj
  only affects the supplied hypotheses.

**Codex (decorrelated):** FAITHFUL. Confirmed no missing measurability (`restrict_iUnion_le` unconditional),
`≤ᵐ` from `μ(D\U)=0` sound, no secret exact-cover requirement, hypotheses satisfiable.

---

## Target 3 — `RouteMSJIncidenceExponent.lean` — **SURVIVED**

Faithful to cert §3/§5, and precisely scoped to the PER-STRATUM gate (no aggregate/coverage leak).

- **`clsCodim`** transcribes `C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ)` with `b=M₁−u`, `d=M₂−b` spelled
  as `M₂−(M₁−u)`. Exact match. (Total ℕ function; every consuming theorem guards it with feasibility, so the
  truncated-subtraction value is only asserted where honest.)
- **`clsCodim_add_ab_eq`** proves `C_{ℓ,s} + ab = (M₀−s)(M₁−s) + s·M₂` (cert §3 ℓ-independence identity).
  Verified by hand over ℤ: LHS expands to `M₀M₁ − M₀s − M₁s + s² + sM₂` after the ℓ-terms
  (`M₀ℓ − (M₀−s)ℓ − sℓ`) cancel exactly; RHS `(M₀−s)(M₁−s)+sM₂` is identical. The `zify [h0..h7]` guards cover
  every truncated subtraction (`M₀−u, M₁−u, M₀−s, M₁−s, u−ℓ−s, M₂−(M₁−u), (M₂−(M₁−u))−ℓ`) from the four
  feasibility hypotheses, so the ℤ→ℕ transfer is valid.
- **`minAdm_arity3`** faithfully specializes the banked `minAdm` (= `((Adm M).inf' (Mval M)).toNat`, the
  minimal admissible zero-product-stratum codim, `Lambda.lean`) to arity 3, giving
  `min_{t≤min(M₀,M₁)}[(M₀−t)(M₁−t)+t·M₂]`. Route: `LayerSplit_value_eq_minAdm` (banked, sorry-free) +
  the `Fin 2` leaf `minAdm(redChain t M) = t·M₂` (via `minAdmRec_leaf`, `redChain_zero`, and
  `redChain t M 1 = M 2`). Correct — the leaf `(t, M₂)` product is `t·M₂`.
- **`clsCodim_gate`** proves the PER-STRATUM `minAdm M ≤ C_{ℓ,s} + ab` (⟺ `T1_q ≤ C_{ℓ,s}/2`) via
  `Finset.inf'_le` at `t = s` (needs `s ≤ min(M₀,M₁)`, from `s≤u≤min`). Direction correct for finiteness:
  `∫₀ r^{C_{ℓ,s}−1−2q}dr` converges near 0 iff `q < C_{ℓ,s}/2`, and `q<T1_q ⟹ q<C_{ℓ,s}/2`.
  - *Uses the FULL `minAdm M`* (min over `0..min(M₀,M₁)`), so `T1_q = (minAdm(M)−ab)/2` is **no larger** than
    a feasibility-restricted `T1`. Conservative (safe / weaker), not an overclaim.
  - **No aggregate/coverage leak.** The theorem asserts only the per-`(u,ℓ,s)` inequality — no equality of
    minima, no `min over the (ℓ,s) range = 2·T1`, no enumeration-completeness. This exactly matches the
    docstring SCOPE block and the cert §3 controller caveat (2026-07-15) that index-completeness on `b<j`
    cuts is under `genm-bltj` adjudication. The Lean stays strictly on the sound side of that line.
- **`minAdm_le_ab_add_uM2`** (comparator gate `T1_q ≤ uM₂/2`, cert §3 line 152) is the `ℓ=0, s=u` corner of
  the gate. Faithful.

*Advisory (assembly-side, not a module defect):* the gate is a division-free integer inequality
(`minAdm ≤ clsCodim + ab`). A consumer that reads it as `T1_q ≤ C_{ℓ,s}/2` must perform the `/2` in `ℝ`/`ℚ`
(matching the real exponent `q`), never `ℕ` floor division. The modules contain no `/2`, so this is a note
for whoever forms the halved thresholds downstream.

**Codex (decorrelated):** FAITHFUL. Independently expanded the ring identity over ℤ to `(M₀−s)(M₁−s)+sM₂`
(matching), confirmed the gate direction, confirmed full-min ⟹ conservative `T1` (not overclaim), confirmed
strictly per-stratum (no aggregate claim), confirmed truncated-ℕ subtractions all protected, hypotheses
non-vacuous (`M=(2,2,1),u=1,ℓ=0,s=1`), and raised the `/2`-in-`ℝ/ℚ` advisory above.

---

## Cross-check ledger (what I verified independently, beyond reading)

- Mathlib signatures confirmed against local checkout: `integrable_rpow_neg_one_add_norm_sq`
  (`finrank<r ⟹ (1+‖x‖²)^{−r/2}` integrable), `lintegral_iUnion_le` (`[Countable β]`, no measurability),
  `map_addHaar_smul`, `lintegral_mono_set'`, `ae_le_set`, `finrank_euclideanSpace_fin (= n)`.
- Ring identity `clsCodim_add_ab_eq` hand-expanded over ℤ (agrees with Codex).
- Banked `minAdm` chain read (`Lambda.Adm/Mval`, `RouteMLayerSplit.minAdm/minAdmRec/redChain/
  LayerSplit_value_eq_minAdm/minAdmRec_leaf`): `minAdm_arity3`'s specialization is faithful.
- sorry / admit / axiom / native_decide: absent in all three targets and in `RouteMLayerSplit`, `Lambda`.

**Verdict:** chart-4 **SURVIVED**, gluing core **SURVIVED**, exponent **SURVIVED**. The assembly may consume
all three as stated. Carry the `/2`-in-`ℝ/ℚ` advisory into the exponent-gate consumer.
