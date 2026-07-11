# genm-vsastruct — A₂-audit of `RouteMSJOnePeel334.lean` (gates the (□)-core bank)

**Seat:** pen-and-paper (fidelity / soundness audit). **Date:** 2026-07-11. **NO Lean edits.** **Charge:**
audit the landed one-peel before banking (the (□)-core, audited hardest). **Decorrelated:**
`codex/audit-{prompt,answer}.md` (gpt-5.6, xhigh; my lean withheld — it CONFIRMED the arithmetic and
SHARPENED the casting fidelity with a divergence counterexample). Audited file:
`lean/DLNFibre/DLN/RLCT/Validate/RouteMSJOnePeel334.lean` (351 LoC). Design spec: `onepeel-tonelli-cert.md`.

---

## VERDICT — PASS (bank the clean-coords core), with a naming scope-mark + a LOAD-BEARING casting caveat

**The landed lemma `onePeel334_lt_top` is SOUND and is the RIGHT (cert-§2-faithful) object: it proves the
CLEAN-COORDINATES one-peel `∫_{X∈box⁸}∫_{Z∈box⁴} S(‖X‖²,‖Z‖²;c') < ⊤` at `c'<7/2`, by the min-cut
weighted-AM-GM (codims ADD → exactly 7/2, not the 3/2 min) + Tonelli into banked Morse integrals, with only
the null singleton `{∑X²=0}` dropped (complement genuinely closed). BANK it. Recommend scope-marking the
name (`_cleanCoords_`). BUT the deferred A₂-casting is a genuine finiteness-preserving CoV ONLY under
`det[w₁;w₂;v̄]≠0` + exact/coercive units — this is LOAD-BEARING, not benign (Codex divergence
counterexample), and the casting follow-on MUST carry + PROVE those hypotheses or it is a hidden gap.**

## 1. Codim-fullness — PASS

The clean model uses `m₀=7 → d₀=m₀+1=8`, `m₁=3 → d₁=m₁+1=4`, faithful to cert §2's `(d₀,d₁)=(8,4)` (the
`(w₁,w₂)`-block codim 8, the `v̄`-block codim 4). The Morse rescue needs `d_k ≥ h_k+1`: `8≥4`, `4≥3` — slack,
non-binding. Binding is the two `u`-marginals, which at the min-cut weights `w=(4/7,3/7)` COINCIDE at
exactly `7/2` (verified: `(h₀+1)/(2w₀)=(h₁+1)/(2w₁)=7/2`). The deep Morse rescues are non-binding (X-Morse
finite for `c'<7`, Z-Morse for `c'<14/3`, both `>7/2`). Arithmetic confirmed. [PASS.]

## 2. FIDELITY — PASS-CONDITIONAL (the load-bearing point, decorrelated-sharpened)

**The abstract `cornerSliceAtUnits` over clean coords IS the right object** (faithful to cert §2): the
deep integral is posed in `(X∈ℝ⁸, Z∈ℝ⁴)` with `U₀=‖X‖²`, `U₁=‖Z‖²` — exactly cert §2. `corner334`'s
Fin-2-row slice is the `(3,2)`-Jacobian INSTANCE (`cornerSlice334Integral_eq_atUnits`, a `rfl` bridge), used
for the slice STRUCTURE, not the codim-faithful literal — so the dimension-model tension is resolved
correctly: the abstract clean-coords is the right formulation, the Fin-2-row is a partial instance. [OK.]

**The deferred A₂-casting `A₂ ↦ (X,Z) = (w₁A₂,δw₂A₂ ; a_piv·v̄A₂)` is a genuine CONSTANT-JACOBIAN,
finiteness-preserving CoV** — `L = I₄⊗N`, `N = diag(1,δ,a_piv)·M`, `M=[w₁;w₂;v̄]`, Jacobian
`|δ·a_piv·det M|⁴` (constant), plus the domain enclosure `L([−1,1]¹²) ⊂ [−T,T]¹²` for `T` large (`f≥0`,
monotone) ⟹ `J_literal ≤ |Jac|⁻¹·J_clean(T) < ∞`. It is NOT generally measure-preserving (only if `M`
orthogonal and `|δ|=|a_piv|=1`), but finiteness-preserving suffices. [FACT — Codex Q1/Q2, exact.]

**★ BUT this is NOT a benign chart hypothesis — it is LOAD-BEARING.** [Codex Q3, decisive]
- **Divergence counterexample:** `w₁=w₂=v̄=e₁` (`M` rank 1). Then `U₀=(1+δ²)q`, `U₁=a_piv²q`,
  `q=‖e₁A₂‖²`, so `S = q^{−c'}·S(const)` and `J_literal ⊇ ∫_{ℝ⁴}‖x‖^{−2c'}dx`, which **DIVERGES for
  `c'≥2`** — even though `J_clean<∞` for `c'<7/2`. So a SINGULAR casting makes the literal integral diverge
  while the clean model converges. **The invertibility `det M≠0` is load-bearing.**
- Codex's exact rule: `codim{U₀=0}=4·rank[w₁;w₂]`, `codim{U₁=0}=4·rank(v̄)`, `codim{U₀=U₁=0}=4·rank M` —
  so `M` singular can leave the individual codims full while collapsing the joint one, and ambient
  12-dim clean integrability does NOT control the singular pullback.
- **The units must be EXACTLY the clean `‖·‖²` forms** (they are, per vslice §5: `U₀=‖(w₁A₂,δw₂A₂)‖²`,
  `U₁=‖a_piv·v̄A₂‖²`, NO cross-terms). If the actual post-reduction units differ, the clean lemma applies
  only via PROVEN uniform coercive comparisons `U₀≥m₀‖X‖²`, `U₁≥m₁‖Z‖²` (`m_k>0`); positive-definite
  cross-terms whiten by another linear iso, but semidefinite/cancelling forms need a new coercivity argument.

**⟹ FIDELITY verdict:** the casting is a genuine finiteness-preserving follow-on, NOT a hidden gap —
**IFF the follow-on carries + PROVES:** (i) `det[w₁;w₂;v̄]≠0` (test directions a basis of ℝ³) —
**explicitly established by the chart construction** (the resolved front full-rank on the good chart), NOT
assumed benign; (ii) `δ,a_piv≠0`; (iii) exact unit-forms (or proven coercive `U_k≥m_k‖·‖²`); (iv) the
parallelepiped enclosed in a clean-lemma box (routine — the clean lemma is stated `∀ T>0`). **Without (i)+(iii)
it is a hidden load-bearing gap.** [PASS-CONDITIONAL.]

## 3. NAMING — recommend a scope-mark

`onePeel334_lt_top` proves `onePeelIntegral 3 2 7 3 T c' < ⊤` — the CLEAN-COORDS integral (casting
deferred). The def `onePeelIntegral` + the module header are HONEST (explicitly "clean coordinates (X,Z)",
"the A₂-casting … left as follow-on"). But the THEOREM name reads as the literal `(3,3,3,4)` one-peel. Per
the `corner334 _fiber` lesson + precision (name=content), **recommend `onePeel334_cleanCoords_lt_top`** (or
equivalent) so a reader scanning names sees it is the clean-coords model, not the literal one-peel. Precision
polish, NOT a soundness blocker (the docstring already caveats). [RECOMMEND.]

## 4. Standing gates — BOTH PASS

- **Charges ADD (not min):** the min-cut AM-GM `(u₀²A+u₁²B)^{−c'} ≤ (u₀²A)^{−w₀c'}(u₁²B)^{−w₁c'}` at
  `w=(4/7,3/7)` makes BOTH `u`-marginals coincide at exactly `7/2` (`= ½·Σp_k`), NOT the multiplicative
  `min = 3/2`. The codims-add mechanism is faithfully realised. [PASS — the min→sum fix is correctly in.]
- **Complement genuinely closed (not a.e.-drop):** only the null singleton `{∑X²=0}` / `{∑Z²=0}` is dropped
  (`measure_singleton`); the deep Morse integral `∫(∑X²)^{−w₀c'}` genuinely CONVERGES near the origin
  (that IS the codim rescue), it is not a positive-measure a.e.-deletion. [PASS.]

---

## Firmest / most-likely-to-break / next
- **Firmest.** The clean-coords lemma is sound, cert-§2-faithful, gives exactly `7/2` (codims add), complement
  closed. Codim-fullness `(8,4)` slack. Decorrelated-confirmed.
- **Most likely to break (the casting follow-on).** `det M≠0` is LOAD-BEARING (divergence counterexample
  `w₁=w₂=v̄=e₁` → `∫‖x‖^{−2c'}` diverges at `c'≥2`). The follow-on must PROVE the resolved front's
  full-rank on the chart, and that the literal units are exactly the clean `‖·‖²` (or coercive). Do NOT bank
  the casting as "measure-preserving/benign".
- **Next.** BANK `RouteMSJOnePeel334` (clean-coords core), with the naming scope-mark. COMMISSION the
  A₂-casting follow-on stating (i)–(iv) as explicit hypotheses, with `det M≠0` PROVEN by the chart
  construction — the casting is a genuine linear-CoV + enclosure, buildable-as-labour, but the basis/coercivity
  conditions are load-bearing, not free.
