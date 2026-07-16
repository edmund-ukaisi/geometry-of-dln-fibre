# Mixed-degeneration `b<j` regime (Q_p-degeneration) — VERDICT: **OUTCOME (b): ABSORBED. NO hole.** (□) is sound as routed in the `b<j` regime.

**Seat:** pen-and-paper (OBSTRUCTION-primary / witness-fallback, decorrelated), aoyagi-full Stage 2,
`genm-bltj`. **Date:** 2026-07-15. **NO Lean, NO build.** Exact algebra (SV-measure radial exponents,
codimension strata, matrix-product RLCT = ½·minAdm, subset-monotonicity) + numerics as GUIDE only
(`mixdegen_mc_guide.py`, `mixdegen_shell_mc.py`) + decorrelated `local-codex-consult` (xhigh, gpt-5.x,
my conclusion WITHHELD, prompt framed "argue whichever way"): `codex/mixdegen-{prompt,answer}.md`.

**Cross-read (verified against, not paraphrased):** `genm-incidencepp/incidence-cert.md` §3/§3b (C_{ℓ,s},
charts 4–5), `genm-t2adjud/t2-bridge-adjudication-cert.md` §2 (the G~σ_min⁻¹ blow-up, exact-codim method),
`genm-shelljhunt/shellj-verdict-cert.md` §2 (λ_j = ½min_{s≤R_j}codim, subset one-liner),
`genm-thresholdhunt/threshold-verdict-cert.md` §2 (off-shell RLCT = ½minAdm).

---

## ★ VERDICT

On the `b<j` probe `M=(3,3,7), u=2, j=2, b=1` (a=b=1, `b=1<j=2`; `r≥3`), and at general arity:

- **The brief's POINTWISE observation is CORRECT.** The inner (front) integral's local threshold is
  `c'=T1=9/2` for `σ_min(Q_p)>0` (generic), and **DROPS to `c'=3`** as `σ_min(Q_p)→0` with `Q_b` generic
  (hsQ corank 1), and further to `c'=3/2` at the exact shell-2 limit (hsQ rank 1). `decLoss` **is** `O(1)`
  on that locus. All three of the brief's numbers check out **pointwise**.
- **The brief's INFERENCE is FALSE.** The **integrated** shell object does **NOT** diverge on `[3, 4.5)`.
  Both the undecorated object `I_j` and the decorated object `G` are **finite for all `c' < T1 = 9/2`**,
  first diverging (log) exactly at `c'=9/2`. The pointwise blow-up is absorbed by the singular-value
  measure on the small SVs (a codim-12 outer volume), and the **binding stratum is the front-vanish
  `T→0` at generic full-rank shell points** (threshold exactly `9/2`), NOT the `Q_p`-degeneration.
- **This is outcome (b), not (a).** The `C_{ℓ,s}` stratification **does** enumerate the `b<j` /
  `Q_p`-degeneration strata (via `ℓ=rank W`, with `rank hsQ = b + ℓ`); nothing was missed. The
  exponent-collapse is correct: `min_{ℓ,s} C_{ℓ,s}/2 = T1_q` holds and the `Q_p`-degeneration strata do
  not undershoot. **No reshape of (v) is required.** One fidelity caveat for the formaliser (§4).

**Triple-confirmed:** exact algebra (3 independent derivations of `9/2`) + MC guide + decorrelated Codex
(independent, no repo access — reached "FINITE to 4.5" and the same exact SV-measure exponents `11/2`).

---

## 1. The object and the danger locus (verified against the code-facts in the cross-read certs)

`L=0` leaf, `M=(3,3,7)`, cut `u=2` ⟹ `a=M₀−u=1`, `b=M₁−u=1`, `d=M₂−b=6`, `ab=1`.
`minAdm(M)=min_r[(3−r)(3−r)+7r]=9` at `r=t★=0` ⟹ `T1=9/2`; `r=min(M₀−t★,M₁−t★)=3`; `u=t★+j ⟹ j=2`, so
`b=1 < j=2` (the `b<j` regime, first reachable at `r≥3`, confirming the brief's scope).

- `Q_p = z` (u×M₂ = 2×7, free box), `Q_b = A_cor` (b×M₂ = 1×7, free box), `hsQ = (Q_p;Q_b)` (3×7 = M₁×M₂).
- Front `T=[P|B]` (M₀×M₁ = 3×3) + transverse `C`; undecorated loss `frobSq(T·hsQ)`.
- **The shell forces `σ_min(Q_p)→0`:** on shell-`j=2`, `hsQ` (3 SVs) has 2 SVs `<ε`, so `rank hsQ → 1` in
  the closure. Since `Q_b` (1 row, generically `O(1)`) already supplies the one surviving direction,
  `rank Q_p → 1`, i.e. `σ_min(Q_p)→0`. The `j−b = 1` "extra" small SV is forced into the pivot block —
  exactly the brief's diagnosis. (Verified: if `rank Q_p = 2` both SVs `O(1)`, then `rank hsQ ≥ 2`, two SVs
  `≥ε`, contradicting shell-2. So shell-2 ⟹ `σ_min(Q_p)→0` on the whole closure.)

**The decorated object** (incidence-cert §1, on the `rank Q_b=b` chart `Q_b=D[I|X]`, `Q_p=[U|UX+W]`,
`W:=Q_p·N` the u×d incidence coordinate; integrate out part of the front ⟹ `det(Q_bQ_bᵀ)^{−a/2}`, shift
`c'→q=c'−ab/2`), after the unimodular shears (incidence-cert §3b charts (1)–(4)):

    G  =  ∫_{outer, shell}  det(Q_bQ_bᵀ)^{−a/2} · [ ∫_{H̃,Y} ( ‖H̃‖² + ‖Y·W‖² )^{−q} ] ,
    H̃∈ℝ^{ub}=ℝ², Y=(P;C)∈ℝ^{M₀×u}=ℝ^{3×2}, W∈ℝ^{u×d}=ℝ^{2×6}.

Key structural fact: **the inner integrand depends on `W`, not on `U`** — `U` (the projection of `Q_p`
onto `row Q_b`) is absorbed by the front shear `H=PU+BD`. `σ_min(Q_p)→0 ⟺ rank[U|W]≤u−1 ⟹ rank W ≤ u−1`,
so the pivot degeneration is carried by `rank W = ℓ` (Codex-confirmed identity `rank hsQ = b + ℓ`).

## 2. The exact thresholds (Deliverable 1) — POINTWISE drops to 3, INTEGRATED stays 4.5

**Pointwise inner threshold** at fixed outer point. For fixed `W` of rank `ℓ`, `‖Y·W‖²` is a PSD form of
rank `M₀ℓ` in `Y`; with `H̃` (dim `ub`) the active directions number `ub+M₀ℓ`, so the inner integral is
finite iff `q < (ub+M₀ℓ)/2`, i.e. `c' < (ub+M₀ℓ+ab)/2 = 3/2·(1+ℓ)`:

| `rank W = ℓ` | `rank hsQ = b+ℓ` | corank hsQ | inner `c'`-threshold | note |
|---|---|---|---|---|
| 2 | 3 | 0 | **9/2 = T1** | `σ_min(Q_p)>0` generic |
| 1 | 2 | 1 | **3** | `σ_min(Q_p)→0`, `Q_b` generic — **the brief's "3"** |
| 0 | 1 | 2 | 3/2 | exact shell-2 limit (`W=0`, full incidence) |

Equivalently (undecorated, t2adjud method): for fixed `hsQ` of corank `k`, `∫_T frobSq(T·hsQ)^{−c'}`
finite iff `c' < M₀(M₁−k)/2`; `k=1 ⟹ c'<3`. **The pointwise "3" is a FACT.** ✓ (MC guide (B): slopes
→ 2.8→3.0; (C) full-rank → 4.5.) Codex Section A: `c'_pt<3R/2`, `R=rank`, identical.

**Integrated threshold** of `G` (and of `I_j`) — three independent exact derivations, all `9/2`:

1. **Reduction to a matrix-product RLCT.** `∫_{H̃,Y,W}(‖H̃‖²+‖Y·W‖²)^{−q}` has RLCT `λ_q = μ + ub/2`,
   `μ = RLCT(‖Y·W‖²) = ½·minAdm(M₀,u,d) = ½·minAdm(3,2,6) = 6/2 = 3` (the paper's own 2-layer codim /
   thresholdhunt smooth-point equality). `λ_q = 3 + 1 = 4` ⟹ `c'`-threshold `= 4 + ab/2 = 9/2`.
2. **Incidence `C_{ℓ,s}` min** (incidence-cert §3, re-derived): `C_{ℓ,s}=ub+M₀ℓ+(M₀−s)(u−ℓ−s)+s(d−ℓ)`,
   `min = 8` at `(ℓ,s)∈{(0,0),(1,0),(2,0)}` ⟹ `min/2 = 4 = T1_q`. Note `C_{ℓ,0}=ub+M₀u=8` is
   **independent of `ℓ`** — the binding front-vanish stratum is flat in `rank W`.
3. **Binding stratum = front-vanish at generic `W`.** `{H̃=0,Y=0}` (front→0) has codim `ub+M₀u = 8`
   uniformly in `rank W`; radial `∫₀^δ r^{8−2q−1}dr` finite iff `q<4 ⟺ c'<9/2`.

**The `Q_p`-degeneration locus is NOT binding — it absorbs to `c'<11/2`** (Deliverable 1, exact
SV-measure). Pointwise near a rank-1 `W`, `I(W) ≍ σ_2(W)^{5−2q}` (blows up for `q>5/2`, i.e. `c'>3`). But
the `2×6` singular-value measure carries `σ_2^{d−u}=σ_2^{4}dσ_2`, so integrated:
`∫₀ σ_2^{(5−2q)+4}dσ_2` finite iff `q<5 ⟺ c'<11/2`. Codex independently: the `3×7` SV measure
`s⁴t⁴(s²−t²)dsdt`, `F(s,t)≍s^{−3}t^{6−2c'}`, gives `ρ^{14−2c'}τ^{10−2c'}` ⟹ absorbs to `c'<15/2` and
`c'<11/2` — **exact agreement on `11/2`.** So the `σ_min(Q_p)→0` locus is finite well past `T1`.

**`decLoss` order on the locus (Deliverable 1).** comparator base `commonDivisor²·‖Q_p‖²_F`: on
`σ_min(Q_p)→0`, `‖Q_p‖²_F = σ₁²+σ₂² → σ₁² = O(1)` (floored), `commonDivisor` floored ⟹ base `= O(1)`,
integrand `O(1)`. **`decLoss` is `O(1)` there — the brief/operator assertion is TRUE.** Its RLCT overall
is `½·minAdm(redChain u M) = uM₂/2 = 7` in `q` (`c'<15/2`), so `comparator.integral` is finite far past
`T1`. The domination `G ≤ K·comparator.integral` therefore holds for `c'<9/2` (both sides finite),
per-exponent `K ∼ 1/(T1−c')`. **No divergence of `G` on `[3,9/2)` ⟹ domination NOT broken.**

## 3. The general-arity verdict (Deliverable 2): OUTCOME (b) — the mechanism, explicitly

**Absorbing mechanism (why the pointwise "3" is moot).** The domination is **INTEGRATED, not pointwise**
— exactly the incidence-cert's own Verdict-1. The `σ_min(Q_p)→0` locus is measure-suppressed: the box
measure on `hsQ` (3×7) gives its small singular values the Jacobian weight `σ^{n−m}=σ^{4}` each
(**MC-confirmed:** `P(σ_min<t)~t^{4.88}≈t^{5}=t^{n−m+1}`; and `σ_2<0.3` is essentially never sampled in
1.5M box draws — shell-2 is genuinely rare, *because* the absorption is strong). Integrated against the
pointwise blow-up, the `Q_p`-degeneration converges to `c'<11/2 > T1`. The binding is the front-vanish
`T→0` at generic full-rank shell points, `c'<9/2 = T1`, marginal (log divergence at `9/2`).

**Rigorous general no-go against the drop (the OBSTRUCTION certificate).** Subset-monotonicity in the
true `(Q_p,Q_b)` box coordinates:

    G_shell(c')  =  ∫_{shell-j ⊆ full box} g   ≤   ∫_{full box} g  =  G_offshell(c'),   g ≥ 0 the same integrand.

`G_offshell` is finite for `c' < T1 = 9/2` (off-shell decorated RLCT `= T1`, §2 derivations 1–3; and the
undecorated `∫_{full}∫_T frobSq(T·hsQ)^{−c'}` is the pure matrix-product RLCT `= ½·minAdm(3,3,7) = 9/2`,
`u`-independent, thresholdhunt). Since shell-`j` is a **subset** of the full box with the **same
nonnegative integrand**, `RLCT(G_shell) ≥ RLCT(G_offshell) = T1`. **This holds at general arity and for
every `1≤j<r`** — the off-shell = `T1` claim is the incidence-cert's exhaustive result (332/332 in-scope
cuts, widths 2..8), and the `b<j` / `Q_p`-degeneration strata are a subset of those `(ℓ,s)` strata.
(Codex endorses subset-monotonicity for `U`, and for `G` relative to its own off-shell once the
transformed measure is included; it flags that a *direct* `G ≤ I_j` is invalid — the two displayed
integrands differ — which my argument does not use.)

**Not a new regime.** The incidence-cert's Verdict-1 counterexample to the *pointwise* bound was
`(3,3,5)@u=2` (`δ^{5−2q}` blow-up at `q=5/2 ⟺ c'=3`) — itself a `b<j` case (`a=b=1, j=2`), and the same
`rank Q_p`-drop phenomenon. So the `b<j` regime was, in substance, already exercised; the present probe
sharpens it and confirms the resolution holds.

## 4. Does `C_{ℓ,s}` enumerate `b<j` / Q_p-degeneration strata? (Deliverable 3) — YES

The `C_{ℓ,s}` stratification indexes `ℓ = rank W` (the transverse/incidence coordinate `W=Q_p·N`) and
`s = rank Y` (front). Since `rank hsQ = b + ℓ`, the corank of `hsQ` is `u − ℓ`, so `ℓ` runs over **all**
`Q_p`-degeneration depths from `ℓ=0` (deepest, `rank hsQ = b`, full incidence) to `ℓ=u` (generic). The
incidence-cert's chart (5) (the determinantal big-cell of `W`, §3b) **is** the `Q_p`-degeneration
resolution. So `(ℓ,s)` does index `Q_p`-degeneration, not only `Q_b`-corank; the `Q_b`-corank is the
*separate* `rank Q_b < b` big-cell (null in the closure, off the chart). The exponent-collapse
`min_{ℓ,s} C_{ℓ,s}/2 = T1_q` is **correct** — the `Q_p`-degeneration strata (`C_{ℓ,0}=ub+M₀u`) tie the
front-vanish minimum and never undershoot. **No missed stratum ⟹ outcome (b), not (a).**

**Statement-shape impact on (v): NONE.** The resolution as routed (the integrated incidence estimate,
`deeperFlag_shell_le` in its `c' < carrierThreshold M` scope) is sound in the `b<j` regime. The corrected
domination to state is the **INTEGRATED** one (do NOT reach for a pointwise `integrand ≤ integrand` — that
is false on the `σ_min(Q_p)→0` locus, as the incidence-cert already flagged):

    ∫_{shell-j} G(c')  ≤  K_{j,c'} · comparator.integral(c'−ab/2),   K_{j,c'} < ⊤,  per-exponent,  c' < T1.

**One fidelity caveat for the formaliser (Codex, [FACT]).** The decorated `G` must carry the correct
chart Jacobian: net `|det D|^{d−a}` (`=|det D|^{5}` here; a positive power, so `D→0` is integrable). If
`G` were instead written with flat `dD dX` and this Jacobian omitted, `det(Q_bQ_bᵀ)^{−a/2}=|det D|^{−a}`
alone would give `∫dD/|det D|`, divergent for **every** `c'` — a *different* object. This is a
build-fidelity check, not a soundness hole; the incidence-cert §3b charts already include `|det D|^{n−b−a−u}`.

## 5. Numerics (GUIDE only; exact algebra §2–§4 is load-bearing)

- `mixdegen_exact.py` (exact ℚ): the thresholds table, `C_{ℓ,s}` min = 8 = 2·T1_q, `μ=minAdm(3,2,6)/2=3`,
  the `11/2` absorption, the subset statement.
- `mixdegen_mc_guide.py`: (B) pointwise corank-1 hsQ slopes → ~3.0 (brief's "3"); (C) full-rank → ~4.5;
  (E) reduced joint off-shell → ~4.0 in `q` (`c'=4.5`). ((F) removed — it reweighted `W` near rank-1
  *without* the SV Jacobian, so it measured a different, wrongly-weighted integral; the SV-measure
  suppression is the whole point.)
- `mixdegen_shell_mc.py` (i): `P(σ_min(hsQ)<t)~t^{4.88}≈t^{5}` — the `σ^{n−m}` absorption confirmed; and
  shell-2 rejection is intractable *because* two small SVs are strongly suppressed (corroborates §3).
- off-shell undecorated `I_j` control: slopes climb 3.36→4.12 (slow small-loss tail, clearly heading to
  4.5, not 3).

## Close

- **Firmest result (OBSTRUCTION against the drop).** The integrated shell object (`I_j` and `G`) is
  **finite to `c' = T1 = 9/2`** in the `b<j` regime — proven by subset-monotonicity from the off-shell
  object (RLCT `= T1` exactly, three ways), general at all arity/`j`. The brief's pointwise "3" (and
  "3/2") and "`decLoss` O(1)" are all correct **pointwise facts**, but the inference "`G` diverges on
  `[3,4.5)`" is the pointwise fallacy the incidence-cert's Verdict-1 already warned against. **Outcome
  (b): absorbed. `(□)` sound as routed. No reshape of (v).**
- **Most likely thing to break it.** (i) A formalisation that omits the chart Jacobian `|det D|^{d−a}`
  (then the object diverges for all `c'` — a different, false object; §4 caveat). (ii) A build that
  states/uses a *pointwise* domination (`integrand ≤ C·integrand`) — false on the `σ_min(Q_p)→0` locus;
  must be the integrated `∫shell ≤ K·∫comparator`. (iii) If the incidence-cert's off-shell `= T1`
  exhaustive claim had a gap at some non-`b<j` cut — outside my scope here, but the subset argument
  inherits from it.
- **Next construction/consult to settle the open part.** The `b<j` question is settled. The only residual
  is generic to the whole route (not `b<j`-specific): a decorrelated confirmation that the incidence
  `min_{ℓ,s} C_{ℓ,s}/2 = T1_q` per-stratum ratio `K_{ℓ,s} < ⊤` holds beyond the corner + the two strata
  worked here — i.e. fold this `b<j` confirmation into the incidence-cert's constructive-`K` closure.
