# genm-gatesclose2 — LEAF-2 close ASSESSED: the two gates are hard analysis, NOT a plug

Charged as the CLOSING tide for the L=2 headline: discharge the two analytic gates `hRne`
(slice non-vanishing) + `hInterface` (R1 degraded core) and plug into `hD1ge_L2_rect_of_gates`
to close `HeadlineL2Assembly.lean` LEAF 2 → sorry-free `aoyagi_learning_coefficient_L2`.

Per the "assess-first, don't over-reach / launder" directive, this tide FRONT-LOADED the two gates
before building. The verdict (decorrelated Codex xhigh, `codex/gates-answer.md`): **the gates as
literally stated in the ∀-`q` wire are NOT dischargeable** — one is false without an extra
hypothesis, the other is outright false ∀-`q`. Closing LEAF 2 requires genuine new analytic content
(3–4 lemmas) AND a re-architecture that binds `q`/`q₂` to the concrete producer residual. No wall
was laundered; the single LEAF-2 `sorry` is retained (green-with-one-sorry, as banked), its comment
now carries the precise finding.

Branch `origin/genm-gatesclose2` (from `origin/genm-b3closer` @ `79e08991`). One code change:
the LEAF-2 comment in `HeadlineL2Assembly.lean` (accurate roadmap); build unchanged
(green, one `sorry` at line 123).

## The two gates (exact, from `d1ge_L2_rect_two_peel_hrank_closed` / `hD1ge_L2_rect_of_gates`)

Both are stated **∀ `q` (a `ContDiff ℝ 2` residual)** with the chart-transfer equation as a
hypothesis, and consumed by the producer at its OWN constructed `q`.

* **`hRne`**: ∀ `C²` `q`, `q(0,t0)=0`, and `rlctAt v = rlctAtOn (p ↦ ∑p.1² + ∑ q(p)²) (0,t0)`
  ⟹ `∃ U ∈ 𝓝 t0, ∑ q(0,z)² ≠ 0` a.e. `z ∈ U`.

* **`hInterface`**: same hyps ⟹ for the built second-peel residual `q₂` (count
  `e = extraCountRect (H0−r)(H2−r) a b`, `a=frontRise`, `b=backRise`) satisfying the second-peel
  chart equation, BOTH (a) `q₂`'s slice a.e.-nonzero, AND (b) `rlctAtOn (t ↦ ∑ q₂(0,t)²) t0₂ =
  ofReal(lambdaCore (MprimeRect (H−r) a b))`.

## Verdict (Codex xhigh corroborated my own analysis)

### `hRne` — TRUE only with an extra hypothesis `rlctAt v > nReg/2`
- **Counterexample to the ∀-`q` statement as written**: `q ≡ 0` is `C²`, vanishes at `(0,t0)`, and
  gives `rlctAtOn (∑s²) (0,t0) = nReg/2`. At a stratum where `rlctAt v = nReg/2` (trivial core) the
  chart equation holds but the slice `∑q(0,z)² ≡ 0`, so the conclusion FAILS. The bare gate is false.
- **With `rlctAt v > nReg/2`** the gate holds, via a NEW lemma (both Codex + I derive it):
  `slice_zero_set_caps_rlct_half` — *if the slice `R(z) = ∑ q(0,z)²` has positive-measure zero-set in
  every nbhd of `t0`, then `rlctAtOn (p ↦ ∑p.1² + ∑q(p)²) (0,t0) ≤ nReg/2`.* Proof: on a
  positive-measure `E` where `q(0,·)=0`, `C¹`-in-`s` gives `|q(s,z)| ≤ L|s|`, so `f ≤ (1+L²)|s|²`
  there, and `∫_{B_s×E} f^{-c} ≥ (1+L²)^{-c} μ(E) ∫_{B_s}|s|^{-2c} = ∞` for `c ≥ nReg/2`. Contrapositive
  gives the a.e.-nonzero. **Difficulty: moderate** (only `C¹`-in-`s` needed).
- **The `rlctAt v > nReg/2` bound is NOT free inside the gate** — deriving it from the first peel is
  circular (the peel bound itself needs `hRne`). It must come from the CONCRETE `q`: b3 gives
  `rank(jacResid (q(0,·)) t0) = extraCountRect > 0` (nondegenerate stratum), and a rank-≥1 `C¹` map
  has a measure-zero zero-set near `t0` (implicit-function / rank theorem) ⟹ slice a.e.-nonzero
  directly, bypassing the value bound. **This route needs the concrete `q`, unavailable to the ∀-`q`
  wire.** (Edge case `extraCountRect = 0`, i.e. `a=b=0`: `v` is the deepest stratum, the inequality
  is the trivial equality — handle separately.)

### `hInterface` — FALSE as the ∀-`q₂` statement
- **Counterexample (Codex)**: `R = x² + u⁴ = x² + (u²)²`; peeling the `x`-square, the built residual
  is `q₂(x,u) = u²`, slice `R₂(u) = u⁴`, `rlctAtOn R₂ = 1/4`. There is no reason `1/4 =
  lambdaCore(M')` (a fixed DLN value). So conclusion (b) fails for arbitrary `C²` `q₂` satisfying the
  second-peel equation. Part (a) also fails at the pure-quadratic threshold (`q₂ ≡ 0`).
- **What it actually needs**: a DLN **model-identification** of the built degraded slice —
  `R₂ = unit · (dlnLoss M' 0) ∘ φ` near `t0₂`, with `unit` bounded away from 0 and `φ` a local `C¹`
  diffeomorphism. Then (b) follows from `r1_resolution_general` (the polynomial DLN core value) +
  bounded-unit/diffeo RLCT invariance, and (a) from transport of the polynomial zero-set nullity.
  **Difficulty: hard-new-analysis** to prove the identification from the current `C²` abstraction;
  the machinery (`r1_resolution_general`) only computes the POLYNOMIAL model core `dlnLoss M' 0`, NOT
  an arbitrary `C²` residual's slice.

## Why the ∀-`q` wire is the wrong interface
`hD1ge_L2_rect_of_gates` (and the producer `d1ge_L2_rect_two_peel_hrank_closed`) demand the gates
∀-`q`/∀-`q₂`. Since the ∀-`q₂` `hInterface` is FALSE and the ∀-`q` `hRne` needs a hypothesis absent
from its statement, **feeding this wire requires proving false/too-weak statements** — it cannot be
done. The gates are true only for the CONCRETE producer residual (where b3's rank fact and the DLN
structure live), so the closing must construct `q`/`q₂` internally and discharge the gates for those,
not route through ∀-`q` hypotheses.

## The precise remaining runway (4 named lemmas, shortest first)
1. **`slice_zero_set_caps_rlct_half`** — pos-measure slice zero-set ⟹ `rlctAtOn ≤ nReg/2` (moderate;
   `C¹`-in-`s`). Standalone, network-free.
2. **`slice_ae_nonzero_of_posrank_jacResid`** — the concrete-`q` route to `hRne`: `rank(jacResid
   (q(0,·)) t0) ≥ 1` ⟹ `{q(0,·)=0}` measure-zero near `t0` ⟹ slice a.e.-nonzero (moderate; rank
   theorem / measure-zero of a positive-rank `C¹` zero-set). Uses b3's banked rank fact — preferable
   to (1)+value-bound since it avoids the circular `rlctAt v > nReg/2`.
3. **`degraded_slice_is_core_up_to_bounded_unit_local_diffeo`** — the built second-peel residual `q₂`
   slice `= unit · (dlnLoss (MprimeRect …) 0) ∘ φ` (hard; the DLN model-identification of the
   second-peel residual). The crux; genuinely new analysis.
4. **`degraded_slice_rlct_eq_lambdaCore`** — (b) from (3) + `r1_resolution_general` + bounded-unit/
   diffeo RLCT invariance; (a) from (3) + polynomial zero-set nullity transport (bounded-bookkeeping
   once (3) lands).

Then a `d1ge_L2_rect_two_peel_closed` that CONSTRUCTS `q`/`q₂` (as `d1ge_L2_rect_two_peel_hrank_closed`
already does) and discharges the gates via (2)+(3)+(4) closes LEAF 2 → sorry-free
`aoyagi_learning_coefficient_L2`. The current ∀-`q` wire (`hD1ge_L2_rect_of_gates`) should be
retired in favour of this concrete-`q` producer.

## Build status
`HeadlineL2Assembly` green, one `sorry` (LEAF 2, line 123) — unchanged from `origin/genm-b3closer`,
comment updated with the finding. Core-geometry (b3 + `hrank₂`) remains DONE and green.
`aoyagi_learning_coefficient_L2` is NOT yet sorry-free (blocked on the 4 lemmas above).

## Artefacts
- `codex/gates-prompt.md`, `codex/gates-answer.md` — the decorrelated verdict.
