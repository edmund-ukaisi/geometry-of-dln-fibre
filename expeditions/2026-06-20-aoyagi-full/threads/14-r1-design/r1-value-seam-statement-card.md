# R1 value-seam statement card — the A1-free chart↔value seam + the `core_rlct_eq_lambdaCore` assembly spine

- **Seat:** `fm` (R1 cover lane, `fm/r1-cover`). The G3.5 chart↔value seam (task #115) isolated as
  pure arithmetic + the conditional assembly spine for the core-RLCT headline.
- **Module:** `lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Value.lean` (built on branch `fm/r1-cover`;
  base @ `e6827ba`, SHA bumped at integration). Standalone (imports only `Skeleton`); **not yet wired
  into `DLNFibre.lean`** — controller wires (single-writer aggregator).
- **Status.** sorry-free + reviewed (fidelity check 2026-06-22: all 5 points PASS, decorrelated Codex
  confirmed SOUND-BANKING — no vacuity, no circularity). Axiom-clean (assembly spine + `⨅`-collapse +
  definitional bridge depend on no S2; the per-chart value lemmas cite only `monomial_rlct`, the one
  permitted axiom).

---

## The seam (the genuinely-closed arithmetic)

> **Claim (chart↔value seam, G3.5).** A resolution chart whose monomial data `(d,k,h)` is the
> stratum-divisor data over the admissible cone (every axis obeys the multiplicity bound
> `m₀·kⱼ ≤ hⱼ+1`, and one binding axis is the regular-sequence divisor `(kⱼ,hⱼ)=(1, m₀−1)`) has
> `monomialThreshold = m₀/2`; over a finite family with every chart `≥ m₀/2` and one chart `= m₀/2`,
> the `⨅` is `m₀/2`; and when `m₀ = min_{Adm} Mval`, that is `ofReal(lambdaCore M)` — definitionally,
> with no A1 closed form.

- **Lean:**
  - `monomialThreshold_ge_of_mult'` — per-chart lower bound `m/2 ≤ monomialThreshold d k h` from
    `∀ j, m·(k j) ≤ h j + 1`, **spectators (`k j = 0`) allowed** (the gated
    `monomialThreshold_ge_of_mult` needs `k j ≥ 1` everywhere; this drops that).
  - `monomialThreshold_eq_half_of_binding` — per-chart `monomialThreshold d k h = m/2` from the
    multiplicity lower + one binding axis `(k j₀,h j₀)=(1,m−1)`.
  - `iInf_monomialThreshold_eq_half` — `⨅ i, monomialThreshold (d i)(k i)(h i) = m/2` from
    every-chart-`≥` + one-chart-`=`.
  - `half_codim_eq_ofReal_lambdaCore` — `(m₀ : ℝ≥0∞)/2 = ofReal(lambdaCore M)` when
    `(Adm M).inf' Mval = (m₀ : ℤ)` (pure cast/`ofReal` arithmetic).
  - `core_rlct_eq_lambdaCore_of_resolution` — the **assembly spine** (below).
- **Gloss.** The RLCT-value `½·codim` arithmetic: a binding regular-sequence divisor over the
  minimal-codimension stratum realises `½·m₀`; multiplicity-control + the cover keep every other
  divisor `≥ ½·m₀`; and `½·m₀` is `lambdaCore M` by unfolding `lambdaCore := ½·inf' Mval`.
- **Proved.** All five lemmas above, unconditionally (the `(2,2,2)` `case222_unit_leaf_threshold` and
  `case222_block_leaf_threshold` are the `m₀=3` instances — checked: both reproduced by
  `monomialThreshold_eq_half_of_binding`).
- **Cited.** `monomial_rlct` (S2, Aoyagi/Watanabe — the one permitted axiom) for the threshold-VALUE
  `monomialThreshold = ⨅ axisRatio`. Enters ONLY the per-chart value lemmas; the `⨅`-collapse and the
  `lambdaCore` bridge are S2-free.
- **Deferred.** Nothing within the seam. (The seam is A1-FREE — it does NOT use `lambdaCore_eq_clean`
  or the clean closed form; per g34-g35, A1 is an independent confirmation of the same number.)

---

## The assembly spine (conditional on the open cover)

> **Claim (core-RLCT headline, conditional).** Given the resolution chart family with
> `rlctAtOn(dlnLoss M 0) 0 = ⨅ monomialThreshold` and the g35 bracket (every chart `≥ m₀/2`, one
> binding chart `= m₀/2`, `inf' Mval = m₀`), the core RLCT is `ofReal(lambdaCore M)`.

- **Lean:** `core_rlct_eq_lambdaCore_of_resolution`.
- **Gloss.** Once the cover delivers `resolution_charts`'s conclusion plus the divisor bracket, the
  value seam closes the headline `rlctAtOn(core M) 0 = ofReal(lambdaCore M)`.
- **Proved.** The assembly (the three rewrites: cover identity → `⨅`-collapse → `lambdaCore` bridge),
  sorry-free and S2-free.
- **Assumed (the open cover obligations, supplied as hypotheses):**
  - `hres` — `rlctAtOn(dlnLoss M 0) 0 = ⨅ monomialThreshold` = the conclusion of `resolution_charts`
    (Skeleton:1017, currently `sorry`). The geometric (C2) cover: per-node blow-up (`pivotBlowupOn`)
    + det-1 Schur straighten (consuming `schur_straighten_exists`) + cover-exhaustiveness (R1.6).
  - `hge` / `heq` — the g35 bracket (R1.2b over all stratum divisors + the cover = lower; R1.2a at the
    minimal-codim achiever = upper).
  - `hm₀` — `inf' Mval = m₀` (the achiever's codimension is the `Adm`-min, g35).
- **Deferred (NOT done — named, on the critical path):**
  - **`resolution_charts` proof** (the cover/exhaustiveness, "the OPEN HARD DESIGN mountain"): the
    R1.1 pivot-atlas recursion + R1.6 exhaustiveness over the nested-rank stratification. Blocked on
    `schur_straighten_exists` (the (A) det-1 straighten, parallel `crux` lane, still `sorry`).
  - **the g35 bracket as theorems** (`hge`/`heq`/`hm₀` discharged from the cover, not assumed): needs
    the cover's chart family wired to `Adm`/`Mval` (R1.3 codim = Mval count, R1.2 per-divisor bracket
    over the atlas).
  - **`Nonempty ι`** (reviewer note, 2026-06-22): the spine requires `[Nonempty ι]`, but
    `resolution_charts` (Skeleton:1017) currently provides only `Fintype ι` — it does NOT assert the
    family is nonempty. True on content (there is always the achiever chart), but the cover lane must
    additionally discharge `Nonempty ι` at wiring. So the full cover deliverable is
    `hres + Nonempty ι + hge + heq + hm₀`, not `hres` alone.

---

## What this de-risks / pins

The seam proves the **value side is A1-free and closed**: the only thing between the geometric cover
and the headline `core_rlct_eq_lambdaCore` is the three hypotheses of `core_rlct_eq_lambdaCore_of_resolution`,
all of which are cover obligations (not arithmetic). The arithmetic mountain is gone; the residual is
purely the geometric cover (R1.1 + R1.6) + the crux straighten. The spine is the exact interface the
controller wires the eventual `resolution_charts` proof into.
