# Thread 09 — Phase D + R design (pen-and-paper, Codex-convergent)

The RLCT-payoff destination at **r=0 is ~1 module (~200–410 LoC)**: loss + `codim(fibre 0)=C` + a Cited
`RlctInterface` + the transport `rlct(K^DLN_0)=C/2`. General-`r` adds only the bundle shift (Lemma 4.6) —
avoidable by scoping r=0 first.

## Phase D — loss + codim identity (`DLNFibre.DLN`, field = ℝ; rlct is a real-analytic invariant)
- **D2 loss** `lossDLN d B A := ((mult d A - B)ᵀ * (mult d A - B)).trace = ‖mult A − B‖²_F` (no prefactor;
  rlct is scale-invariant). `lossDLN_nonneg`; the load-bearing **`zeroLocus_lossDLN_eq_fibre :
  {A | lossDLN d B A = 0} = fibre d B`**. Hardest: `Tr(MᵀM)=0 ↔ M=0` over ℝ (Frobenius API). ~80–150 LoC.
- **D3 (r=0, load-bearing)** `fibre_zero_eq_productRankLocusLE_zero : fibre d 0 = productRankLocusLE d 0`
  (over a field `rank M = 0 ↔ M = 0`; rfl-close) ⟹ **`codimRepCanonical (fibre d 0) = (cCodim d 0 h).toNat = C`**
  (consume LANDED `codimRepCanonical_orbitRankLocus_eq_height` + `cCodim_eq_inf_geomCodim`). ~60–120 LoC, zero-cited.
- **D3 (general r)** `codim(fibre B) = C + r(d_0+d_N−r)` (Lemma 4.6 bundle) — PROVE (fibre-dim drop, ~150–350) OR
  CITE Lemma 4.6 with the shift NAMED in the statement. Do NOT name a general-r theorem if only r=0 is proved.
  `C` computed over ℂ, base-changed to ℝ (`Core.BaseChange`; `C` field-unambiguous per `rmk:real_points`).

## Phase R — the RLCT payoff (Cited interface; NAME = CONTENT — the precision-critical part)
Three analytic layers, do not conflate: (i) the rlct *definition* — interfaced (absent from Mathlib;
multi-month sub-library); (ii) the general `rlct ≤ codim/2` — Atiyah, Cited; (iii) **the DLN equality
`rlct(K^DLN_B) = codim(fibre)/2` — Cited, purchased by Aoyagi Thm 1 / LR thm:aoyagi-rlct**. The codim→rlct
equality is Aoyagi's ANALYTIC theorem, NOT a geometric consequence of `C`.

- **R1 interface (Design A — recommended, Codex-convergent):**
  ```
  structure RlctInterface (d) where
    rlct : (Tuple ℝ d → ℝ) → ℝ                              -- opaque (no Mathlib rlct)
    cited_aoyagi_dln : ∀ B r, B.rank = r → r ≤ … →          -- CITED = Aoyagi Thm 1 / LR 8.6
      rlct (lossDLN d B) = (codimRepCanonical (fibre ℝ d B) : ℝ) / 2
  ```
  Guards (each kills an overclaim): axiom NAMED `cited_aoyagi_dln` (announces citation + scope), STOPS at
  `codim(fibre)/2` (so R2 is non-trivial transport, not a restatement), carries ONLY the equality (reject
  Design B — opaque rlct + general `≤` + Aoyagi `≥` by antisymmetry — its decisive `≥` is still external).
- **R2 payoff** `rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi (I : RlctInterface d) (h) :
  I.rlct (lossDLN d 0) = (cCodim d 0 h : ℝ)/2` := `rw [I.cited_aoyagi_dln …, codim_zeroLocus_lossDLN_zero_eq_cCodim]`.
  **Name = content:** `I : RlctInterface` explicit in the type (Cited dependency visible) + `via_aoyagi` in the
  name. A bare `rlct_…_eq_half_codim` with no interface in scope is FORBIDDEN (the CLAUDE.md `rlct_…` trap).
  General-r companion carries the shift. R1 ~30–60, R2 ~30–80 LoC.
- **`θ` is NOT in Phase R** (paper line 1934: no simple relation rlcm↔θ). R is `C/2` only.

## Cited-vs-proved split
- **Proved here (zero-cited):** loss zero-set = fibre; `codim(fibre 0) = C`; the transport into `C/2`;
  (general r) `codim(fibre) = C + r(d_0+d_N−r)` if attempted.
- **Cited (Aoyagi/LR 8.6):** the rlct definition + `rlct(K^DLN_B) = codim(fibre)/2`.
- **Not claimed:** the general `≤` bound as a Lean fact (unneeded under Design A); any θ↔rlct/rlcm relation.

## (2,2,2) r=0 (exact, 3 routes): C=3, codim(fibre 0)=3, rlct=3/2. Matches `cCodim_d222_zero=3`, paper Ex 4.3.
General-r stress (shift faithful): (2,2,2) r=1 → codim Σ̄^1=1 (=`cCodim_d222_one`), shift 3, fibre codim 4, rlct=2.

Codex artefacts: `threads/09-DR-design/codex/cited-boundary-{prompt,answer}.md`.
