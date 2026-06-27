# Thread 01 — R0 interface design (scout: pen-and-paper + literature)

**Target:** pin the exact form of the three CITED analytic theorems (rlct-of-a-quadratic = c/2; Watanabe `rlct ≤ ½·codim` for a sum-of-squares; the resolution criterion "all exceptional divisors ≥ ½·codim ⟹ rlct ≥ ½·codim") AND the **precise geometric hypothesis** the lower-bound criterion consumes — so the DLN geometry can prove it. Output: the interface spec (a certificate; no Lean).

## Sources read

- LR paper §8 (`sec:RLCT`, main.tex L1782–1937): Def 1 (rlct), the zeta/Atiyah meromorphy, `prop:rlct_elem` (upper bound, Thom–Sebastiani additivity, `inf_x`), Example `ex:rclts` (`rlct(Σxᵢ²)=e/2`), **Thm 8.6 `thm:aoyagi-rlct`** + proof.
- Aoyagi 2023 PDF (`theory/aoyagi-2023-reproduction/aoyagi-2023-extracted-text.txt`): Def 1, Lemma 1, the **Hironaka extraction** (p.6), Thm 1/2, Thm 3 (block reduction), Thm 4 (deepest point), the recursive blow-up (Cases 1/2), terminal normal-crossing.
- Lean scaffold: `RlctPayoff.lean` (monolithic `RlctInterface.cited_aoyagi_dln`), `Skeleton.lean` (`monomial_rlct` axiom + D1→L2→R1→S2→A1 route + `aoyagi_learning_coefficient`), `Foundations/Rlct.lean` (`rlctAt`, `weightedThreshold`, the PROVED `axisRatio_ge_of_mult`).
- Prior `2026-06-20-aoyagi-full` design-spec §4–§8 (`Mval`/`Adm`/`aoyagiLambda`, S2 §7.1, D1 §7.2).
- Decorrelated Codex (xhigh, gpt-5.5, own web research: Mustață lct survey, Ein–Mustață inversion of adjunction arXiv:math/0209392, Saito–Varchenko Newton arXiv:math/0601336, lct-of-ideals arXiv:1107.2676): `codex/lower-bound-criterion-answer.md`.
- Cross-thread (Mathlib-coverage scout, via coordinator): the **real↔complex seam** — rlct is over ℝ, all banked DLN geometry is over `K` alg-closed; rated the real wall, above the lci gap.

---

# CERTIFICATE — R0 interface design

## 0. The decisive structural findings (reframe the seam)

Two findings change the seam from the brief's first sketch:

**(A) The lower bound is a condition on the IDEAL, not the set; "lci + smooth strata" is FALSE.**
There are two routes to `rlct = ½·codim`: the brief's "generic resolution criterion + DLN mildness," vs. Aoyagi's *bespoke explicit resolution*. The geometric hypothesis the lower bound consumes is the **log-canonical pair / divisorial-valuation inequality** `A_X(E) ≥ c·ord_E(I)`, a property of the defining ideal — NOT a stratification-smoothness datum on the zero-set. Codex (decorrelated) kills the brief's candidate (b) with an explicit lci-codim-2-quadratic counterexample (§2).

**(B) The interface MUST be framed over ℝ; the real↔complex transfer is its own first-class step (currently HIDDEN in the monolith).** The analytic rlct is irreducibly over ℝ (`F : ℝ^N → ℝ`, real integral/zeta, real zero-set `V_ℝ`). All banked DLN geometry (`cCodim`, `codimRepCanonical`, smoothness, conormal) is over `K` alg-closed (`[IsAlgClosed k]`). The current monolith `cited_aoyagi_dln` bridges the real-loss rlct directly to `codim_K(mult⁻¹(B.map ι))` and its docstring *explicitly buries* the transfer ("the real↔complex passage … is part of what Aoyagi Cites. No from-scratch base-change lemma is needed", `RlctPayoff.lean` L270–272). The refined interface's job is the opposite: **expose** real↔complex as a named step and decide CITED vs PROVED for it (§4). This is the genuine wall (§5, RISK-1).

---

## 1. The three cited analytic theorems (exact statements, framed over ℝ)

`X` a real-analytic manifold (`Params = ℝ^N`), `dvol` Lebesgue, `F : ℝ^N → ℝ` real-analytic `≥ 0`. `rlct_x(F) = sup{ s>0 : |F|^{−s} loc. integrable near x }`, `rlct(F) = inf_x rlct_x(F)`. For `F = Σⱼ fⱼ²` (`fⱼ : ℝ^N → ℝ` real-analytic), **`V_ℝ = F⁻¹(0) = {f₁=…=f_c=0} ⊆ ℝ^N`** is the REAL zero-set; `codim_ℝ V_ℝ` is the real codimension. Every "codim" in C1–C3 below is the **real** one.

### C1 — rlct of a non-degenerate quadratic = c/2 (the local model)

> For `F(x) = x₁²+…+x_c²` on `ℝ^n` (`c ≤ n`): `rlct(F) = rlct₀(F) = c/2`. (`V_ℝ` is the smooth real linear subspace of real codim `c`.)

Source: LR Example `ex:rclts`; Aoyagi p.6 (`∫₀^ε u^{−2c}du < ∞ ⟺ c<1/2`). **In Lean already:** `axisRatio_regularSeq` + `monomial_rlct` at `(kⱼ,hⱼ)=(1,0)`; additive form `rlct_additive_smooth_block` (`λ(Σxᵢ²+G²) = n/2 + λ(G²)`). Purely real — no transfer issue. Citable to Watanabe / standard SLT.

### C2 — Watanabe universal upper bound `rlct ≤ ½·codim_ℝ V_ℝ`

> If `F = Σⱼ fⱼ²` (real-analytic, finite) and `V_ℝ ≠ ∅`, then `rlct_x(F) ∈ (0, codim_{ℝ,x} V_ℝ /2] ∩ ℚ` locally; globally `rlct(F) ∈ (0, codim_ℝ V_ℝ /2] ∩ ℚ` when `inf_x rlct_x` is attained (guaranteed for `X,F` algebraic — DLN loss is polynomial ⇒ attained).

Source: LR `prop:rlct_elem`(i)+(iii), `eqn:rlct_upper_bound{,_glob}` (cited Lin `lin:phd_thesis` + `spl:real-jets`); Watanabe SLT. The easy half; LR L1882–1885 applies it directly. **Codim is the REAL codim of the REAL zero-set** — to reach our `cCodim` (complex) needs the transfer T (§4). State C2 with the algebraicity/compactness hypothesis, not bare.

### C3 — the resolution lower-bound criterion (the one needing care)

The faithful statement is the **per-divisor multiplicity inequality on a real-analytic log-principalization of the IDEAL** (Codex-confirmed; real analogue of Mustață's lct-of-ideals formula):

> Let `I = (f₁,…,f_c)` real-analytic, `V_ℝ = V(I)` of pure real codim `c`. Let `π : Y → ℝ^N` be a **real-analytic log-principalization of `I`**: `I·𝒪_Y = 𝒪_Y(−Σⱼ kⱼEⱼ)` (total transform monomial, s.n.c.), `Jac_π ∼ ∏ⱼ yⱼ^{hⱼ}`. Since `F = Σfᵢ²`, `F∘π = u·∏ⱼ yⱼ^{2kⱼ}` (`u>0` analytic unit). Then
> `rlct_x(F) = min{ (hⱼ+1)/(2kⱼ) : Eⱼ over x, kⱼ>0 }`.
> **Criterion:** if EVERY divisor `Eⱼ` with `kⱼ>0` (exceptional or strict-transform) over the region satisfies `hⱼ+1 ≥ c·kⱼ`, then `rlct(F) ≥ c/2`. With C2: equality.

Source: Hironaka extraction (Aoyagi p.6 — **already the `monomial_rlct` S2 axiom** at the chart level). The chart-level VALUE `monomialThreshold = ⨅ axisRatio` is the Lean axiom; the lower-bracket `axisRatio_ge_of_mult` (`m·k ≤ h+1 ⟹ m/2 ≤ axisRatio`) and `monomialThreshold_ge_of_mult` are **PROVED** in `Skeleton.lean`. So C3 at chart level is in hand; the missing piece is the resolution datum `(π, kⱼ, hⱼ)` (= R3, §2). All real-analytic — no transfer issue *inside* C3 (the transfer is in matching `c` to `cCodim`, §4).

**Naming honesty for C3.** "All NORMAL-CROSSING divisors of a resolution of `V`…" is subtly wrong twice: (i) it is a log-principalization of the *ideal* `I`, not a resolution of the *set*; (ii) the bound is per-divisor on `(kⱼ,hⱼ)`, and the DEEP-stratum divisors are where it fails. Both caveats are load-bearing (§2 kill).

---

## 2. THE CRUX — the precise geometric hypothesis (the R3 target), over ℝ

**Sharp condition (Codex + Ein–Mustață):**

> `(ℝ^N, c·I_{V_ℝ})` is **log canonical** ⟺ the divisorial-valuation inequality `A_X(E) = h_E+1 ≥ c·ord_E(I_{V_ℝ})` for EVERY divisorial valuation `E`. For `F = Σfᵢ²` this gives `rlct(F) ≥ c/2`; with a real smooth reduced codim-`c` point (C2) it is equality. Equivalently `lct(I_{V_ℝ}) = c = codim_ℝ`.

For reduced lci, *inversion of adjunction* (arXiv:math/0209392) translates the ambient-pair condition into log-canonical (reducible/non-normal ⇒ **semi-log-canonical**, slc) singularities of `V` itself.

**What R3 must prove for the DLN fibre — three routes, decreasing strength / increasing citability:**

- **(R3-resolution — what Aoyagi does, what the scaffold builds):** exhibit Aoyagi's recursive real blow-up `π` as a log-principalization of `I_{mult⁻¹(B)}` (the reduced-core ideal `⟨∏Cˢ⟩`), produce the per-chart `(kⱼ,hⱼ)` table, check `hⱼ+1 ≥ c·kⱼ`. In Lean = `resolution_charts` (R1) + `monomialThreshold_ge_of_mult`; the per-divisor inequality reduces (via `Mval = codimForm`, banked `MvalMultSum.lean`) to combinatorial `min_T Mval ≥ cCodim`, which the LANDED `cCodim`-monotonicity supports. **The route the prior expedition built (the big in-progress mountain).**
- **(R3-Newton — candidate clean route):** show the DLN core is **Newton-non-degenerate** (Saito–Varchenko, arXiv:math/0601336) with Newton-polyhedron rlct `= c/2`. Coordinate-dependent, not necessary, but ONE citable theorem discharges all per-divisor inequalities. **Untested for DLN — R1's decisive computation should probe this; if it holds, the mountain collapses.**
- **(R3-lci+slc — structural route):** prove `mult⁻¹(B)` reduced lci of pure codim `c` with **slc** singularities, cite inversion of adjunction → `lct(I_V)=c`. Heavy slc-classification; the reducible fibre (`θ>1`) forces *semi*-lc.

**KILL-CONDITION for the crux (stated before confirming):** the hypothesis is NOT "the singular strata of `mult⁻¹(B)` are themselves smooth of expected codim" (brief candidate (b)). Codex counterexample:

> Reduced lci codim 2, quadratic leading term: `I=(x, y²−z³)`, `F = x²+(y²−z³)²`. Integrate in `x`: `rlct = ½ + rlct((y²−z³)²) = ½ + 5/12 = 11/12 < 1 = c/2`.

An lci with smooth strata + right multiplicity can have `rlct < c/2`: a deep cusp valuation drops the ratio. What rescues `= c/2` is the *absence* of bad divisorial valuations (the lc-pair condition) — which DLN satisfies *because* Aoyagi's explicit resolution exhibits only divisors meeting `hⱼ+1 ≥ c·kⱼ` (the `Mval ≥ cCodim` combinatorics), not because of any set-smoothness.

Further kills: a condition on `V` alone cannot suffice (`x²` vs `x⁴`: same set, different rlct). The hypothesis is on the ideal `I_{V_ℝ}`; DLN fixes it (entry-generators of `mult A − B`) — but the interface must carry the **ideal/loss**, not the bare set. (The scaffold is faithful: works with `dlnLoss`/`⟨∏Cˢ⟩`.)

---

## 3. What Aoyagi's proof actually uses (literature map)

| Layer | Aoyagi object | What it is | Aoyagi: cited or proved |
|---|---|---|---|
| A0 | Def 1 + Hironaka extraction (p.6) | monomial formula `λ = min (hⱼ+1)/(2kⱼ)`, `θ = max chart-count` | **cited** (Hironaka exists; Atiyah meromorphy). = our `monomial_rlct` S2 axiom |
| A0 | Lemma 1 (p.5) | `λ(J) = λ(Σgᵢ²)` (ideal-only) | cited [30–32] |
| L1/L2 | Lemma 2, Thm 3 (p.10–13) | Schur reduction `∏A → diag(reg,∏Cˢ)`; `λ = [−r²+r(H¹+Hᴸ⁺¹)]/2 + λ⟨∏Cˢ⟩` | proved (matrix algebra + Lemma 1) |
| D1 | Thm 4 (p.14) | reduce to deepest point (`r⁽ˢ⁾=r`) | cited [22] (homogeneity) |
| **R1** | **Cases 1/2 blow-up (p.14–22)** | **explicitly CONSTRUCTS the real resolution `π` + normal-crossing divisors of `‖∏Cˢ‖²`** | **proved BY HAND** — bespoke blow-up induction (the wall) |
| A5 | terminal form + Lemma 3 (p.22–25) | reads off `(kⱼ,hⱼ)`, minimises arithmetically → `λ` | proved (finite quadratic) |

**Aoyagi's lower bound is NOT a structural-criterion invocation — it is a bespoke explicit real resolution.** The abstract says so: *"we determine the resolution map and normal crossing divisors."* He cites only the monomial extraction (A0) once the resolution is built. This is exactly the brief's intended division (cite A0/S2; prove the resolution) and the existing `Skeleton.lean` route is faithful.

**LR Thm 8.6 adds no analytic content** — pure formula-match `2·λ_Aoyagi = C` (the `Mval ↔ codimForm` identity). LR's novelty is the geometric *interpretation* of `λ` as `½·codim`.

---

## 4. The recommended seam (interface decision), with real↔complex EXPOSED

Refine the monolithic `cited_aoyagi_dln` into a thin **CITED** layer + **PROVED** DLN geometry + an **explicit real↔complex transfer step T**.

**CITED (thin, general, honest) — `RlctInterface` fields, all over ℝ:**
1. **C1** rlct-of-a-quadratic `= c/2` — *already* `monomial_rlct`@`(1,0)` + `rlct_additive_smooth_block`. Keep as base case.
2. **C2** Watanabe universal `rlct ≤ ½·codim_ℝ V_ℝ` for a sum-of-squares — a *new* thin field (currently folded in). Citable Watanabe/Lin.
3. **C3-chart** monomial extraction `rlctAt F w* = ⨅ charts (hⱼ+1)/(2kⱼ)` given a normal-crossing chart datum — *already* the `monomial_rlct` S2 axiom (the bare monomial-integral fact). The irreducible cited boundary.

**TRANSFER T (the named real↔complex step — decide CITED vs PROVED):**
- **What it must say:** `codim_ℝ (mult⁻¹_ℝ(B)) = codim_K (mult⁻¹_K(B.map ι))` (real codim of the real fibre = complex codim of the base-changed fibre), AND `V_ℝ` has a real smooth point of the expected codim (so C2 is non-vacuous over ℝ — the real points are not all in the deep strata).
- **Is it cited or provable?** It is **provable**, and should be PROVED, not buried:
  - *Codim equality:* the multiplication fibre is a determinantal-type locus cut by the *same* polynomial equations over ℝ and over `K` (entries of `mult A − B`). For these loci the real points are Zariski-dense in the relevant top-dimensional components (the realizer points `realizerD` are real, and the orbit construction is defined over ℚ ⊆ ℝ), so `dim_ℝ V_ℝ = dim_K V_K` and the codims agree. This is a real-algebraic-geometry transfer (Zariski-density of real points / real dimension = complex dimension for a variety defined over ℝ with a smooth real point). **Provable from the existing realizer being real** — flag as a *new* lemma (R-transfer), not a citation.
  - *Real smooth point:* the `deepestPoint` / realizer construction in `Skeleton.lean` produces a REAL parameter; the smooth locus of the top component contains real points (the regular-rank stratum is real-defined). So the C2 upper bound is realised over ℝ. **Provable.**
- **Why this matters:** the monolith's "no base-change lemma needed" is the visible-progress trap — it hides the one transfer that genuinely connects the real analytic theorem to the complex geometry. Exposing T is the bedrock move.

**PROVED (the prize, DLN-specific):**
- loss `= Σ` of `c` defining squares — banked (`zeroLocus_lossDLN_eq_fibre`).
- the **real resolution datum** for `mult⁻¹_ℝ(B)`: a real-analytic log-principalization with `(kⱼ,hⱼ)` satisfying `hⱼ+1 ≥ c·kⱼ` → C3-chart + LANDED `monomialThreshold_ge_of_mult` → `rlct ≥ ½·codim_ℝ`. = R1/R3 (`resolution_charts` + `Mval=codimForm` + `min Mval = cCodim`).
- compose C2 (upper, over ℝ) + R3 (lower, over ℝ) + T (codim_ℝ = codim_K) → `rlct(K^DLN_B) = ½·codim_K mult⁻¹_K(B.map ι)` = the refined `cited_aoyagi_dln`, now resting on a thin named boundary.

**Why NOT a standalone "C3-structural: lc-pair ⟹ rlct≥½codim" cited field:** cleaner interface, but discharging its hypothesis for DLN still needs the explicit resolution (R3-resolution) or unproven Newton/slc. The honest thin boundary is the chart-level monomial fact (C3-chart) with the resolution PROVED. Add a fourth cited lc-pair field only if R3-Newton/R3-slc discharges cheaply (R1 decides).

---

## 5. Kill-conditions / risks (for the controller)

- **RISK-1 (THE wall, real↔complex — coordinator's flag, confirmed):** the analytic rlct is over ℝ; all banked geometry is over `K` alg-closed. The seam MUST be framed over ℝ with T (codim_ℝ = codim_K + real smooth point) as an explicit PROVED step. I judge T *provable* (the realizer/deepestPoint are real, the fibre is defined over ℚ ⊆ ℝ with real points Zariski-dense in the top components), but it is genuinely *new* Lean work and is the highest-risk single brick — above the lci gap. **It must not be re-buried in the citation.** If real points happen to be sparse in some top component (a component with no real points), `codim_ℝ` could exceed `codim_K` there and the upper bound would be loose — to rule out, prove every minimising orbit closure has a real smooth point (the realizer does, being real-defined).
- **RISK-2 (the lower bound needs the full bespoke resolution):** Codex confirms NO purely structural shortcut from "lci + codim." "Prove all DLN geometry" = finish the `resolution_charts` mountain (R1, the prior expedition's large scaffold, ~45 sorries under `Validate/`). The thin interface relocates the citation to the chart-level monomial fact; it does NOT shrink the resolution work. **If R3-Newton (nondegeneracy) discharges for DLN, this collapses — the high-value gamble R1 should test first.**
- **KILL for brief candidate (b):** "singular strata smooth of expected codim ⟹ rlct = ½codim" is FALSE (Codex `I=(x,y²−z³)`, `F=x²+(y²−z³)²`, rlct `11/12 < 1`). Do not state R3 as a set-stratification smoothness condition.
- **KILL for "condition on V alone":** same zero-set, different ideal powers ⇒ different rlct. Carry the ideal/loss, not the bare set. (Scaffold faithful.)
- **NAME-HONESTY gate:** no `rlct_…` result may assert `≥ ½·codim` while secretly assuming C3-chart for a resolution it does not exhibit, NOR burying T in a citation. Cited boundary = C1+C2+C3-chart; resolution `(kⱼ,hⱼ)` table + T = PROVED. A `rlct_ge_half_codim` lemma carries the resolution-datum + real-point hypotheses explicitly until R1/R3/T discharge them.
- **C2 scope:** the global bound needs `inf_x rlct_x` attained — guaranteed for `X,F` algebraic (LR `prop:rlct_elem`(iii)); DLN loss polynomial ⇒ OK. State with the algebraicity hypothesis.
- **θ (rlcm) out of scope but adjacent:** the order/multiplicity is the harder analytic seam (meromorphic continuation Mathlib lacks); carried `rlctOrderAt` opaque + asserted `= chart-count` inside S2. Not part of `rlct=½codim`; don't over-claim it.

---

## 6. Status

`survived` (established-tier; verified against LR §8 + Aoyagi PDF + decorrelated Codex; reframed over ℝ per the cross-thread constraint). **Seam decision:** thin cited boundary = chart-level monomial extraction (C3-chart) + quadratic base (C1) + Watanabe upper bound (C2), ALL over ℝ; PROVED = the DLN real resolution datum (R1/R3) feeding the LANDED lower-bracket, + an EXPLICIT real↔complex transfer T (codim_ℝ = codim_K + real smooth point). The brief's "generic resolution criterion + mildness hypothesis" is refined to the log-canonical-pair / per-divisor inequality (a condition on the ideal), dischargeable for DLN only via the explicit (Aoyagi) resolution unless Newton-nondegeneracy is shown. The real↔complex transfer T, not the lci gap, is the genuine wall.
