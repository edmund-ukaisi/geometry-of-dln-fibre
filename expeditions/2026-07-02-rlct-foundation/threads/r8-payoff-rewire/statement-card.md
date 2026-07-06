# Statement cards — R8 payoff rewire (built `rlctGlobal`, `rlctReal` retired)

The honest capstone of the RLCT foundation: the opaque `rlctReal` scalar axiom is **retired** and the
DLN payoff is restated on a **built, cite-free** global RLCT `RLCT.Global.rlctGlobal` (paper Def 8.1(i)). The
payoff now rides only the two DLN monuments (Watanabe upper, Aoyagi lower); the cite surface drops from
4 to 3 across the foundation.

---

## Card 1 — the global RLCT (definition, Def 8.1(i))

> **Claim.** For a loss germ `K : X → ℝ` on a measure + topological space `X`, the **global** real
> log-canonical threshold is the supremum of the exponents `c ≥ 0` at which `K^(-c)` is globally
> locally integrable (integrable on some neighbourhood of every point).
>
> - **Lean:** `RLCT.Global.rlctGlobal` (def) + `RLCT.Global.globalAdmissibleExponents`
>   (`lean/DLNFibre/Core/Analysis/RLCT/Global.lean` @ `b9087980`). All Global-machinery names live
>   in the nested `RLCT.Global` namespace (the helper names `negPow` / `localAdmissibleExponents` /
>   `rlctAt` there mirror the `Fin n → ℝ` local zeta theory in `RLCT.Basic`/`RLCT.Local` without
>   clashing).
> - **Gloss.** `globalAdmissibleExponents K = {c : ℝ | 0 ≤ c ∧ ∀ x, IntegrableAtFilter (negPow K c)
>   (𝓝 x)}`; `rlctGlobal K = sSup (globalAdmissibleExponents K)`, an `ℝ` value. Polymorphic in `X`
>   (`{X} [MeasureSpace X] [TopologicalSpace X]`), so it names the DLN loss `lossDLN d B : Rep_d → ℝ`.
> - **Proved.** The object is defined; `zero_mem_globalAdmissibleExponents` (`0` admissible when `1`
>   loc-integrable everywhere). Axiom-clean (`#print axioms RLCT.Global.rlctGlobal = [propext,
>   Classical.choice, Quot.sound]`).
> - **Assumed.** none (definition).
> - **Cited.** none — cite-free (the local zeta-pole continuation cite is for the *local* `(λ,m)` pair,
>   off the global-payoff path).
> - **Deferred.** The `sSup` is the honest value only in the pole regime (`{K=0} ≠ ∅`, bounded
>   admissible set); on a nowhere-vanishing germ the honest value is `+∞`, out of the ℝ `sSup`'s scope
>   (junk `0`) — a documented scope, matching `rlctAt`. `name = content`.
> - **Status.** sorry-free

---

## Card 2 — Prop 8.3(iii): `rlctGlobal = inf over the zero locus` (elementary half + conditional)

> **Claim.** `rlctGlobal K ≤ rlctAt K x` at every point `x` (global loc-integrability ⟹ local at
> `x`); folded over the zero locus, `rlctGlobal K ≤ sInf (rlctAt K '' {K = 0})`. The full equality
> `rlctGlobal K = sInf (rlctAt K '' {K = 0})` (Prop 8.3(iii)) holds **modulo a gluing hypothesis**.
>
> - **Lean:** `RLCT.Global.rlctGlobal_le_rlctAt`, `RLCT.Global.rlctGlobal_le_sInf_zeroLocus`,
>   `RLCT.Global.rlctGlobal_eq_sInf_zeroLocus_of_glue` (`.../Global.lean` @ `b9087980`)
> - **Gloss.** `_le_rlctAt`: under `BddAbove (localAdmissibleExponents K x)` + global-set nonempty,
>   `rlctGlobal K ≤ rlctAt K x` (`csSup_le_csSup` on the subset `globalAdmissibleExponents ⊆
>   localAdmissibleExponents K x`). `_le_sInf_zeroLocus`: + `{K=0}` nonempty ⟹ `rlctGlobal K ≤
>   sInf (rlctAt K '' {K=0})` (`le_csInf`). `_eq_..._of_glue`: + `hGlue : sInf (…) ≤ rlctGlobal K` ⟹
>   the equality (`le_antisymm`).
> - **Proved.** The elementary `≤` half, unconditionally (given the pole-regime `BddAbove` + zero-locus
>   nonemptiness). The full equality is proved **from** the explicit `hGlue`.
> - **Assumed.** For `_le_*`: local `BddAbove` at each zero (pole regime) + global-set / zero-locus
>   nonemptiness. For the equality: additionally `hGlue`.
> - **Cited.** none — axiom-clean.
> - **Deferred (named).** `hGlue` — the reverse `≥` direction — is a **paracompactness/gluing lift**
>   (local integrability near each zero + near each regular point, glued to global). The paper itself
>   flags non-attainment "at infinity"; attained for `X` compact or `X, F` algebraic. It is supplied as
>   an explicit hypothesis, **not** a `sorry`. Proving it for the algebraic DLN germ is a separate build
>   (roadmapped). The DLN payoff does **not** use this characterization.
> - **Status.** sorry-free

---

## Card 3 — the retired-`rlctReal` DLN payoff on the built `rlctGlobal`

> **Claim.** For a genuine deep network (`0 < N`) and a rank-`0` (resp. rank-`r`) target, the built
> global RLCT of the DLN square-Frobenius loss equals `C/2 = (cCodim d 0).toNat/2` (resp.
> `(C + r(d_0+d_N−r))/2`) — via `le_antisymm` of the two cited Watanabe/Aoyagi bounds, now stated
> **about `rlctGlobal (lossDLN d B)`**, composed with the PROVED real↔complex codim transfer and the
> geometry `codim mult⁻¹(0) = C`.
>
> - **Lean:** `DLNFibre.DLN.rlct_lossDLN_zero_eq_half_cCodim_aoyagi` (corner-0, cited instance) +
>   the interface-parametrized `rlct_lossDLN_zero_eq_half_cCodim_via_aoyagi`,
>   `rlct_lossDLN_eq_half_cCodim_add_shift` (general-r);
>   the two `@[cited]` bounds `cited_watanabe_upper_ax` / `cited_aoyagi_lower_ax`
>   (`lean/DLNFibre/DLN/RLCT/AoyagiCited.lean`, `.../RlctPayoff.lean`,
>   `.../BundleShiftDischarge.lean` @ `b9087980`)
> - **Gloss.** `RlctRealInterface d` now carries the two bounds `rlctGlobal (lossDLN d B) ≤/≥
>   ½·codim_ℝ` (the opaque `rlct` field is GONE). `aoyagiRlctRealInterface` builds it from the two
>   cited axioms. `rlct_lossDLN_zero_eq_half_cCodim_aoyagi (hN : 0<N) (h : (kostantPartitions d 0)
>   .Nonempty) : rlctGlobal (lossDLN d 0) = ((cCodim d 0 h).toNat : ℝ)/2`.
> - **Proved.** Everything but the two analytic bounds: the built `rlctGlobal`, the connector
>   (`zeroLocus_lossDLN_eq_fibre`), the real↔complex transfer
>   (`codimRealFibre_eq_codimRepCanonical_baseChange`), the catenary, `codim_K = C` (bridge (b)).
>   The two `Tuple ℝ d` measure/topology instances (product Lebesgue + Euclidean, via the
>   `Matrix = Pi` unfolding) let `rlctGlobal` name the loss.
> - **Assumed.** The inhabited-fibre guard `0 < N → B.rank = r → (∀ k', r ≤ d k')` (the scope where the
>   fibre `mult⁻¹(B)` is nonempty, so `rlctGlobal < ∞`; Prop 8.3(i)).
> - **Cited.** `cited_watanabe_upper_ax` (Watanabe universal `rlctGlobal ≤ ½·codim`),
>   `cited_aoyagi_lower_ax` (Aoyagi Thm 1 / LR §8 matching lower bound) — **two** located `@[cited]`
>   axioms about the *built* object. `rlctReal` is **retired** (was a 3rd cite).
> - **Deferred.** none for the payoff. (Deriving the two bounds themselves — Watanabe's universal RLCT
>   bound + Aoyagi's exact DLN computation — is the genuine analytic monument, cited by design.)
> - **Status.** sorry-free
>
> **`#print axioms` footprint (the target).** `rlct_lossDLN_zero_eq_half_cCodim_aoyagi` depends on
> `[propext, Classical.choice, Quot.sound, cited_aoyagi_lower_ax, cited_watanabe_upper_ax]` — std-3 +
> the **two DLN cites**, NO `rlctReal`, NO continuation cite. Cordon: `UNACCOUNTED = ∅`,
> `CITED = {Watanabe, Aoyagi}`. Foundation-wide: `scripts/sorries = 0 sorry, 3 axiom`
> (`cited_local_zeta_pole` + the two DLN bounds); the cite surface dropped 4 → 3.

---

## Reviewer note (fidelity focus)

The load-bearing fidelity questions for a decorrelated reviewer:

1. **Does `rlctGlobal` faithfully render Def 8.1(i)?** The Lean is `sSup {c ≥ 0 | ∀ x,
   IntegrableAtFilter (K^(-c)) (𝓝 x)}` vs the paper's `sup {s | |F|^{-s} locally integrable}`. Note:
   (a) the ℝ-`negPow` (`Real.rpow` of the *signed* germ value) matches the DLN loss `K ≥ 0`, so
   `K^{-c}` is the honest `|F|^{-s}` there; (b) restricting to `0 ≤ c` (vs the paper's `s ∈ ℝ`) is
   harmless and keeps the `sSup` honest — matches the local `rlctAt` convention; (c) the junk-`0` at a
   regular point (unbounded admissible set) is why the characterization is `inf over {K=0}`, NOT `⨅
   over all X` (the paper's inf is over all `X` only because regular points give `+∞`, which the
   ℝ-valued proxy cannot represent).
2. **Is the payoff naming honest?** The payoff names the *built* `rlctGlobal`, not an opaque map; the
   two bounds are cited about the built object. Confirm the two `@[cited]` sources are the right
   theorems (Watanabe's universal bound; Aoyagi Thm 1 / LR §8) and that the inhabited-fibre guard is
   the correct scope (off `image(mult)` the fibre is empty, `codim = (⊤).toNat = 0`, and an unguarded
   upper bound would force the false `rlctGlobal ≤ 0`).
3. **Is `hGlue` a genuine hypothesis, not a hidden `sorry`?** Card 2's equality is `le_antisymm` of the
   proved `≤` and the *supplied* `hGlue`; the reverse direction is not asserted — it is the named
   paracompactness lift, roadmapped.

**`local-codex-consult` verdict (ran clean, `codex/rlctglobal-faithfulness-{prompt,answer}.md`).**
Codex (xhigh) judged all four fidelity questions **harmless-caveat or faithful — no genuine gap** for
the `F = K ≥ 0` DLN use-case with a nonempty zero locus and Lebesgue-type measure:
(1) restricting to `0 ≤ c` is faithful (negative exponents lie below `0`, never raise the sup once `0`
is admissible); (2) `Real.rpow` of the signed value = `|F|^{-s}` away from `{K=0}`, and the
`Real.rpow 0 (neg) = 0` convention is harmless on the null zero-locus of a nonzero analytic loss (would
be a gap only for signed `F` / atomic measures / positive-measure zero sets); (3) the
`inf`-over-`{K=0}` is the correct honest reading of Prop 8.3(iii) given the junk-`0` (regular points
would contribute `+∞`); (4) "`∀ x`, loc-integrable at `x`" matches Def 8.1(i)'s "locally integrable" —
noncompactness affects only *attainment* (the `hGlue` roadmap), not the meaning. Overall: `rlctGlobal`
is a faithful rendering for the DLN payoff, provided the junk-`0` cases stay explicitly out of scope —
which the module docstring does.
