# hproducer — coupled producer decomposition + (b)-route re-adjudication

Re-spec after the formaliser + Codex refined the (b)-proof premise. **Two findings:** (1) the (b)
comparability is a POINTWISE fixed-invertible-map statement, NOT the unbanked germ/Taylor the formaliser
feared — so **A' is the least-Lean route** (no restructure, no WLOG, no Taylor); (2) the coupled producer
decomposes into 5 build-ready sub-lemmas (Codex Q3, refined). Decorrelated Codex (xhigh) on both.

## Part 1 — A' vs B RE-ADJUDICATED: A' (pointwise), NOT germ/Taylor

**The formaliser's premise (germ/Taylor required) is OVERTURNED.** Their worry: hS1' places the
last-layer pivot-read INSIDE the product, so the map relating `deepestEFull²` to `Sreg` is `w`-dependent.
But hS1' (`hs1prime-verdict.md:28`) shows the colPerm is `colPerm_J(Mdev)·Qf = Mdev·(Pπ·Qf)` — `Pπ` a
FIXED orthogonal permutation matrix on the OUTPUT (H2) column side, adjacent to `Qf_last` (the last
factor's output = the product's output). It is NOT on an internal varying interface. So:

- `deepestEFull²(w) = regE( reindex(rThr, pivotThr J)( ∏ framedParamsPivot(w) ) )`, and after telescoping
  the framed product's residual = `reindex(rThr, pivotThr J)` of the SAME residual `N(w) = ∏A(w) − B`,
  with the deviation columns carrying `Pπ`. By FACT2 (`reindex(rThr, pivotThr J)(M·Pπ) = reindex(rThr,
  rThr)(M)`, VERIFIED), this equals `regE( reindex(rThr, rThr)( N-conjugated ) )` — the THRESHOLD read.
- `Sreg(w) = regE( reindex(rThr, pivotThr J)( N-conjugated ) )` — the PIVOT read.

**Both are fixed linear reindexings of the SAME residual `N(w)`.** Pointwise comparability via two FIXED
invertible maps:

    deepestEFull²(w) = ‖ E_thr · vec(N-conj(w)) ‖²,   Sreg(w) = ‖ E_piv · vec(N-conj(w)) ‖²,
    E_thr, E_piv fixed invertible (reindex permutations + the unit QL) ⇒ both Gram PD, SAME kernel.

Exact cert (r=1,H0=1,H2=2,J:0↦1): generalized eig `[c₁,c₂]=[0.5195,1.9250]`, both Gram spectra identical
`{3.394,10.606}`. **No Taylor, no isLittleO** — a fixed finite-dim Frobenius/norm comparability lemma.

**The corner is NOT a floating −1** (the trap that sank my earlier hand-models): `deepestEFull` subtracts
the corner in its OWN pivot reindex (the `framedParamsPivot` corner is `reindex(rThr, pivotThr J).symm
(fromBlocks 1 0 0 0)`, landing the 1 at the PIVOT diagonal = 0 residual; banked `deepestEFull_base`).
FACT2's threshold-conversion applies ONLY to the deviation, NOT the corner. So `N(w)` is a genuine
residual (→0), no `−1` re-introduced. **Soundness-critical (relay to formaliser):** the proof must keep
the corner subtraction in the pivot convention (as the def does), and apply FACT2 only to the deviation.

**Ranking (Codex Q2 + my cert):**
1. **A' pointwise fixed-map comparability** — least Lean. Two residual identities + a fixed-invertible
   Frobenius comparability (the banked `conjugation_frobenius_comparable`/`dlnLoss_two_sided_of_frame`
   machinery DOES apply, contrary to the formaliser's read — because after FACT2 it IS a fixed
   reindex+QL conjugation, not an internal-interface mix).
2. **B front-pivot WLOG** — sound (loss identity exact, MP, no PIN1) but invasive (transport `QL`
   coherently, `Π_J` folded into every endpoint-frame statement). The fallback.
3. **A germ/Taylor** — most expensive, NOW UNNECESSARY (the premise was wrong).

**Net: A' (pointwise). NO restructure, NO WLOG, NO germ/Taylor.** The formaliser's germ premise rested on
believing `Π_J` interleaves with varying factors; hS1' shows it's fixed at the output. The coupled `𝓝`
is needed regardless (Part 2).

## Part 2 — the coupled producer, build-ready sub-lemmas (dependency order)

The producer needs a SINGLE `U ∈ 𝓝 w0` satisfying all conjuncts. Each conjunct holds on its own eventual
nbhd; `U` = the finite intersection. Build order:

### (i) the (b)-atom — `deepestEFull_Sreg_comparable`  [Part-1 route, A']
    theorem deepestEFull_Sreg_comparable (H r … J Pf Qf …) :
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ w in 𝓝 w0,
        c₁ * Sreg w ≤ (∑ i, deepestEFull … (split w) i ^ 2)
          ∧ (∑ i, deepestEFull … (split w) i ^ 2) ≤ c₂ * Sreg w
Proof: the two residual identities (`deepestEFull` reads = `reindex_thr(N-conj)` via FACT2;
`Sreg` = `reindex_piv(N-conj)`) + a GENERIC fixed-invertible-reindex Frobenius comparability lemma. The
fixed maps' operator norms give `c₁ = σ_min²`, `c₂ = σ_max²`. Actually `∀ᶠ` is even unneeded for the
COMPARABILITY (it's pointwise on the whole chart where the reindex is defined) — but stated `∀ᶠ` to
compose uniformly. **Module home:** NOT `DeepestSchurComparability` (circular — references `deepestEFull`).
Put in a HIGHER module that imports `deepestEFull`: `GaugeChart.DeepestEFullSregComparability` (new) or
inline in the producer module. The low-level module keeps only the generic fixed-map Frobenius lemma.

### (ii) S5a — `eventually_P00_invertible`
    theorem eventually_P00_invertible (H r … ) :
      ∀ᶠ w in 𝓝 w0, IsUnit (P00 w)    -- equivalently (P00 w).det ≠ 0
Proof: `P00 w = toBlocks₁₁(reindex_piv(prod framedParamsPivot w))`; at `w0`, `P00 w0 = 1` (the corner).
`det P00` continuous in `w` (prod entries continuous), `det (P00 w0) = 1 ≠ 0` ⇒ `det ≠ 0` eventually.
Provides `Invertible P00` + a bound `‖⅟P00‖ ≤ M` on the nbhd.

### (iii) S5b — `eventually_leak`
    theorem eventually_leak (ht : 0 < t … ) :
      ∀ᶠ w in 𝓝 w0, (∑ i j, (P10·⅟P00·P01) i j ^ 2) ≤ t² * Sreg w
Proof: `P01 w0 = 0`, `P10 w0 = 0` (off-diagonal residual vanishes at the corner); `⅟P00` bounded (ii).
Cauchy-Schwarz / sub-multiplicativity: `‖P10⅟P00 P01‖² ≤ ‖⅟P00‖²‖P10‖²‖P01‖² ≤ t²·(‖P10‖²+‖P01‖²) ≤
t²·Sreg` for a suitable `t` and small enough nbhd. (Depends on (ii).)

### (iv) (d,e) — `eventually_core_comparable`  [wiring to the BUILT atom]
    theorem eventually_core_comparable (H r … ) :
      ∃ c₁ c₂, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ w in 𝓝 w0,
        c₁ * deepestCoreF (coreAbsorb w) ≤ (∑ i j, (P11 − P10⅟P00 P01) i j ^ 2)
          ∧ (∑ i j, (P11 − P10⅟P00 P01) i j ^ 2) ≤ c₂ * deepestCoreF (coreAbsorb w)
Pure wiring to the BUILT `schur_core_germ_comparability` (`R = P11 − P10⅟P00 P01` = the global Schur;
the atom's germ form gives the two-sided bound). Depends on (ii) (for `⅟P00`).

### (v) the final producer — `hproducer`
    theorem hproducer (ht : 0 < t … ) :
      ∃ U ∈ 𝓝 w0, ∀ w ∈ U,
        hconj w ∧ bComparable w ∧ IsUnit (P00 w)
          ∧ (leak bound) ∧ coreComparable w
Proof: `hconj` is the S0–S3 telescope+normalize (the framedbody-cert S0–S3, banked-atom chain — UNCHANGED
by this re-spec). Then `U := U_b ∩ U_5a ∩ U_5b ∩ U_de` (the eventual nbhds of (i)–(iv)); finite
intersection of `𝓝 w0` members is a `𝓝 w0` member (`Filter.inter_mem`). Each conjunct holds on `U` by
monotonicity (`Filter.Eventually.mono`).

## Dependency order (build sequence)
1. generic fixed-invertible-reindex Frobenius comparability lemma (low-level, `DeepestSchurComparability`).
2. (i) `deepestEFull_Sreg_comparable` (new module `GaugeChart.DeepestEFullSregComparability`, imports
   `deepestEFull` + the FACT2 reindex identity + lemma 1).
3. (ii) `eventually_P00_invertible` (continuity of det).
4. (iii) `eventually_leak` (needs ii).
5. (iv) `eventually_core_comparable` (wires the BUILT `schur_core_germ_comparability`, needs ii).
6. (v) `hproducer` (the framedbody S0–S3 `hconj` + intersect i–iv).
Multi-tide OK: 1–2 (the (b)-atom), then 3–5 (the eventual-nbhd atoms, parallelizable), then 6 (assembly).

## Import structure (resolved)
- `DeepestSchurComparability` (low-level): generic Frobenius/fixed-map comparability lemmas ONLY — no
  mention of `deepestEFull` (avoids the circular reference).
- `GaugeChart.DeepestEFullSregComparability` (new, higher): the (b)-atom `deepestEFull_Sreg_comparable`,
  imports `deepestEFull` + `DeepestSchurComparability` + the FACT2 reindex identity.
- the producer module (`DeepestGaugeConstruction`): imports the above + the BUILT `schur_core_germ_comparability`,
  assembles (v).

## Scope / caveat (honest)
- The pointwise fixed-map (b)-comparability is exact-certified at r=1/H0=1/H2=2 (the PD generalized-eig).
  The structural argument (FACT2 makes the deviation threshold-effective; corner subtracted in pivot conv;
  two fixed reindexings of the same N ⇒ kernel-equal PD forms) is convention-uniform but I did NOT
  symbolically enumerate H0>r / general M. **Soundness-critical for the formaliser:** (1) apply FACT2 to
  the DEVIATION only, keep the corner in the pivot convention (NOT colPerm the corner — that re-introduces
  a spurious −1); (2) the generic Frobenius comparability lemma needs both reindex maps invertible (they
  are — permutations × the unit QL).
- If the general-H pointwise proof snags (e.g. Lean needs the explicit operator-norm bound on the
  composite reindex map), that's the on-call seat; B (front-pivot WLOG) is the validated fallback.

## Files
- `/tmp/hprod_clean.py` (the correct clean-residual PD cert), `hprod_cancel.py` (FACT2 + corner
  reconciliation), `a_kernel.py` (the generalized-eig). `/tmp/hprod_codex/answer.md` (the clean consult).
  Earlier `hprod_germ.py`/`a_general.py` mis-placed the corner (the lesson: corner stays in pivot conv).
