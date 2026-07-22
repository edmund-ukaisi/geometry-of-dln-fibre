# Elder Gap B resolution + verbatim forms + operator high-level read (2026-07-23, banked from the elder send)

ELDER RESUME — fresh process, reconstructed from repo (charter/compass/owed-register/journal-tail/the Lean objects + AxCheck footprint); no prior transcript in context, so everything below is re-derived against the tip, not recalled. Two deliverables.

════════════════════════════════════════════════
DELIVERABLE 1 — GAP B CAP: RESOLVED. The reversal stands, and the decorrelated Codex read SHARPENS it in a load-bearing way that CHANGES the render.
════════════════════════════════════════════════

**(a) The concern-1 reversal is CORRECT — verified, not recalled.** I rebuilt coreGen symbolically over 6 dimension vectors. Result, uniform: coreGen is degree-1-homogeneous AND vanishing over `layerCoords d ℓ` for EVERY layer ℓ<N (multilinearity across layers — each product term carries exactly one factor per layer); it FAILS both over `blockCoords d ℓ` exactly when the running-min cap bites (widthMinUpto d ℓ < d_ℓ). The witness is exactly the one the machine check named: d=![1,2,1], layer 1 (widthMinUpto=min(1,2)=1 ⟹ blockCoords={col 0}); coreGen = A₂[0,0]·A₁[0,0] + A₂[0,1]·A₁[1,0], and zeroing blockCoords leaves the term A₂[0,1]·A₁[1,0] ("m1_01·m0_10") ≠ 0. So the base atom must be stated over `layerCoords`. The pinned "…HomogeneousDeg1On over blockCoords" (journal 22:10) is FALSE at the root, ℓ=1. Kill confirmed.

**(b) THE DECORRELATED FINDING (Codex xhigh, artifact: threads/L3T/codex/gapB-cap-{prompt,answer}.md) — the cap is SHEAR-DEPENDENT, not shear-independent. This corrects the design.** Codex, asked independently whether the strict-transform residual at the descended layer is confined to the capped columns, returned FAILS: at a δ=1 clear (pivot x₀=t, x₁=tv) the strict transform of y₀x₀+y₁x₁ is r = y₀ + v·y₁, which reads y₁ = the over-cap column. Its own inference: the basis change y′₀ = y₀+v·y₁ restores capped support — and that basis change is EXACTLY `edgeShearRaw`/`canonShearOf`, baked into foldResid's strict transform (MonumentAtlas:454); in the sheared frame r = y′₀, supported on the one capped coord. Codex Q3 also proves homogeneity and the cap are logically INDEPENDENT (f=y₁ has (A) not (B); f=y₀² has (B) not (A)).

CONSEQUENCE: the journal's characterization of foldResid_layerHomogeneous as "SHEAR- AND PIVOT-INDEPENDENT, off the CENTER pin only" (tick 20:40, 13866) is right FOR THE HOMOGENEITY (conjunct-2, a linear basis change preserves per-layer degree) but WRONG for the CAP. The cap rides the SHEAR pin (canonShearOf / ShearWithinCarve), NOT the center pin and NOT homogeneity. The design's plan for `foldResid_layerHomogeneous` to "subsume hslot" and discharge `realBranch_appendResidDescent` (conjunct-1 over blockCoords) cannot work: homogeneity is over layerCoords and is independent of the cap.

**(c) The cap is load-bearing and cannot be dodged.** I checked: `realBranch_cover` (MonumentAtlas:988, PROVEN) needs `supportAt(parent) ⊆ ed.center` with BOTH widthMinUpto-capped; canonCenterOf caps the col axis (Case1Wire:276-277). Relaxing supportAt to layerCoords would break the already-sorry-free conjunct-A route (deg1SupportedOn_center_of_hslot). So the child slot's conjunct-1 over blockCoords(S+1) is a GENUINE, non-negotiable obligation.

**THE RULING (verbatim below).** `Deg1SupportedSlot` already splits the two concerns — use that, do NOT re-fuse them:
  • conjunct-2 `PerLayerDeg1From` is over `layerCoords` (MonumentAtlas:527) — this is where homogeneity goes.
  • conjunct-1 `∃c, resid = Σ_{i∈S} c_i·u_i` over `S = supportAt = blockCoords` — this is the cap.
- `foldResid_layerHomogeneous` (over layerCoords, he_lin, non-terminal) discharges CONJUNCT-2 only.
- The CAP (conjunct-1 descent) is a SEPARATE lemma consuming the SHEAR (canonShearOf/ShearWithinCarve) + the parent's conjunct-1 (hslot) — it is part of the WALL's re-factoring content (seat-L4's BlockDivision / the Schur fold: "child re-factors on C′=supportAt(child)"), NOT a homogeneity corollary. Name it a FRONTIER-LEAF-CANDIDATE, not strike-able: I have verified the shear confines in the d=![1,2,1] base instance (r=y′₀), but whether canonShearOf's value confines at coupled corank≥2 IS the wall — do not disguise it.
- The hslot→hhomog "re-wire" (subsume hslot) is RETRACTED: hslot is NOT subsumed; the step consumes BOTH hslot (cap) and homogeneity (degree).

────────── VERBATIM FORMS (for arch-C) ──────────

-- (1) predicate — vanishing strengthening of AffineOn, over the FULL layer:
```
def HomogeneousDeg1On {D : ℕ} (f : (Fin D → ℝ) → ℝ) (X : Finset (Fin D))
    (V : Set (Fin D → ℝ)) : Prop :=
  AffineOn f X V ∧ ∀ u ∈ V, (∀ x ∈ X, u x = 0) → f u = 0
```
RENDER NOTE: over X=∅ the vanishing clause degenerates to "f≡0 on V" (vacuous premise). layerCoords d ℓ = ∅ for ℓ ≥ N, so assert HomogeneousDeg1On only at ℓ < N (guard it); conjunct-2 itself uses AffineOn (harmless over ∅), so PerLayerDeg1From is unaffected.

-- (2) BASE atom (he_lin; TRUE — sympy-verified all layers ℓ<N):
```
theorem coreGen_layerHomogeneous {N : ℕ} (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he_lin : IsLinearMap ℝ ⇑e)
    (i : Fin (d (Fin.last N) * d 0)) (ℓ : ℕ) (hℓ : ℓ < N) :
    HomogeneousDeg1On (coreGen d e i) (layerCoords d ℓ) Set.univ
```

-- (3) STEP / standalone (over layerCoords; he_lin threaded from L5; non-terminal guard) — discharges conjunct-2:
```
theorem foldResid_layerHomogeneous {N : ℕ} (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (he_lin : IsLinearMap ℝ ⇑e)
    (p : TreePath d) (hnonterm : ¬ N ≤ p.conState.layer)
    (hbranch : p.IsRealBranch e)
    (j : Fin (foldNR d p)) (ℓ : ℕ)
    (hℓsup : supportLayerOf p.conState ≤ ℓ) (hℓN : ℓ < N) :
    HomogeneousDeg1On (foldResid d e p j) (layerCoords d ℓ) (foldRegion d e p)
```
(induction on p: base = coreGen_layerHomogeneous; step = the uniform `homogeneousDeg1On_comp_of_fixing` reusing the banked stepMap/qm hfix/hagree + case11_pivot_decode_lt. u_pivot is excluded at δ=1 because it is not HomogeneousDeg1On at layer p.layer+1 — the vanishing clause forbids the constant-1 transform.)

-- (4) the CAP — the SEPARATE argument (conjunct-1 descent), shear-consuming. NOT homogeneity:
```
theorem realBranch_appendResidDescent {N : ℕ} (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (p : TreePath d) (ed : TreeEdge d p) (hlayer : ed.nextState.layer + 1 < N)
    (hbranch : (p.extend ed).IsRealBranch e)
    (hslot : ∀ j, Deg1SupportedSlot d (foldResid d e p) j
      (supportAt d p.conState.layer p.conState.cleared)
      (supportLayerOf p.conState) (foldRegion d e p)) :
    ∀ j, ∃ c : Fin (flatDim d) → (Fin (flatDim d) → ℝ) → ℝ,
      (∀ i, ContinuousOn (c i) (foldRegion d e (p.extend ed))) ∧
      (∀ u ∈ foldRegion d e (p.extend ed), foldResid d e (p.extend ed) j u
        = ∑ i ∈ supportAt d (p.extend ed).conState.layer (p.extend ed).conState.cleared,
            c i u * u i)
```
This is `realBranch_multiAffine_step`'s conjunct-1. It CONSUMES canonShearOf (via IsRealBranch's shear pin) — the shear is what maps the strict transform's over-cap dependence (Codex's v·y₁) into the capped block. `foldResid_layerHomogeneous` supplies conjunct-2 alongside; the two together rebuild the child `Deg1SupportedSlot`. Keep both.

════════════════════════════════════════════════
DELIVERABLE 2 — OPERATOR HIGH-LEVEL READ (4 questions; stern voice)
════════════════════════════════════════════════

**Q1 — Fidelity to Lehalleur–Rimányi + Aoyagi; drift.** The objects (buildTree/conOracle/foldResid/the block-center blow-up/the leaves) are Aoyagi's Cases-1&2 recursion TRANSCRIBED, not a re-derivation — corroborated by the documented typo-ledger (Def-3, Lemma-1 direction, T-profile comparability, Case-2 raw-width, per-step principality, δ-as-state, block-center-with-spectators) where the team caught HER errors against page images and corrected TOWARD the paper. ChainNF/boostReady is a Lean encoding of the b-chain divisibility (Aoyagi's own invariant), not a new object. Fidelity discipline is WORKING: today's Gap-B episode is the evidence — a machine check + decorrelated Codex caught a false "shear-independent cap" characterization BEFORE it was rendered. NO drift from the paper's path. The historical drift (chart route) is settled-dead (compass F1, category-proven). One standing caution: the payoff still rests on `cited_aoyagi_lower_ax` + `cited_watanabe_upper_ax` + the monument `sorryAx` — until the wall lands, "rlct = ½·codim" is CITED, not proven. Name=content holds only if every headline says so.

**Q2 — Owed-maths ledger.** Honest and small. The genuinely-open surface = O2 (the 8 monument leaves + THE WALL: coupled corank≥2 divisibility). Every wave-tail unit the register recommended (M1/M2/M3/M8, O5/P2, P1-r0) was ALREADY landed when recommended — the register's value was the naming, its status column was systematically stale until the author+ground-truther pairing. Objects A/C/D + E-combinatorial are landed sorry-free. Runway (named, not hidden): P3 general-rank lane, P1/P2 printed closed forms, P7 analytic ρ. No hidden monuments beyond the two already-named (the resolution wall; the zeta continuation).

**Q3 — Trajectory vs the rising sea.** The sea IS rising — A/C/D/E-comb landed, the wall's substrate (BlockDivision, exists_graded_decomp, terminal_bezout, canonCenter, L1) banked. BUT the stern note: the recent re-open + FOUR boostReady re-scopes (one-liner → 2 lemmas → path-induction → ChainNF sub-expedition) + the Gap-B design getting the cap WRONG TWICE (blockCoords, then "shear-independent") are symptoms of OVER-ENGINEERING THE ENCODING relative to the math. The math is bounded and buildable — my base-case check + Codex confirm the mechanism, including that the shear does the confining. The risk is manufacturing statement-complexity (statement-risk ≫ proof-risk, per the altitude note). RECOMMENDATION: hold the "one construction pin + derived lemmas off IsRealBranch" line; resist further predicate proliferation; the closed loop IS working (defects caught pre-render), keep the SPECIFY-first gate.

**Q4 — the ρ-seam runway.** P6.2 CLOSED and faithful: ρ = chainHeight of the binding-minimiser poset = θ = a(ℓ−a)+1, the actual poset object (witness [2,2,2,2,2] corrected the antichair speculation to chain). The analytic half — ρ = zeta-pole multiplicity — is monument-class (Mathlib lacks meromorphic continuation), correctly deferred = P7. The runway is honest: the combinatorial object is BUILT; the analytic identification is a cite for the next expedition. No overclaim here.

Artifacts: base-case check /tmp/gapb_check.py (re-runnable); Codex read expeditions/2026-07-17-aoyagi-engine/threads/L3T/codex/gapB-cap-{prompt,answer}.md. Descent render is UNBLOCKED with the verbatim above — the key correction for arch-C is that homogeneity ≠ the cap, so hslot stays and conjunct-1 is a shear-consuming frontier leaf, not a homogeneity corollary.