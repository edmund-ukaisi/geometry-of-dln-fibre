# h2 diffeo-bridge design cert — `rlctAtOn(Sreg_E + Score) = rlctAtOn(Sreg_E + coreΦ)` via an explicit Ψ

Build-ready design (no Lean) for the goal lemma (`DeepestGaugeConstruction.lean` ~3143, `hstep2`):
`rlctAtOn Φscore wstar = rlctAtOn Φcore wstar`, with
`Φscore x = ∑(regStraighten(split x)).1² + Score x`, `Φcore x = ∑(regStraighten(split x)).1² + coreΦ x`,
`Score = frobSq(Rcore)`, `coreΦ = deepestCoreF(coreAbsorb(split x)).2.1`. Feeds banked
`rlctAtOn_comp_localDiffeo` (`DeepestRegAbsorbIFT.lean:283`).

Verified exactly (sympy + numpy, all r,M shapes): the composition identity, Sreg-invariance, the fderiv,
the fixpoint. Decorrelated Codex (xhigh) reviewed the smoothness/transport story.

---

## CORRECTION to the naive design (load-bearing — a core-only Ψ does NOT work)

The naive `Ψ: T1 ↦ (1−K)·T1 + K·Z1(1+X1)⁻¹Y1` (act on the last-layer core only) gives `coreΦ∘Ψ = Score`
EXACTLY, **but it does NOT fix `Sreg_E`.** Reason: `Sreg_E = ‖P00−I‖² + ‖P01‖² + ‖P10‖²` is the FULL
framed-product reg residual (`deepestEFull`, `:415` — the "core leak" the def comment names), and
`P01 = A0·Y1 + Y0·T1` DEPENDS ON `T1`. So changing `T1` shifts `Sreg_E` by `O(t⁴)` ≠ 0 (verified:
`|ΔSreg| ~ 5e-6` at t=0.1). Both `Φscore` and `Φcore` SHARE the reg term `∑(regStraighten(split x)).1²`,
so `Φcore∘Ψ = Φscore` requires `Ψ` to fix that reg term — i.e. fix `(P00, P01, P10)`. The core-only
action fails this. (Codex independently flagged this: "Sreg_E must truly factor only through the slots
fixed by Ψ; if it contains `Y0·T1`, changing T1 would not fix it.")

## THE CORRECT Ψ — a JOINT `(T1, Y1)` action (verified exact, all shapes)

Act on BOTH the last-layer core `T1` AND the last-layer reg read `Y1` (= `Y_last`), holding `P01` fixed.
The two constraints:
- (E1, the core identity) absorbed `S1' = (1−K)·S1`, i.e. `T1' − Z1·A1⁻¹·Y1' = (1−K)·(T1 − Z1·A1⁻¹·Y1)`.
- (E2, Sreg-invariance) `P01` fixed: `A0·Y1' + Y0·T1' = A0·Y1 + Y0·T1`.
  (`P00 = A0A1 + Y0Z1` and `P10 = Z0A1 + T0Z1` contain neither `T1` nor `Y1`, so they are fixed AUTOMATICALLY;
  only `P01` needs the joint fix.)

**Closed form** (solve E1,E2 for `(T1', Y1')`; `A0,A1` units near wstar, `K = Z1·⅟P00·Y0`):

    W   := I_{M1} + Z1·A1⁻¹·A0⁻¹·Y0            (= I + O(read²), an M1×M1 unit near wstar)
    T1' := W⁻¹·[ (I−K)·S1 + Z1·A1⁻¹·Y1 + Z1·A1⁻¹·A0⁻¹·Y0·T1 ]      (S1 = T1 − Z1·A1⁻¹·Y1)
    Y1' := Y1 + A0⁻¹·Y0·(T1 − T1')

Everything else (reg X0,X1,Z0; cores T0; spectators) is FIXED. Verified across r=1/2, M=(1,2,1),(2,2,2),
(2,2,1),(1,3,2),(3,2,1): `|ΔSreg_E| ≈ 0`, `|coreΦ(Ψx) − Score(x)| ≈ 0`, hence
`(Sreg_E + coreΦ)∘Ψ = Sreg_E + Score` to machine precision (~1e-17).

Note `T1 − T1' = O(read³)` (so `Y1' = Y1 + O(read⁴)` — the Y1 compensation is higher-order; the dominant
action is still `T1 ↦ (1−K)T1 + …`). This makes the fderiv clean (below).

## (1) Ψ on the FLAT coordinates — and why `split` smoothness is NOT a blocker

`Ψ_flat = split⁻¹ ∘ Ψ_split ∘ split`, where `Ψ_split` is the joint `(T1,Y1)` action on `DeepestSplit`.
Codex raised a "loud red flag" that `split : ≃ₜ` (homeomorphism) does not transport smoothness. **I read
the `split` definition (`DeepestSplitConcrete.lean:32`) and it CLEARS the flag:**

    deepestSplit = (Homeomorph.subRight wstar)                    -- w ↦ w − wstar (affine translation)
      ∘ (Homeomorph.piCongrLeft (deepestRoleIndexEquiv))          -- coordinate PERMUTATION of Fin→ℝ (LINEAR)
      ∘ (Homeomorph.sumPiEquivProdPi …)                           -- regroup ⊕ into × (LINEAR)
      ∘ (Homeomorph.prodCongr (refl) (sumPiEquivProdPi …))        -- (LINEAR)

So `split` is an **affine isomorphism** `split(w) = L(w − wstar)` with `L` a linear coordinate-iso. It is
ContDiff⊤ AND a diffeo; its derivative everywhere is `L` (a `≃L`). The `≃ₜ` typing UNDERSTATES it.
**Action item for the formaliser:** promote `split` (or just `deepestSplit`) to a smooth affine chart —
a `ContDiff⊤` + `HasStrictFDerivAt split L w` fact. Each factor is C⊤: `subRight` is translation
(deriv id); `piCongrLeft`/`sumPiEquivProdPi` on `Fin→ℝ` are coordinate permutations/regroupings —
each output coord IS an input coord, so ContDiff is `continuous_apply`-trivial (Mathlib has the
`ContinuousLinearEquiv`/`LinearEquiv` lifts: `LinearEquiv.piCongrLeft'`, the pi-regrouping CLEs). This is
mechanical, NOT multi-tide — but it IS a real prerequisite (it does not exist banked yet). **If promoting
`split` is fiddly, the cleaner route (Codex option 1) is to apply `rlctAtOn_comp_localDiffeo` in
`DeepestSplit` coordinates** — but the goal `hstep2` is stated in flat coords, so a flat `Ψ` (or a
flat↔split RLCT transport) is needed. Recommend: prove `split` is a smooth affine equiv (a `≃L` up to
translation) ONCE as a reusable lemma; then `Ψ_flat` inherits ContDiff/fderiv from `Ψ_split` by chain rule.

## (2) The composition identity `coreΦ ∘ Ψ = Score` — the exact chain

On the inner ball (χ=1, coreAbsorb's cutoff = raw Schur shift):
1. `Ψ` fixes reg/spec and `T0`; changes `(T1,Y1) ↦ (T1',Y1')` per the closed form.
2. `U1 := Z1·A1⁻¹·Y1` (the absorb shift datum) — note `Y1` changes, so recompute: by E1 directly,
   absorbed `S1' = T1' − Z1·A1⁻¹·Y1' = (I−K)·(T1 − Z1·A1⁻¹·Y1) = (I−K)·S1` (this is exactly E1's RHS).
3. `S0' = T0 − Z0·A0⁻¹·Y0 = S0` (T0, reg fixed). So `∏(absorbed) = S0·(I−K)·S1`.
4. Banked `deepestCoreF_coreAbsorb_eq_prodSchur` (`:1940`): `coreΦ(Ψx) = frobSq(S0·(I−K)·S1)`.
5. Banked LDU `rcore_schur_factor_of_corner_split` (`DeepestBlockDecomp.lean:207`):
   `Rcore = S0·(I−K)·S1` with the SAME cores `S0,S1` (G0,G1 = framedParamsPivot(split x) blocks =
   `(1+X_s, Y_s, Z_s, T_s)`) and `K = (G1)₂₁·⅟(G0G1)₁₁·(G0)₁₂ = Z1·⅟P00·Y0`.
6. So `coreΦ(Ψx) = frobSq(Rcore(x)) = Score(x)`. ∎
   (Product-order convention: `deepestCoreF = dlnLoss(deepestM)` uses `prod = layer0·layer1 = S0·S1`,
   matching the LDU's `S0·(…)·S1` order. Confirm the `prodAux` fold direction in-build.)

Combined with `Sreg_E(Ψx) = Sreg_E(x)` (E2): `Φcore∘Ψ = Φscore` on the inner ball.

## (3) The fderiv + domain hypotheses (the `rlctAtOn_comp_localDiffeo` antecedents)

- **`HasStrictFDerivAt Ψ_flat (id : flat ≃L flat) wstar`:** verified `D(Ψ_split − id)(0) = 0` exactly
  (the `(T1,Y1)` change is `O(read³)`: `K = O(read²)`, `S1 = O(read)`, `W − I = O(read²)`). So
  `Ψ_split'(0) = id`, hence `Ψ_flat'(wstar) = L⁻¹∘id∘L = id`. The `e` is the identity `≃L`. (Mirrors the
  banked `hasStrictFDerivAt_coreShearHomeo_symm_zero` pattern — derivative id at 0 when the shift's
  derivative vanishes.)
- **`Ψ_flat wstar = wstar`:** verified (the change vanishes at wstar; `K(wstar)=0`, reads → 0). ✓
- **`ContDiff ℝ ⊤ Ψ_flat` (GLOBAL — the heaviest hypothesis):** the raw Ψ has inverses `⅟P00`,
  `(1+X1)⁻¹`, `(1+X0)⁻¹`, `W⁻¹` — smooth only on the common invertibility locus (a nbhd of wstar). Use
  the **cutoff-bump** pattern (banked `schurCutoffShift = χ·schurShiftRaw`, `DeepestSchurShift.lean:310`):
  multiply the entire `(T1,Y1)`-CORRECTION by a `ContDiffBump` χ with χ=1 near wstar and `tsupport χ`
  inside the common invertibility locus. The cutoff Ψ_χ is GLOBAL ContDiff⊤, EQUALS honest Ψ on the
  inner ball (χ=1), and keeps `Ψ_χ'(wstar)=id` (χ=1 near wstar) and `Ψ_χ(wstar)=wstar`. **Then the
  composition identity holds as a GERM/eventual equality** (`Φcore∘Ψ_χ = Φscore` on the inner ball),
  which suffices because `rlctAtOn` is a germ invariant. Codex confirmed all three antecedents hold for
  the cutoff version.

The final chain:
`rlctAtOn Φcore wstar =[localDiffeo, Ψ_χ] rlctAtOn(Φcore∘Ψ_χ) wstar =[germ, χ=1 nbhd] rlctAtOn Φscore wstar.`
(`rlctAtOn_comp_localDiffeo` gives the first `=`; `rlctAtOn` germ-locality + `Φcore∘Ψ_χ = Φscore` ∀ᶠ gives
the second.)

## (4) Honest tide estimate (a9711b920 said multi-tide — CONFIRMED, ranked)

Heaviest → lightest:
1. **`split` smooth-affine promotion (NEW prerequisite, ~1 tide):** prove `deepestSplit` is ContDiff⊤
   with `HasStrictFDerivAt = L` (a coordinate `≃L` ∘ translation). Mechanical (each factor is a banked
   Mathlib coordinate iso) but NOT yet in the library, and load-bearing (Codex's red flag). Could be
   sub-tide if the `LinearEquiv.piCongrLeft'` / pi-regroup CLE lifts are directly usable.
2. **Cutoff global smoothness + the inverses' smoothness/support (~1 tide):** the `W⁻¹`, `⅟P00`,
   `(1+X_s)⁻¹` ContDiff-on-the-unit-locus + the χ-cutoff. Reuses the `schurCutoffShift` pattern, but
   `⅟P00` (full-product (1,1) block inverse) and `W⁻¹` are NEW inverse-smoothness lemmas (not the
   per-layer `(1+X_s)⁻¹` already banked). Moderate.
3. **Composition-identity plumbing (~1–2 tides):** the chain (2) through `split`/`coreAbsorb`/
   `paramsEquivFlat`/`framedParamsPivot` defeq + the banked LDU + `deepestCoreF_coreAbsorb_eq_prodSchur`.
   The E1/E2 algebra is light, but threading it through the actual split/absorb encodings (the joint
   `(T1,Y1)` action expressed in the flat `paramsEquivFlat`-encoded core+reg slots) is fiddly bookkeeping.
4. **Strict-fderiv = id (sub-tide):** once Ψ is in smooth coordinates, the `O(read³)`-correction ⟹
   deriv id is small (mirrors the banked coreShear fderiv lemma).
5. **#1 measurability (mechanical, bundles in):** the entrywise `nonsing_inv` measurability for `Score`
   (the other residual `sorry` at ~3128) — no design, pure Mathlib plumbing.

**Total: ~3–4 tides.** The heaviest genuinely-new piece is the `split` affine-smoothness promotion (#1
above) — flag it FIRST, since the whole flat-Ψ route depends on it (or on switching to DeepestSplit
coords). The cleanest de-risking: prove `split` smooth-affine as a standalone reusable lemma before
touching Ψ.

## Residual risks / honest caveats
- The joint `(T1,Y1)` Ψ is heavier than the core-only map; its `W⁻¹` is a second inverse to cut off.
  If a cleaner Ψ exists (fixing the reg blocks with a single slot action), it would simplify — but I did
  NOT find one (every core read leaks into Sreg_E; the joint action is the minimal fix). Worth a
  formaliser sanity-check that no simpler reparametrization exists.
- The product-order convention (`prod = S0·S1` vs `S1·S0`) must match between `deepestCoreF`'s `prodAux`
  fold and the LDU's `S0·(…)·S1` — confirm in-build (low risk, L=2 two-factor).
- `rlctAtOn` germ-locality (step "=[germ]") — confirm `rlctAtOn` depends only on a nbhd of wstar (it does
  by definition — the smallest pole of `∫_U f^{-s}`; the banked `rlctAtOn` API should have an
  `eventuallyEq` congruence; if not, that is a small add).
- All verification is exact-algebra/numeric at the L2 producer; the L≥3 gap is separate.

## Artifacts (re-runnable; mine + Codex)
- `/tmp/h2confirm/` — the Ψ design + verification (core-only fails Sreg; joint (T1,Y1) closed form exact;
  fderiv=id; all shapes).
- Codex: `codex/h2-diffeo-{prompt,answer}.md` (smoothness/transport review; flagged `split` + the Sreg
  leak; confirmed the cutoff route).
- Supersedes the `h2-ripple-confirm.md` "the fix is 1 tide" optimism: the BUILD revealed the joint action
  + split-promotion, making it ~3–4 tides (a9711b920's multi-tide call was right).
