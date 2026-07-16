# Adjudicate: the sound route to an ENNReal `∃ C < ⊤, LHS ≤ C·RHS` domination (all `c'`), Lean 4 / Mathlib measure theory

You are a decorrelated second opinion (xhigh). Adjudicate a **soundness + proof-architecture** question. Exact real/measure analysis. Be concrete about `ℝ≥0∞` (`ENNReal`) subtleties. State FACT vs INFERENCE.

## Setting (deep-linear-network RLCT; you don't need the DLN meaning)

All integrals are Lebesgue lower integrals `∫⁻` valued in `ℝ≥0∞`. `frobSq X = ∑ᵢⱼ Xᵢⱼ²` (≥ 0). `matBox a b 1 = [-1,1]^{a×b}`, `genBox = [-1,1]^{…}` (bounded boxes). `paramsBoxM … 1`, `unitBox d = [0,1]^d` are bounded boxes. `ofReal (t ^ (-c'))` is the `rpow` of a nonneg real. All bases below are ≥ 0.

Fix data (constant w.r.t. the integration variables): dims `u ≥ 1`, `a := M₀−u`, `b := M₁−u`, `M₁ = u+b`, `M₂`, `n`, `m`; a floor `ε > 0`; a frame `Z := Zf z` (an `M₂×n` matrix depending on the param `z`) with `Zᵀ`-rank `≥ m` and a Loewner floor `Z Zᵀ ⪰ ε'²·U U ᵀ` with `U ᵀU = 1` (so `Z` has ≥ m singular values ≥ ε').

For a fixed `z` and a corank matrix `A_cor` (an `(M₁−u)×M₂` matrix), define the **stacked** matrix
`Q_stack(z,A_cor) := fromRows Q_p (A_cor·Z)`, an `M₁×n` matrix, where `Q_p = Q_p(z)` is `u×n`.
The **pivotShell** is `{A_cor | Q_stack Q_stackᵀ ⪰ ε²·1_{M₁}}` (a DOMAIN restriction on `A_cor`; on it `Q_stack` has full row rank `M₁`, which forces `M₁ ≤ n` for nonemptiness).

**LHS** (`pivotDomLHS`), for a universally-quantified real `c'` (NO threshold hypothesis):
```
LHS = ∫z∈paramsBox ∫A_cor∈(matBox ∩ pivotShell z) ∫x=(P,B₁₂,C)∈outerDom ∫D∈genBox
        ofReal( frobSq( fromBlocks P B₁₂ C D · Q_stack(z,A_cor) ) ^ (−c') )
```
`P: u×u`, `B₁₂: u×b`, `C: a×u`, `D: a×b`. `outerDom = box ∩ {IsUnit P}` (⊆ box; can enlarge to box, integrand ≥ 0). Row-splitting the block product: `frobSq(fromBlocks…·Q_stack) = w + κ`,
`w = frobSq([P|B₁₂]·Q_stack)` (top u rows; a fn of P,B₁₂,A_cor,z — NOT C,D),
`κ = frobSq(C·Q_p + D·(A_cor·Z))` (bottom a rows; a fn of C,D,A_cor,z — NOT P,B₁₂).

**RHS** (`pivotDomRHS`), the comparator:
```
RHS = ∫z∈paramsBox ∫v∈[0,1]  ofReal(|v₀|^{J}) ·
        (∫A_cor∈matBox ∫Γ∈genBox  ofReal( ( decLoss(z,v) + frobSq(Γ·(A_cor·Z)) ) ^ (−c') ))
```
where `decLoss(z,v) = v₀²·frobSq(Q_p(z))`, exceptional coordinate `v₀∈[0,1]`, monomial exponent `J = minAdm' − 1` (a nat), `minAdm' = minAdm(reduced chain)`. Note RHS A_cor is over the FULL matBox (no shell), and the corank has NO `C·Q_p` cross-term (Ccross = 0).

## Banked lemmas I can consume (all sorry-free, exact Lean signatures)

1. **Corank peel (S3), coupled variant** `shell_corankPivot_coupled_le`: for `Z` with `b ≤ Z.rank`, `hc' : (a·b)/2 < c'`, any `Ccross`, any `wf : (corank-matrix) → ℝ` with `wf > 0`, any set `sΓ`:
```
∫A_cor∈matBox ∫Γ∈sΓ ofReal((wf A_cor + frobSq(Ccross + Γ·(A_cor·Z)))^(−c'))
  ≤ ∫A_cor∈matBox ofReal( det((A_cor·Z)(A_cor·Z)ᵀ)^(−a/2) · Cresid(a·b) c'
        · (wf A_cor + frobSq(Ccross·(1 − proj(A_cor·Z))))^(−(c' − a·b/2)) )
```
(`proj(Qb) = Qbᵀ(Qb Qbᵀ)⁻¹ Qb`.) REQUIRES `c' > a·b/2`.

2. **Corank peel (S3), Z-uniform** `shell_corankOffSector_le_unif`: on the shell (`Z Zᵀ ⪰ ε²UUᵀ`, `b≤m≤M₂`, `m≤Z.rank`), reduced-convergent `a < m−b+1`, `hc':(a·b)/2<c'`, any Ccross, `w>0`:
```
∫A_cor∈matBox ∫Γ∈sΓ ofReal((w + frobSq(Ccross + Γ·(A_cor·Z)))^(−c'))
  ≤ Cunif · ofReal(w^(−(c'−a·b/2)))
```
with `Cunif < ⊤` free of `Z,Ccross,w`. REQUIRES `c' > a·b/2`.

3. **Pivot box finiteness (D-B)** `lintegral_cube_frobSq_neg_of_finrank_range` / `twoMatBox_rankR_lintegral_lt_top`: for a LINEAR map `L : (Fin N → ℝ) →ₗ (Fin Mout → ℝ)` with `finrank(range L) = rk`, and a measure-preserving flatten `E` of a matrix box onto the cube `[-1,1]^N`:
```
∫x∈matBox ofReal((∑ⱼ (L (E x))ⱼ²)^(−c')) < ⊤    for   c' < rk/2.
```

4. **Radial blow-up (D-A)** `pivotBlock_radial_blowup`: for fixed `Q : M₁×n`, measurable `φ`:
```
∫W:(u×M₁) ofReal(φ(frobSq(W·Q)))
  = ∫ω∈sphere(ℝ^{u·M₁}) ∫r∈(0,∞) ofReal(r^{u·M₁−1}) · ofReal(φ(r²·frobSq(P̂·Q)))
```
`P̂ = matReshape ω` (`frobSq P̂ = ‖ω‖² = 1`). This is over the FULL W-space (no box), an exact CoV EQUALITY.

5. `deeperFlag_shell_core_le`: `RHS = deeperFlagCoreIntegrand ≤ C·comparator.integral(c'−a·b/2)`, `C<⊤`, REQUIRES `c' > a·b/2` and a.e. `decLoss>0`. (This is an UPPER bound on RHS.)

6. `deeperFlagCore_decLoss_pos_ae`: `decLoss(z,v) > 0` a.e.

## Design cert (pen-and-paper, decorrelated Codex-concurred) says

- The pivot integral `J(c'') := ∫_{[P|B₁₂]∈box} frobSq([P|B₁₂]·Q_stack)^{−c''}` is finite **iff** `c'' < u·ρ/2`, where `ρ = rank(Q_stack)` (map `W↦W·Q_stack` = `u` copies of `x↦x·Q_stack`, rank `u·ρ`). On the shell `ρ = M₁`.
- Gate hypothesis present in the theorem: `hpiv : minAdm' ≤ u·ρ` (`ρ = tailMinWidth`, the generic tail rank). **The "bounded integrand via σ_min(P̂)" route is a DEAD END** (integrand is unbounded; finiteness is only via integrable codim-singularity, i.e. D-B).
- The radial blow-up "exposes the v-monomial `r^{u·M₁−1} ↔ |v₀|^{J}`" but finiteness is via the box-codim (D-B), NOT the blow-up.

## THE THEOREM to prove (no threshold hypothesis on `c'`)

`pivotPeel_domination : ∃ C : ℝ≥0∞, C < ⊤ ∧ LHS ≤ C · RHS`  — for ALL real `c'`.
Its ONLY consumer needs: `RHS < ⊤ → LHS < ⊤` (via `lt_of_le_of_lt hle (ENNReal.mul_lt_top hC hRHS)`).
There is ALSO a separately-available `RHS ≠ 0` (from `decLoss > 0` a.e.).

## QUESTIONS (adjudicate each, FACT/INFERENCE)

**Q1 (architecture).** What is the cleanest SOUND way to prove `∃ C<⊤, LHS ≤ C·RHS` for ALL `c'`? Two candidates:
   (A) **Ratio trick**: case `RHS=⊤` (C:=1, `LHS ≤ ⊤`); case `RHS<⊤` prove `LHS<⊤` then `C := LHS/RHS` (needs `RHS≠0`). 
   (B) **Genuine pointwise/integrand domination** valid for all `c'` simultaneously.
   Given the ONLY consumer wants finiteness, is (A) sound and complete? Its crux becomes: **prove `RHS < ⊤ → LHS < ⊤`.**

**Q2 (the crux, THE soundness question).** To prove `RHS < ⊤ → LHS < ⊤` for a UNIVERSALLY-quantified `c'`: the banked corank peels (S3) and pivot finiteness (D-B) BOTH need a threshold on `c'` (`c' > a·b/2` for S3; `c'' < u·ρ/2` for D-B). But the theorem gives NO threshold. So I must EXTRACT constraints on `c'` from `RHS < ⊤`. 
   - Is it true/necessary that `RHS = ⊤` whenever `c'` is at/above the comparator threshold (so `RHS < ⊤ ⟹ c'' < minAdm'/2 ≤ u·ρ/2` by `hpiv`, giving D-B finiteness)? If so, does proving this require a DIVERGENCE lower bound on RHS (a genuinely separate hard lemma), or is there a cheaper way?
   - The regime `c' ≤ a·b/2`: here the integrand `(w+κ)^{−c'}` is over BOUNDED domains — is `LHS < ⊤` then simply because the integrand is bounded (for `c' ≤ 0`) / mildly singular (`0 < c' ≤ ab/2`)? For `0 < c' ≤ ab/2` can I still get `LHS<⊤` cheaply (e.g. dominate `(w+κ)^{−c'} ≤ w^{−c'}` and use D-B with `c' < ab/2 ≤ ... ` — but need `c' < u·M₁/2` which holds since `c'≤ab/2` and `ab/2 ≤ ...`?), WITHOUT S3?
   - Concretely: is the SOUND & COMPLETE decomposition of `RHS<⊤ → LHS<⊤`: **(i)** `c' ≤ 0` trivial-bounded; **(ii)** `0 < c'` and drop κ: `(w+κ)^{−c'} ≤ w^{−c'}` (κ≥0, −c'≤0), then `LHS ≤ ∫z ∫_{A_cor∈shell} ∫_{[P|B₁₂,C,D]∈box} w^{−c'} = vol(C,D,A_cor boxes)·∫z∫_{A_cor∈shell}∫_{[P|B₁₂]∈box} w^{−c'}`, and the inner pivot integral is finite via D-B iff `c' < u·M₁/2` (shell ⟹ rank u·M₁)? But does dropping κ LOSE finiteness (i.e. is `∫ w^{−c'}` over the box actually FINITE for the relevant `c'`, using only the pivot's own codim `u·M₁`, INDEPENDENT of RHS)? If `∫w^{−c'}<⊤` for `c' < u·M₁/2` and RHS<⊤ forces `c' < u·ρ/2 ≤ u·M₁/2`... we still need the `c'`-extraction.

**Q3.** Is dropping κ (`(w+κ)^{−c'} ≤ w^{−c'}`) SOUND here (it discards the corank charge)? Does it over-estimate LHS to ⊤ in the operative regime? (The DLN header claims dropping the corank `ab/2` shift over-estimates to ⊤ for `c' ∈ (u·ρ/2, minAdm/2 = u·ρ/2+ab/2)` — i.e. dropping κ LOSES the `ab/2` and the pivot-only threshold `u·M₁/2` may be BELOW `c'` even when RHS<⊤. But on the SHELL the pivot threshold is `u·M₁/2`, not `u·ρ/2` — is `u·M₁/2` always `≥ c''+ab/2 = c'` when RHS<⊤? i.e. is `u·M₁/2 ≥ minAdm'/2 + ab/2`? Given `hpiv: minAdm' ≤ u·ρ ≤ u·M₁`, is `u·M₁ ≥ minAdm' + ab`? NOT obviously.) **Resolve whether dropping κ is sound for LHS finiteness on the shell, or whether the corank `ab/2` shift is genuinely needed (⟹ must use S3 ⟹ must handle `c' > ab/2` regime + `c'≤ab/2` regime separately).**

**Q4 (lemma 6 statement).** Given the above, state the PRECISE, MINIMAL new lemma(s) I should isolate and prove (the "pivot-block finiteness / coupled-residual bound"). Give exact Lean-ish signatures. Is it just an instantiation of D-B (construct the linear map `W ↦ W·Q_stack` on the flattened pi type, rank = `u·M₁` on the shell), or does it need the coupling with the corank-peel residual?

Be decisive and concrete. If (A)+drop-κ is sound and avoids S3 entirely, say so (that would drastically simplify). If the corank shift is genuinely needed, give the exact regime split.
