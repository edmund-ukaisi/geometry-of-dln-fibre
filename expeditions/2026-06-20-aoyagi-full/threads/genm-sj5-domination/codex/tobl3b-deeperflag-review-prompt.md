# Decorrelated audit: is a Lean domination lemma (L1) faithful/non-circular, and is an isolated `sorry` (S1) a correct non-vacuous statement?

You are an independent adversarial reviewer of a Lean 4 / Mathlib formalisation. I give you the EXACT
definitions and statements (transcribed verbatim). Adjudicate two questions DECISIVELY, either direction.
I have WITHHELD my own conclusions. Reason from the definitions; distinguish fact from inference.

## Background objects (verbatim-transcribed Lean)

`SJDecoration M` is a structure with fields `d : ℕ`, `jac : Fin d → ℕ`, `Z : Type`, `dom : Set Z`,
a measure on `Z`, a "carrier" and a `ctx`. Two derived defs:

```
SJDecoration.decLoss (D) (u : Fin D.d → ℝ) (z : D.Z) : ℝ := D.carrier.loss u (D.ctx z).1 (D.ctx z).2

SJDecoration.integral (D) (c' : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in D.dom, ∫⁻ u in unitBox D.d,
    ENNReal.ofReal ((∏ ℓ, |u ℓ| ^ (D.jac ℓ)) * (D.decLoss u z) ^ (-c'))
```

`cornerComparator M' k jc : SJDecoration M'` has `d := d`, `jac := jc`, `Z := Params M'`,
`dom := paramsBoxM M' 1`, uniform support `≡ k`, identity-selection carrier reading `prod M'`. A PROVED
theorem: `cornerComparator_decLoss`: `(cornerComparator M' k jc).decLoss u z = commonDivisor(supp)(u)^2 * frobSq (prod M' z)`.

A PROVED brick `shell_corankOffSector_le_unif` (sorry-free), the analytic core: for `Z : M₂×n`,
`U_s : M₂×m` with `U_sᵀU_s=1`, `b ≤ m ≤ M₂`, `m ≤ Z.rank`, `ε>0`, shell PSD `Z Zᵀ ⪰ ε²·U_s U_sᵀ`,
convergence `a < m − b + 1`, and `ab/2 < c'`:
```
∀ w > 0,  ∫_{A_cor ∈ matBox b M₂ 1} ∫_{Γ ∈ sΓ} (w + frobSq(Ccross + Γ·(A_cor·Z)))^{−c'}
            ≤ Cunif · w^{−(c' − ab/2)}
```
with `Cunif = deeperFlagUnifConst … ε c'`, PROVED `< ⊤` in the convergent regime `a < m−b+1`. `sΓ` arbitrary.

## Object under audit #1 — the LHS def of L1

```
deeperFlagCoreIntegrand M u k jc Zf Ccrossf sΓf c' : ℝ≥0∞ :=
  ∫⁻ z in paramsBoxM (redChain u M) 1, ∫⁻ v in unitBox d,
    ENNReal.ofReal (∏ ℓ, |v ℓ| ^ (jc ℓ))
      * (∫⁻ A_cor in matBox (M 1 - u) M₂ 1, ∫⁻ Γ in sΓf z,
          ENNReal.ofReal (((cornerComparator (redChain u M) k jc).decLoss v z
              + frobSq (Ccrossf z + Γ·(A_cor·Zf z))) ^ (−c')))
```
Note the pivot energy `w` inside the inner integral is SET to `(cornerComparator (redChain u M) k jc).decLoss v z`.

## Statement under audit #1 — L1 (PROVED sorry-free)

`deeperFlag_shell_core_le`: given `hUs (U_sf z)ᵀU_sf z = 1`, `hbm : M1−u ≤ m`, `hmM : m ≤ M₂`,
`hmZ : ∀z, m ≤ (Zf z).rank`, `hshell : ∀z, (Zf z (Zf z)ᵀ − ε²·U_sf z (U_sf z)ᵀ).PosSemidef`,
`hconv : (M0−u) < m − (M1−u) + 1`, `hc' : (M0−u)(M1−u)/2 < c'`, and
`hpos : ∀ᵐ z ∈ paramsBoxM…, ∀ᵐ v ∈ unitBox d, 0 < (cornerComparator (redChain u M) k jc).decLoss v z`:
```
∃ C < ⊤,  deeperFlagCoreIntegrand M u k jc Zf Ccrossf sΓf c'
            ≤ C * (cornerComparator (redChain u M) k jc).integral (c' − peelCharge M u / 2)
```
The proof: pointwise-a.e. in (z,v), apply `shell_corankOffSector_le_unif` at `w = decLoss v z > 0` (via
`hpos`), then integrate; the RHS `.integral` matches the collapsed `∫_z ∫_v ofReal((∏|v_ℓ|^{jc_ℓ})·(decLoss v z)^{−e})`
DEFINITIONALLY (the final step is `le_refl`).

**Q1 (faithfulness / non-circularity of L1).** Is `deeperFlagCoreIntegrand` a GENUINE representation of the
"off-sector-core" integrand that `shell_corankOffSector_le_unif` bounds (inner double integral over `A_cor,Γ`
of `(w + frobSq(...))^{−c'}` with `w` a real pivot energy), OR is it GERRYMANDERED so that L1 says nothing
(e.g. the LHS is definitionally the RHS, making L1 a vacuous `rfl`)? Consider: the LHS inner integrand is
`(decLoss + frobSq(Ccross+Γ(A_cor Z)))^{−c'}` (an `A_cor,Γ` double integral), the RHS integrand is
`(decLoss)^{−e}` with `e = c' − ab/2` (NO `A_cor,Γ`). Are these genuinely different objects with real analytic
content between them (the freed-corner peel + PSD weak-elimination + strong-block finiteness)? Is setting
`w := decLoss` legitimate given `cornerComparator_decLoss` says `decLoss = commonDivisor(v)²·frobSq(prod)`? Is
`∃ C < ⊤` a real finite constant (not the vacuous `C = ⊤`)?

**Q2 (`hpos` honesty).** `hpos` restricts the pointwise bound to `{decLoss v z > 0}`. Given
`decLoss v z = commonDivisor(v)²·frobSq(prod(redChain u M) z)`, is `{decLoss = 0}` a genuine NULL set (so `hpos`
is an honest a.e. side-condition dischargeable from product-nonvanishing + exceptional monomial), or does `hpos`
smuggle the hard part of the conclusion?

## Statement under audit #2 — S1 (an isolated `sorry`, statement only)

`deeperFlag_spineToCore`: for `M : Fin (L+3) → ℕ`, `t j : ℕ`, `κ : Fin (t+j) ↪ Fin (M 1)`, `ε>0`, `c'`,
`ht : t ≤ min (M0) (M1)`, `hj : j ≤ min (M0−t) (M1−t)`:
```
∃ (M₂ m n d : ℕ) (k jc : Fin d → ℕ) (Zf, Ccrossf, U_sf, sΓf functions of z ∈ Params (redChain (t+j) M)) (i₀),
  (∀z, (U_sf z)ᵀ U_sf z = 1) ∧ (M1−(t+j) ≤ m) ∧ (m ≤ M₂) ∧ (∀z, m ≤ (Zf z).rank)
  ∧ (∀z, (Zf z (Zf z)ᵀ − ε²·U_sf z (U_sf z)ᵀ).PosSemidef)
  ∧ ((M0−(t+j)) < m − (M1−(t+j)) + 1)                          -- hconv, strict convergence
  ∧ (∀ᵐ z, ∀ᵐ v, 0 < (cornerComparator (redChain (t+j) M) k jc).decLoss v z)   -- hpos
  ∧ (1 ≤ d) ∧ ((minAdm (redChain (t+j) M))/2 ≤ monomialThreshold d k jc)         -- hd, hbeta
  ∧ shellSpineIntegrand M (t+j) κ ε (min (M0−t)(M1−t)) ⟨j,_⟩ c'
      ≤ deeperFlagCoreIntegrand M (t+j) k jc Zf Ccrossf sΓf c'                    -- hle
```
`shellSpineIntegrand M u κ ε r jf c'` is a FIXED object: the freed-Γ triple integral
`∫_{A' ∈ box ∩ {prod(tailChain M) A' ∈ singularShell ε r jf}} ∫_{x∈outerDom u (M0−u)(M1−u) 1}
∫_{Γ | Γ+schurShift x ∈ genBox} (freedSchurLoss x Γ ((prod(tailChain M) A').submatrix (blockSplitEquiv κ) id))^{−c'}`.
`M₂, m, n, d, k, jc, Zf, Ccrossf, U_sf, sΓf` are all EXISTENTIALLY chosen. `shellSpineIntegrand` (the LHS) is
NOT existential — it's pinned by `M, t, j, κ, ε, c'`.

**Q3 (S1 non-vacuity + could-it-be-a-false-statement).** (a) Could this ∃-statement be satisfied VACUOUSLY —
e.g. by choosing `sΓf`, `Zf` degenerate so that `deeperFlagCoreIntegrand = ⊤`, making `hle` trivial? KEY
CONSTRAINT: L1 (Q1, PROVED) shows that WHENEVER the L1-hyps hold (`hUs..hconv,hpos` — which are exactly S1's
constraints), `deeperFlagCoreIntegrand ≤ C·comparator.integral(e)` with `C < ⊤`. Does this FORCE the RHS finite
(hence `hle` a genuine finite domination) whenever S1's `hconv` etc. hold — i.e. is the "degenerate RHS = ⊤"
escape BLOCKED by L1? (b) Could S1's constraints be jointly CONTRADICTORY (∃ over an empty type / false premise),
making S1 a FALSE statement that a `sorry` would wrongly "prove"? Check especially: is `hconv` (strict
convergence) jointly satisfiable with `hbm, hmM` and the shell PSD/rank conditions — given `M₂, m, n` are FREE
to choose? (c) Are the constraints `ht/hj` the right binding-cut structure, or is S1 stated over a range broader
than any convergent mechanism could cover (e.g. `j=0` with `M0−(t+j) = M₂ − (M1−(t+j)) + 1` exact, forcing
`m > M₂` against `m ≤ M₂` for the REAL deep width M₂)? Does the existential freedom over `M₂, m` rescue the
edge cases, or is there a concrete `(t,j)` where S1 is provably false?

Answer Q1–Q3 crisply. For each: VERDICT (faithful/vacuous/false/sound) + the one-line reason. If you find a
concrete counterexample making S1 false, state it exactly.
