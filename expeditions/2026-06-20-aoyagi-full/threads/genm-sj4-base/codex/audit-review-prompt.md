<task>
Lean 4 / Mathlib formalisation AUDIT. Adjudicate two soundness/vacuity questions about a LANDED
(green, sorry-free) admissibility clause + its consumer base lemma. I have my own read; do NOT assume it.
Reason from the definitions below. Flag any hidden unsoundness or silent vacuity.

SETTING (deep linear networks RLCT descent). A chain is `M : Fin (L+1) → ℕ` (layer widths). The
parameter space `Params M = ∀ s : Fin L, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ` (L layer
matrices). `prod M A = A^(1)·…·A^(L) : Matrix (Fin (M 0)) (Fin (M last)) ℝ`. `dropHead M : Fin (L+1)→ℕ`
of a width-(≥2) chain `M : Fin (L+1+1)→ℕ` is `fun i => M i.succ` (drop first vertex). `paramsBoxM M 1`
is the sup-norm-≤1 product box over the L layers; `matBox a n 1` the sup-norm-≤1 box in `Fin a→Fin n→ℝ`.
`rmatMul X Y = (Matrix.of X) * Y`. `frobSq X = ∑ᵢⱼ (X i j)²`. `minAdm M : ℕ`; at width-2
(`M : Fin 2 → ℕ`) `minAdm M = M 0 * M 1` (proven `minAdm_two_eq`). `axisRatio h k = (h+1)/(2k)`;
`monomialThreshold d k jac = ⨅ⱼ axisRatio (jac j) (k j)`.

The finiteness target: `DecoratedBoxThresholdFinite D := ∀ c':NNReal, (c':ℝ) < minAdm M / 2 →
D.integral c' < ⊤`, where `D.integral c' = ∫_{z∈dom} ∫_{u∈unitBox d}
ofReal((∏ℓ |uℓ|^{jac ℓ}) · (decLoss u z)^{-c'})`, and `decLoss u z = ∑_i (genMonomial supp i u ·
residual (ctx z) i)²` (a sum of squares of generator monomials × linear residuals).

THE BASE CONTRACT (only ever consumed at width-2): `DecoratedBaseHyp adm := ∀ (M : Fin (1+1)→ℕ)
(D : SJDecoration M), adm 1 M D → DecoratedBoxThresholdFinite D`. The recursion driver dispatches
arity `n=0` by a direct `minAdm=0 ⟹ threshold=0 ⟹ vacuous` argument (IGNORING the adm hypothesis),
`n=1` by `DecoratedBaseHyp` (width-2), `n≥2` by a step whose IH is at arity ≥1. So `DecoratedBaseHyp`
is width-2 ONLY.

`adm n M D := genuineCarrier D ∧ (admCorankA M = 0 ∨ admCorankB M = 0 ∨ FaithfulSJAt D)`.
- `genuineCarrier D`: `D.ζ = Unit ∧ ∃ (hν : D.ν = Fin(M 0)×Fin(M last)) (e : D.Z ≃ᵐ Params M),
  MeasurePreserving e ∧ D.dom = e⁻¹'(paramsBoxM M 1) ∧ ∀ z, (hν ▸ (D.ctx z).2) = fun ik ↦
  prod M (e z) ik.1 ik.2`.
- `FaithfulSJAt D`: `(D.d = 0 ∧ ∀ z x u, carrier.loss u z x = ∑ᵥ (x v)²)` OR
  `(1 ≤ D.d ∧ ∃ i₀, α ∧ β ∧ δ0 ∧ gammaPrimeClause D i₀)` where
  α = `∀ j ℓ, supp i₀ ℓ ≤ supp j ℓ` (pSimultaneous),
  β = `(minAdm M : ℝ≥0∞)/2 ≤ monomialThreshold D.d (sharedDivisorExp supp) jac`,
  δ0 = `∀ i ℓ, supp i ℓ = sharedDivisorExp supp ℓ` (uniform support).

THE CLAUSE UNDER AUDIT — `gammaPrimeClause` (units-free, tail-TIED form). Matched on L:
```
gammaPrimeClause : {L}→{M : Fin (L+1)→ℕ}→(D : SJDecoration M)→D.ι→Prop
| 0, _, _, _ => False
| L+1, M, D, i₀ =>
    ∃ (a : ℕ) (eΓ : D.Z ≃ᵐ (Fin a → Fin (M 1) → ℝ) × Params (dropHead M))
      (ρ : D.ι ≃ (Fin a × Fin (M (Fin.last (L+1))))),
      MeasurePreserving eΓ ∧
      D.dom = eΓ⁻¹'(matBox a (M 1) 1 ×ˢ paramsBoxM (dropHead M) 1) ∧
      minAdm M ≤ a * M 1 ∧
      ∀ z i, D.carrier.residual (D.ctx z).1 (D.ctx z).2 i
             = rmatMul (eΓ z).1 (prod (dropHead M) (eΓ z).2) (ρ i).1 (ρ i).2
```
NOTE the tail matrix is HARD-CODED to `prod (dropHead M) (eΓ z).2` — it is NOT an existentially-quantified
free `Z_tail`. `tailProd_width2 : ∀ (M : Fin (1+1)→ℕ) (r : Params (dropHead M)),
prod (dropHead M) r = (1 : Matrix (Fin (M 1)) (Fin (M 1)) ℝ) := rfl` (at width-2 the head-dropped chain
has 0 layers, so the tail product is the empty fold = identity).

BACKGROUND — why the tie exists. An EARLIER untied form (free `Z_tail : R → Matrix (Fin n) (Fin Dt)` with
NO tie) was found UNSOUND: with `M=(1,2)`, `a=1`, `n=Dt=2`, `Z_tail ≡ diag(1,0)` (rank-deficient), the leaf
integral `∫_{matBox} frobSq(Γ·diag(1,0))^{-c'} dΓ` DIVERGES for `1/2 ≤ c' < 1`, so `DecoratedBaseHyp`
would be FALSE. The banked analytic leaf lemma `corankLeaf_rpow_lt_top` requires the tail `Z` to satisfy
`0 < c ∧ (Z·Zᵀ − c•1).PosSemidef` (i.e. Z full-row-rank / `Z Zᵀ ≽ c·1`, c>0), for `c' < a·n/2`;
`diag(1,0)` fails this (`diag(1,0)·diag(1,0)ᵀ − c•1 = diag(1−c,−c)`, not PSD for c>0).

HOW #4 CLOSES the `d≥1` case at width-2 (proven, sorry-free): obtain the gammaPrimeClause data
`⟨a, eΓ, ρ, hmpΓ, hdomΓ, hdim, hprov⟩`; since `prod (dropHead M) = 1` (tailProd_width2), set the tail
`Z := (1 : Matrix (Fin (M 1)) (Fin (M 1)))`, `c := 1`; `hZ : (1·1ᵀ − 1•1).PosSemidef` holds because
`1·1ᵀ − 1•1 = 0` and `(0).PosSemidef`. Derive `decLoss = commonDivisor(u)²·frobSq(rmatMul (eΓ z).1 1)`
from δ0 (uniform support ⟹ leftover monomials =1) + provenance (`residual = (rmatMul (eΓ z).1 1)_{ρ i}`,
ρ a bijection ⟹ ∑ residual² = frobSq (eΓ z).1); Tonelli-split into a finite u-monomial box (via β) times
`∫_{matBox×ˢ Rbox} frobSq((eΓ z).1 · 1)^{-c'}`, bounded by `volume(Rbox)·corankLeaf_rpow_lt_top` with
budget `c' < a·M1/2 ≥ minAdm/2`. `Rbox = paramsBoxM (dropHead M) 1` is a one-point space (0 layers),
volume 1 < ⊤.

QUESTION 1 (deviation soundness — the crux). Given the tail is HARD-CODED to `prod (dropHead M)` (not a
free `Z_tail`), and `tailProd_width2` forces it to the `M1×M1` identity at width-2:
(a) Is the divergent `diag(1,0)` witness genuinely EXCLUDED by this tie? (Can any width-2 decoration
    satisfying the tied clause have a rank-deficient tail?)
(b) Is the identity `Z=1` genuinely full-row-rank enough for `corankLeaf_rpow_lt_top` (does `1·1ᵀ = 1 ≽ 1·1`
    hold, making the leaf integral finite below `a·M1/2`)?
(c) Is the tie OVER-constraining — i.e. could it make the `d≥1` branch of `FaithfulSJAt` VACUOUS at
    width-2 (unsatisfiable), so #4's case (iii) never fires and the "completion" is hollow? Or is a genuine
    width-2 d≥1 decoration still satisfiable?
(d) Consistency: at width-2, `genuineCarrier` forces `D.Z ≃ᵐ Params M` (dimension `M0·M1`), while the tied
    γ' forces `D.Z ≃ᵐ (Fin a→Fin M1→ℝ) × Params(dropHead M)` (dimension `a·M1`, since dropHead has 0 layers
    so Params(dropHead) is a point). The clause only requires `minAdm = M0·M1 ≤ a·M1` i.e. `a ≥ M0`. If
    `a > M0` the two measurable isos would force `M0·M1 = a·M1` — a contradiction. Does this make the
    combined `adm` UNSATISFIABLE for `a>M0` (harmless — #4 vacuously true for those D, and the proof closes
    for ANY a with minAdm≤a·M1), or does it introduce a soundness problem in #4's proof? (The #4 proof does
    NOT assume a=M0; it feeds `corankLeaf_rpow_lt_top` with the actual `a` and budget `a·M1/2`.)

QUESTION 2 (anti-vacuity guard sufficiency). A width-3 witness `witnessDecoration222` on `M=![2,2,2]`
(minAdm=3, both binding coranks =1>0 so the a=0∨b=0 escape does NOT fire, forcing the d≥1 branch) is
proven to satisfy `FaithfulSJAt witnessDecoration222` (its d≥1 branch): d=1, uniform support ≡1, jac=![3],
`Z = (Fin 2→Fin 2→ℝ) × Params(dropHead ![2,2,2])`, `ctx z = ((), fun ik ↦ rmatMul z.1 (prod(dropHead M) z.2) ik)`,
`eΓ = refl`, `ρ = refl`, tail `= prod(dropHead ![2,2,2])` = the genuine single tail layer A^(2) (NON-identity,
z-dependent). β: `axisRatio 3 1 = 2 ≥ 3/2`. This inhabits the tied γ' with a genuine non-identity tail
mid-recursion (where the earlier fixed-single-Z form was vacuous — a fixed matrix cannot equal the varying
layer product).
BUT the witness does NOT prove `genuineCarrier witnessDecoration222` (so the FULL `adm 2 ![2,2,2] D` is not
machine-checked inhabited); the docstring says genuineCarrier is deferred to the peel step (#5).
(a) Is proving `FaithfulSJAt` (the γ' clause specifically) — WITHOUT the genuineCarrier conjunct — a
    SUFFICIENT anti-vacuity guard for the concern "the tied γ' is silently vacuous mid-recursion"?
(b) Does omitting genuineCarrier leave a real hole — i.e. is there any reason `genuineCarrier` would be
    INCOMPATIBLE with this witness's ctx/dom (`ctx z = z.1 · prod(dropHead) z.2`, `dom = matBox 2 2 1 ×ˢ
    paramsBoxM(dropHead) 1`), so that FULL `adm` with d≥1 is actually UNSATISFIABLE at intermediate arity?
    (Consider: does there exist an MP `e : Z ≃ᵐ Params ![2,2,2]` with `prod ![2,2,2] (e z) = z.1 · prod(dropHead) z.2`
    and `e⁻¹'(paramsBoxM M 1) = matBox 2 2 1 ×ˢ paramsBoxM(dropHead) 1`? Params ![2,2,2] = 2 layers = 
    Matrix(Fin2)(Fin2)², and z = (front block, single tail layer).)

<output_contract>
Two sections Q1, Q2. For Q1 answer (a)(b)(c)(d) each in 1-3 sentences with the specific reason (name the
forced value / the failing PSD / the dimension count). For Q2 answer (a)(b). End each section with a
one-word verdict: for Q1 SOUND / UNSOUND (does the tie correctly exclude the divergent witness without
introducing a new hole); for Q2 SUFFICIENT / INSUFFICIENT (is the partial witness an adequate anti-vacuity
guard). If INSUFFICIENT/UNSOUND, give the minimal concrete repair.
</output_contract>

<grounding_rules>
Distinguish FORCED-by-the-stated-definitions from INFERRED. If a step needs a Mathlib lemma, name it or
flag "needs-checking". Do not assume my leaning. Flag if the tie is subtly unsound (still admits a divergent
witness) or subtly vacuous (excludes all genuine d≥1 decorations) rather than merely inconvenient.
</grounding_rules>
</task>
