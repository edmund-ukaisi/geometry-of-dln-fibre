<task>
Lean 4 + Mathlib v4.29 formalisation scope/architecture decision. I am building the L=2 case of an
"achiever box-divergence" atom for the RLCT lower bound of deep linear networks.

SETTING (concrete):
- `Params M = ∀ s : Fin 2, Matrix (Fin (M s.castSucc)) (Fin (M s.succ)) ℝ` for `M : Fin 3 → ℕ`
  (two layers A : M0×M1, C : M1×M2). `dlnLoss M 0 A = ‖A·C‖²_Frobenius = Σᵢⱼ (A·C)ᵢⱼ²`.
- `flatDim M = M0·M1 + M1·M2`; `paramsEquivFlat M : Params M ≃ᵐ (Fin (flatDim M) → ℝ)` (measure-preserving
  homeo; per-entry value is `rfl`). `routeMCore M x = dlnLoss M 0 ((paramsEquivFlat M).symm x)`.
- `minAdm M` for L=2 = `min over t∈[0,min(M0,M1)] of (M0−t)(M1−t)+t·M2`. For (3,3,4): minAdm=8 at t=1.
- TARGET atom (general M : Fin (L+1)→ℕ): `∫⁻_{cubeBox (flatDim M) ε} |routeMCore M|^{−c'} = ⊤`
  for `c' ≥ ½·minAdm M`, every ε>0.

THE CONSTRUCTION (verified EXACT in sympy, for arbitrary (M0,M1,M2) and achiever rank t):
A single weighted radial blow-up φ (= `pivotBlowupOn active pivot`, an existing gated Mathlib-backed map:
pivot p ↦ x_p; active j≠p ↦ x_p·x_j; spectators fixed; `det Dφ = x_p^{card(active)−1}`).
Choose: A = [identity t×t pivot block; (M0−t)×(M1−t) residual block = u·Dbar; cross strips = 0];
C = [top t rows = u·Tbar with Tbar[0,0]=u the PIVOT; bottom (M1−t) rows = S generic].
Then the product P = A·C = u·[[Tbar],[Dbar·S]] EXACTLY, so F = ‖P‖² = u²·U with U = ‖Tbar‖²+‖Dbar·S‖²,
U is EXACTLY u-free (F is pure degree 2 in u), and U = Σ(P[i,j]/u)² with P[0,0]/u = 1, so U ≥ 1 unconditionally.
active = {all Dbar entries}∪{all Tbar entries}, card = (M0−t)(M1−t)+t·M2 = minAdm, pivot∈active,
so det = u^{minAdm−1}. Binding axis (k,h)=(1,minAdm−1), threshold minAdm/2. At c'=½·minAdm the exponent is −1.
This feeds the EXISTING leaf atom `monomialIntegrand_lintegral_box_eq_top` (the sharp ∫u^{−1}=⊤).

I have the full (2,2,2) template `routeM222_box_diverges` (a 3-step composite chart phiUnit) to mirror;
the L=2 single blow-up is structurally SIMPLER (one pivotBlowupOn, no Lemma-2 splice, no gauge chain).

THE DECISION: ship the CONCRETE (3,3,4) lemma fully sorry-free (binding corank-2 anchor, the headline
obstruction), OR attempt the GENERAL (M0,M1,M2) lemma with symbolic minAdm/achiever-t/abstract active-set.
The brief wants "a standalone L=2 lemma for M : Fin 3 → ℕ that plugs into the general atom via cases L",
but also offers (3,3,4) as "the simplest first target" and Codex previously recommended (3,3,4) first.

KEY COST DRIVERS for general (M0,M1,M2):
- The achiever rank t is a `minAdm`-minimizer over a Finset.range — extracting it generically + proving
  card(active)=minAdm requires reasoning about an opaque minimizer.
- The matrix-product algebra `A·C = u·[stack]` over ARBITRARY dims (not `decide`-able; needs Matrix.mul
  manipulation, Frobenius = double sum).
- The flat-coordinate enumeration: active ⊆ Fin(flatDim M) via `Fintype.equivFin (FlatIdx M)` (OPAQUE).
- Matching the general-`d=flatDim M` monomial exponent vectors (k,h) to monomialIntegrand's shape.
- (3,3,4) lets `decide`/`fin_cases`/explicit `![...]` carry the enumeration + det card + algebra.
</task>

<output_contract>
1. VERDICT (2-3 sentences): concrete-(3,3,4) first, or push straight to general-(M0,M1,M2)? Given a single
   tide's budget and "never leave the build broken / stop on thrash" discipline.
2. If (3,3,4): the cleanest module skeleton — list the ~8-12 sub-lemmas in dependency order (factorization,
   det, c-o-v, image-subset, leaf-integrand, box-divergence), each one line, flagging which are `decide`/
   `ring`/`fin_cases`-cheap vs which carry real proof weight. Identify the single most likely-to-wall step.
3. The TWO soundness traps to NOT get wrong (the U≤C-for-lower-bound direction is one I already know from
   the prior consult — name the OTHER one specific to a single-blow-up vs the (2,2,2) composite).
4. For the general lift (if deferred): the ONE structural lemma that, once banked, makes (M0,M1,M2)
   mechanical — i.e. what to factor out of the (3,3,4) proof so the general case is a re-instantiation.
</output_contract>

<grounding_rules>
Flag inference vs fact. You do NOT have the Lean source; reason from the API shapes I gave. If a Mathlib
lemma name you cite is uncertain, say so — I will verify before use. Do not invent that a step is cheap if
the dependent-matrix/opaque-equivFin structure makes it expensive; that asymmetry is the crux of the decision.
</grounding_rules>
