<task>
Lean 4 + Mathlib v4.29 formalisation. I must prove one lemma, `normalSlice_transfer`, the crux of a
"front-peel" recursion for a deep-linear-network RLCT box-integral. The MATH is fully settled and
verified (I paste the certificate below); I need your independent judgement on the MINIMAL LEAN LEMMA
DECOMPOSITION and which sub-pieces are genuinely reachable vs. dependent-width "walls".

CONTEXT (Lean objects, all banked/defined):
- `Params (H : Fin (n+1) → ℕ)` = `∀ s : Fin n, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ` (a
  composable matrix tuple; H are the layer widths).
- `prod H A : Matrix (Fin (H 0)) (Fin (H (Fin.last n))) ℝ` = A₀·A₁···A_{n-1} (left fold `prodAux`).
- `frobSq (M : a→b→ℝ) = ∑ᵢⱼ Mᵢⱼ²`; `rmatMul` = matrix mult in function form.
- `matBox p n T`, `paramsBoxM H T` = entrywise [-T,T] boxes; `routeMLayerBoxIntegral M c' 1` =
  `∫_{A∈paramsBoxM M 1} frobSq(prod M A)^(-c')` (an `ℝ≥0∞` lintegral).
- `tailChain M i = M i.succ` (drop head); `minAdm M : ℕ` (a codimension); `tailMin M` = min tail width.
- `RouteMBoxThresholdFinite M := ∀ c':NNReal, c' < minAdm M/2 → routeMLayerBoxIntegral M c' 1 < ⊤`.
- I have PROVED: `outerRankCover` (box ≤ ∑_{q≤tailMin} frontStratumIntegral M q c') and
  `shiftedThreshold` (c' < minAdm M/2, q≤tailMin ⟹ c'-M₀q/2 < minAdm(reduced)/2).
- `frontStratumIntegral M q c' := ∫_{A'∈paramsBoxM(tailChain M)1 ∩ {rank(prod(tailChain M)A')=q}}
    ∫_{A0∈matBox(M 0)(M 1)1} ofReal(frobSq(rmatMul A0 (prod(tailChain M)A'))^(-c'))`.

THE LEMMA TO PROVE:
  normalSlice_transfer (M : Fin(L+1+1+1)→ℕ) (q) (hq : q ≤ tailMin M) (c' : NNReal)
    (hc' : c' < minAdm M/2)
    (hIH : RouteMBoxThresholdFinite (fun i:Fin(L+1+1) => M i.succ - q)) :
    frontStratumIntegral M q c' < ⊤

CERTIFICATE (settled math, verified exact L≤4, Codex-decorrelated):
On {rank P = q} (P = tail product, widths (M₁..M_L)), block each factor X_i by q+(m_i-q) rows/cols
X_i=[[A_i,B_i],[C_i,D_i]] (A_i is q×q). Thread right-to-left, K_L=0:
  α_i = A_i + B_i K_{i+1};  γ_i = C_i + D_i K_{i+1};  K_i = γ_i α_i⁻¹;  Y_i = D_i − γ_i α_i⁻¹ B_i.
With M_i=[[I,0],[−K_i,I]] (det 1): M_i·X_i·M_{i+1}⁻¹ = [[α_i,B_i],[0,Y_i]] (block upper-tri).
Telescoping: M_1·P = [[α_1···α_{L-1}, *],[0, Y_1···Y_{L-1}]]. On the chart where every α_i is
invertible: rank P = q + rank(Y_1···Y_{L-1}), so {rank P ≤ q} ⟺ {Y_1···Y_{L-1}=0} = Σ⁰ of the reduced
chain (M₁−q,…,M_L−q). Jacobian ±1 (α_i⁻¹ only as unit coefficients — no det-inverse). The A₀-loss splits
frobSq(A₀·P) ≃ ‖R‖²+‖Z‖² (R:M₀×q from A₀, Z=reduced product), DISJOINT variable blocks ⟹ RLCTs ADD:
½M₀q + ½minAdm(reduced) = ½frontCharge(q). FINITENESS is BANKED: radial_morse_residual_power_le
(exponent shift c'↦c'-½·blockdim), lintegral_eq_polar (corner blow-up), matBox_corank_dominates/residual
(the M₀q Morse block, regimes c'≷M₀q/2), sumSqND_box_lt_top; the reduced-chain box finiteness is hIH.
The CoV needs every α_i invertible → a FINITE PIVOT-CHART COVER (banked pivotLocus_eq_iUnion +
pivotChartCover_matBox_le_sum). The L=2 single-matrix Schur block split is banked as
frobSq_schur_block_split. Opaque-width dependent-Fin casts are the known friction (matrix-apply simp
fails in-context; work in Pi form, per-entry haves at ⟨_,by decide⟩ indices, mul_three_reassoc for
reassociation; ⅟→⁻¹ via invOf_eq_nonsing_inv; measurePreserving_shearSub for det-1 shears).
</task>

<output_contract>
1. THE LEMMA DAG: list the minimal set of intermediate Lean lemmas/definitions to prove
   normalSlice_transfer, in dependency order. For EACH: a one-line Lean-shaped statement sketch, and a
   tag [REACHABLE | HARD-opaque-width | BANKED-reuse].
2. ENTRY POINT: the single sub-lemma to attempt FIRST (max learning / de-risk), and why.
3. WALLS: which sub-pieces are the genuine dependent-width risk, and the concrete Lean tactic pattern
   most likely to get through each (be specific about the cast handling).
4. SIMPLIFICATIONS: any way to AVOID defining the full threaded α/K/Y recursion as Lean functions
   (e.g. an existence-only "∃ unit-triangular U,V: U·P·V = blockdiag" statement that skips the explicit
   thread), if it still delivers rank P = q + rank(reduced) and the loss split. Rank the tradeoff.
5. Flag anything in the certificate that looks Lean-infeasible or that you'd restate differently.
Be concrete and terse. Assume expert Lean/Mathlib knowledge.
</output_contract>

<grounding_rules>
Distinguish (a) what Mathlib v4.29 provably has (name the lemma if you're confident) from (b) your
inference about what "should" exist. Flag any lemma name you're not sure exists as UNVERIFIED. Do not
invent Mathlib API. The math is settled — do NOT re-derive it; focus only on the Lean decomposition.
</grounding_rules>
