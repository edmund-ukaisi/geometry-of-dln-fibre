You are a decorrelated reviewer auditing a Lean 4 measure-theory re-architecture for SOUNDNESS. Be adversarial;
try to find an unsound step or a hidden hypothesis. Independent verdict; do not ask for mine.

BACKGROUND. A prior route bounded a shell integrand by a "front-charge box" that turned out to be +∞ at EDGE
cells (a+b = ρ+1), making the per-cell finiteness hypothesis UNFILLABLE there. The fix re-wires the interior to
a "coupled box" that is finite at every rank sector. All integrals are Lebesgue ℝ≥0∞ integrals (nonneg).

The interior branch of the assembly skeleton is now:
  shellSpineIntegrand ... ≤[shellSpine_le_coupledBox]  ∫_box coupledBoxIntegrand  <[coupledBox_lt_top_of_cells]  ⊤

STEP 1 — `shellSpine_le_coupledBox (M) (t j) (κ) (ε c') (hj : j ≤ r)` :
    shellSpineIntegrand M (t+j) κ ε r ⟨j,_⟩ c'  ≤  ∫⁻ p in (paramsBoxM (redChain (t+j) M) 1 ×ˢ matBox (M1-(t+j)) M2 1), coupledBoxIntegrand M (t+j) c' p
  Proof: unfold shellSpineIntegrand (an integral over `paramsBoxM(tailChain M) 1 ∩ {A' | prod ∈ singularShell …}`
  of an inner (x,Γ) double integral); then
    (a) `lintegral_mono_set Set.inter_subset_left`  — enlarge the domain from (box ∩ shell) to box (drop the shell indicator);
    (b) `lintegral_congr hval` — rewrite the inner integrand to `coupledBoxIntegrand ∘ (hsSplit M (t+j) κ)` via an integrand identity;
    (c) transport `∫ over paramsBoxM(tailChain M)1` to `∫ over paramsBoxM(redChain (t+j) M)1 ×ˢ matBox …` via
        `(measurePreserving_hsSplit …).setLIntegral_comp_preimage_emb` (measure-preserving equiv) + `hsSplit_preimage_box`.
  It takes ONLY `hj : j ≤ r` — no charge bound, no binding-cut, no genericity hypothesis.

STEP 2 — `coupledBox_lt_top_of_cells (M) (u) (c') (hcell : ∀ i : CRIndex(dropHead(redChain u M)), ∫_(box ∩ projDeep⁻¹' dcell i) coupledBoxIntegrand < ⊤)`
      : ∫_box coupledBoxIntegrand < ⊤.
  Proof: `lintegral_lt_top_of_finite_cover (fun i => box ∩ projDeep⁻¹' dcell i) box coupledBoxIntegrand hunion hcell`,
  where `hunion : (⋃ i, box ∩ projDeep⁻¹' dcell i) = box`, proven by `⋃ i dcell i = {A | rank(prod) ≤ dropHead 0}`
  (`deepRankLE_eq_iUnion_cells`) and `deepFactor_rank_le_rows` (every p's deep factor has rank ≤ rows ⟹ preimage union = univ).
  CRIndex is a FINITE index type (finitely many rank cells).

CAPSTONE CONTEXT (faithfulness). The ∀-M capstone `routeMBoxThresholdFinite_coupled` takes an ABSTRACT hypothesis
  hcoupled : ∀{L}(M:Fin(L+3)→ℕ)(t), (∀i,1≤M i) → NondegBindingCut M t → (∀M':Fin(L+2)→ℕ,RMBTF M') → RMBTF M
and proves `∀{L}(M:Fin(L+1)→ℕ), RMBTF M`. The interior theorems above are NOT called by the capstone; they are the
intended DISCHARGE of the `hcoupled` hole. The re-arch changed only the interior theorems + a hypothesis rename
(hfin→hcell, integrand frontChargeIntegrand→coupledBoxIntegrand); the capstone's statement and proof term are
byte-identical to before.

QUESTIONS (answer each precisely):
1. Step 1(a): is `∫_{box ∩ shell} f ≤ ∫_box f` (enlarging the domain, f : ℝ≥0∞ nonneg) UNCONDITIONALLY valid?
   Does dropping the shell restriction lose soundness (vs merely looseness)? Could it hide a needed hypothesis?
2. Step 1 overall: is a domination `shellSpine ≤ ∫coupledBox` proven via [a-fortiori domain enlargement + measure-
   preserving transport (equality)] a SOUND ≤ with NO hidden hypothesis beyond `j ≤ r`? Any way this ≤ is false?
3. Step 2: does `lintegral_lt_top_of_finite_cover` soundly conclude `∫_box f < ⊤` from (i) a FINITE cover whose
   union is box and (ii) each piece-integral finite? Does the cover need to be DISJOINT, or does overlap (double-
   counting) stay sound for an UPPER finiteness bound? Is "union = box" (no cell dropped) the only real requirement?
   Is the cover-completeness argument (every p lands in some rank cell via rank ≤ rows) valid?
3b. VACUITY: `hcell` asserts `∫ coupledBoxIntegrand over a cell < ⊤`. coupledBoxIntegrand = ∫_x ∫_Γ (freedSchurLoss)^(−c').
   Is this a genuine (non-trivial, fillable) finiteness obligation, or could it be trivially ⊤ (unfillable) or trivially
   finite (vacuous)? (Given the whole point of the re-arch is that coupledBox is finite per-cell where frontCharge was +∞.)
4. Capstone faithfulness: if the interior theorems change but the capstone takes `hcoupled` as an abstract hypothesis
   and its proof term is unchanged, does the capstone STILL STAND unchanged and remain a faithful ∀-M conditional?
   Is there any way the interior re-arch could silently invalidate or weaken the capstone?
