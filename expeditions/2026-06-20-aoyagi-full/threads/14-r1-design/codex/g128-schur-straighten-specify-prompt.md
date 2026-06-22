<task>
I am a Lean 4 / Mathlib formaliser. I have been handed a LOCKED interface and asked to PROVE a
theorem `schur_straighten_exists` against it. Before sinking proof effort I want a decorrelated
red-team on whether the theorem as stated is PROVABLE, or whether the SPECIFY is defective and the
interface must change.

CONTEXT (Aoyagi-RLCT general-M det-1 Schur straightening "(A) lane"). The intended math is sound and
WITNESSED: at a post-blow-up node the loss core factors, via a det-1 (measure-preserving) transvection
pair L·A·R = blockdiag[1, D − b·a], into a regular smooth block (∑ pivot-row entries²) plus a strictly
smaller matrix-chain zero-core ‖S·Bred‖². That math is NOT in question.

THE LOCKED STRUCTURE (verbatim fields):

  structure IsSchurStraighten {L : ℕ} {N N' : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
      (nReg : ℕ)
      (flatCore : (Fin N → ℝ) → ℝ)
      (flatRedCore : (Fin nReg → ℝ) × ((Fin N' → ℝ)) → ℝ)
      (redEmbed : (Fin N' → ℝ) → Params S.red)
      (χ : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))    -- HOMEOMORPHISM
      (u : (Fin nReg → ℝ) × (Fin N' → ℝ) → ℝ)
      (active : Finset (Fin N')) (p : Fin N') : Prop where
    measurePreserving : MeasurePreserving χ volume volume
    umeas : Measurable u
    redCore_eq : ∀ q, flatRedCore q = (∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2)
    factor : (fun q => flatCore (χ q)) =ᶠ[nhds 0] (fun q => u q * flatRedCore q)
    pivot_active : p ∈ active
    active_nonempty : active.Nonempty
    measure_drops : ∑ s, S.red s < ∑ s, M s

THE THEOREM I AM ASKED TO PROVE (body currently `sorry`):

  theorem schur_straighten_exists {L : ℕ} (M : Fin (L + 1) → ℕ) (S : ChainDimSplit M)
      (nReg N N' : ℕ) (flatCore : (Fin N → ℝ) → ℝ) :
      ∃ (flatRedCore ...) (redEmbed ...) (χ : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ))
        (u ...) (active : Finset (Fin N')) (p : Fin N'),
        IsSchurStraighten M S nReg flatCore flatRedCore redEmbed χ u active p

Note: nReg, N, N', flatCore are ALL universally quantified inputs with NO relating hypothesis.

MY OBSTRUCTION CLAIM (please red-team for correctness, not politeness):
  (O1) Take N' = 0. Then the existential binder `∃ ... (p : Fin N'), ...` = `∃ p : Fin 0, ...`. `Fin 0`
       is empty, so NO witness p exists ⟹ the proposition is FALSE for N'=0. Independently `active : Finset
       (Fin 0)` cannot satisfy `active_nonempty`.
  (O2) The field `χ : ((Fin nReg → ℝ) × (Fin N' → ℝ)) ≃ₜ (Fin N → ℝ)` is a homeomorphism of finite-dim
       real spaces; by topological invariance of domain this forces nReg + N' = N. For inputs with
       nReg + N' ≠ N (e.g. nReg=0,N'=0,N=1) NO such χ exists ⟹ FALSE.
  (O3) Even with dims matched, `redCore_eq` + `factor` force `flatCore ∘ χ` to locally equal
       u·((∑ q.1²) + dlnLoss S.red 0 (redEmbed q.2)). For ARBITRARY flatCore this constrains the germ at 0;
       it is not freely satisfiable (e.g. flatCore ≡ a negative constant cannot equal a unit times a
       nonneg-plus-dlnLoss form that vanishes appropriately) — though u is free-signed so this one is the
       weakest of the three.

CONCLUSION I lean to: the abstract universal statement is UNPROVABLE; the SPECIFY stripped the ties that
the geometric application supplies (nReg + N' = N, and flatCore = dlnLoss M 0 in post-blow-up coords with
a genuine pivot). The fix is to RE-ATTACH hypotheses, NOT to change the structure fields.
</task>

<output_contract>
  1. VERDICT on each of O1, O2, O3: is my obstruction correct? (one line each: CORRECT / WRONG + why).
  2. Overall: is `schur_straighten_exists` as stated provable, or must its STATEMENT change? (PROVABLE /
     DEFECTIVE-SPECIFY).
  3. If DEFECTIVE: the MINIMAL hypothesis set to re-attach to the THEOREM (not the structure) that makes
     it provable while preserving the geometric content. Be concrete about: the dim tie, the flatCore tie,
     and the N'>0 / active nonempty tie. State whether the structure `IsSchurStraighten` itself needs any
     change or whether re-hypothesising the theorem suffices.
  4. Flag any obstruction I MISSED.
  Keep it under ~400 words. Mark inference vs. fact.
</output_contract>

<grounding_rules>
  Treat the Lean type theory as fact (Fin 0 empty, homeomorphism dimension invariance). You may not assume
  any hidden hypothesis I did not state. If you assert a Mathlib lemma name, mark it as "recall — verify".
</grounding_rules>
