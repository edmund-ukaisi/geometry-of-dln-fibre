import DLNFibre.DLN.RLCT.Validate.RouteMSJDecoratedStep
import DLNFibre.DLN.RLCT.Validate.RouteMSchurRectCapB
import DLNFibre.DLN.RLCT.Validate.RouteMSJWaistReversalCoV

set_option linter.style.longLine false

/-!
# `DLNFibre.DLN.RLCT.Validate.RouteMSJWaistConnector` — hole (c) `deeperFlagWaist_finite` connector

**Thread `genm-sj5-waist` (aoyagi-full Stage 2), the (c) fill (waistdec).** The WAIST-branch decorated
finiteness, reduced to the BARE box `RouteMBoxThresholdFinite M` (the shared decoration→bare-box
reduction `hred` — regime-agnostic, shared with hole (d), extracted at rendezvous from
`deeperFlagGood_finite_impl`) followed by a bare-box discharge that splits on chain arity:

* **`L = 0` (3-width, e.g. the palindrome `(3,2,3)`)** — `routeMBoxThresholdFinite_mnp` DIRECTLY (the
  3-width box is finite below `½·minAdm` for ALL triples, waists included — rectangular-Schur recursion,
  no SVD). A 3-width waist can reverse to another 3-width waist (`(3,2,5) ↦ (5,2,3)`), so reversal does
  NOT orient it; the 3-width mnp base is exactly the fixpoint of the recursion.
* **`L ≥ 1` (`≥ 4`-width)** — REORIENTATION. Every `≥ 4`-width waist `M` reverses to a GOOD chain
  (`deepTailMin_rev_le_of_waist`: `M₁ < M_{last−1} = (rev M)₁` and `min(M₀,…,M_{last−1}) ≤ M₁`, so
  `deepTailMin (rev M) ≤ (rev M)₁`), so the good-case machinery `deeperFlagGood_finite (rev M)` (on the
  TRIVIAL decoration — Γ-free, `genuineCarrier` via `e = id`) delivers
  `RouteMBoxThresholdFinite (rev M)` (via `decoratedBoxThresholdFinite_trivial_iff`), and the reversal
  brick `routeMBoxThresholdFinite_of_rev` transfers it to `M`.

**Γ-consume soundness.** No Γ-carrying decoration is ever handed to `hIH`: the Γ block is consumed into
the bare-box front factor by `hred` (the shared reduction, exactly as `deeperFlagGood_finite_impl`), and
the only `hIH` consumer downstream is `deeperFlagGood_finite (rev M)` called on the TRIVIAL decoration.
Well-founded: `(c)(M) → (d)(rev M)` is SAME arity (`L + 2`), and both take the SAME strong one-arity-lower
IH `hIH` (rev M has the same ambient `L`), so `hIH_M = hIH_{rev M}`; no `(d) → (c)` back-edge (no cycle).

`deeperFlagWaist_finite_impl` takes `hred` (O1 shared reduction) as a hypothesis and calls the skeleton's
`deeperFlagGood_finite` (a hole on the crux lane) — both auto-close at rendezvous when the shared lemma
is extracted and the crux lands. UNTRACKED, NOT wired into `DLNFibre.lean`/`AxCheck`.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- **Every `≥ 4`-width waist reverses to a GOOD chain.** For `M : Fin (L+1+1+1+1) → ℕ` in the waist
regime `M 1 < deepTailMin M`, the reversed chain `M ∘ Fin.rev` is good: `deepTailMin (M ∘ Fin.rev) ≤
(M ∘ Fin.rev) 1`. Proof: `(M ∘ Fin.rev) 1 = M ⟨L+2⟩` (`Fin.rev 1`); `deepTailMin (M ∘ Fin.rev) ≤ M 1`
(the `M 1` term sits at reversed-index `⟨L⟩` of the tail min-set `{M 0,…,M_{L+1}}`); and `M 1 <
deepTailMin M ≤ M ⟨L+2⟩` (waist + `M ⟨L+2⟩` in `M`'s tail min-set). So `deepTailMin (M ∘ Fin.rev) ≤
M 1 < (M ∘ Fin.rev) 1`. -/
theorem deepTailMin_rev_le_of_waist {L : ℕ} (M : Fin (L + 1 + 1 + 1 + 1) → ℕ)
    (hwaist : M 1 < deepTailMin M) :
    deepTailMin (M ∘ Fin.rev) ≤ (M ∘ Fin.rev) 1 := by
  -- `(M ∘ Fin.rev) 1 = M ⟨L+2⟩`.
  have hrev1 : (M ∘ Fin.rev) 1 = M ⟨L + 2, by omega⟩ := by
    have h : Fin.rev (1 : Fin (L + 1 + 1 + 1 + 1)) = ⟨L + 2, by omega⟩ := by
      apply Fin.ext; simp only [Fin.val_rev, Fin.val_one]; omega
    simp only [Function.comp_apply, h]
  -- Step A: `deepTailMin (M ∘ Fin.rev) ≤ M 1`, via `inf'_le` at `i = ⟨L⟩ : Fin (L+2)`.
  have hvalA : (M ∘ Fin.rev) ((⟨L, by omega⟩ : Fin (L + 1 + 1)).succ.succ) = M 1 := by
    have h : Fin.rev ((⟨L, by omega⟩ : Fin (L + 1 + 1)).succ.succ)
        = (1 : Fin (L + 1 + 1 + 1 + 1)) := by
      apply Fin.ext; simp only [Fin.val_rev, Fin.val_succ, Fin.val_one]; omega
    simp only [Function.comp_apply, h]
  have hstepA : deepTailMin (M ∘ Fin.rev) ≤ M 1 := by
    have key : deepTailMin (M ∘ Fin.rev)
        ≤ (M ∘ Fin.rev) ((⟨L, by omega⟩ : Fin (L + 1 + 1)).succ.succ) :=
      Finset.inf'_le (f := fun i : Fin (L + 1 + 1) => (M ∘ Fin.rev) i.succ.succ)
        (Finset.mem_univ _)
    rwa [hvalA] at key
  -- Step B: `M 1 < M ⟨L+2⟩`, from waist + `deepTailMin M ≤ M ⟨L+2⟩` (`inf'_le` at `j = ⟨L⟩`).
  have hvalB : M ((⟨L, by omega⟩ : Fin (L + 1 + 1)).succ.succ) = M ⟨L + 2, by omega⟩ := by
    have h : (⟨L, by omega⟩ : Fin (L + 1 + 1)).succ.succ
        = (⟨L + 2, by omega⟩ : Fin (L + 1 + 1 + 1 + 1)) := by
      apply Fin.ext; simp only [Fin.val_succ]
    rw [h]
  have hstepB : M 1 < M ⟨L + 2, by omega⟩ := by
    have key : deepTailMin M ≤ M ((⟨L, by omega⟩ : Fin (L + 1 + 1)).succ.succ) :=
      Finset.inf'_le (f := fun i : Fin (L + 1 + 1) => M i.succ.succ) (Finset.mem_univ _)
    rw [hvalB] at key
    exact lt_of_lt_of_le hwaist key
  rw [hrev1]
  exact le_trans hstepA (le_of_lt hstepB)

/-- **HOLE (c) — the waist branch `deeperFlagWaist_finite`, filled modulo the shared reduction `hred`.**
For a `≥ 3`-width chain `M` in the waist regime with `M 1 ≠ 1` and the decorated strong IH `hIH`, every
`adm`-admissible `D` is finite below `carrierThreshold M`. Reduces (via the shared decoration→bare-box
`hred`) to `RouteMBoxThresholdFinite M`, discharged by `routeMBoxThresholdFinite_mnp` (3-width) or by
reorientation to the good `rev M` (`≥ 4`-width). The signature mirrors the skeleton's
`deeperFlagWaist_finite` plus the `hred` hypothesis (O1, supplied at rendezvous). -/
theorem deeperFlagWaist_finite_impl {L : ℕ}
    (M : Fin (L + 1 + 1 + 1) → ℕ) (D : SJDecoration M)
    (hD : adm (L + 1 + 1) M D)
    (hwaist : M 1 < deepTailMin M)
    (hM1 : M 1 ≠ 1)
    (hIH : ∀ (M' : Fin (L + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (L + 1) M' D' → DecoratedBoxThresholdFinite D')
    (hred : ∀ {K : ℕ} (M' : Fin (K + 1 + 1 + 1) → ℕ) (D' : SJDecoration M'),
        adm (K + 1 + 1) M' D' → RouteMBoxThresholdFinite M' → DecoratedBoxThresholdFinite D') :
    DecoratedBoxThresholdFinite D := by
  refine hred M D hD ?_
  -- goal: `RouteMBoxThresholdFinite M`
  rcases L with _ | L'
  · -- `L = 0`: 3-width waist. `M : Fin 3`; the 3-width box is `mnp`.
    have hM : M = ![M 0, M 1, M 2] := by
      funext i; fin_cases i <;> rfl
    rw [hM]
    exact routeMBoxThresholdFinite_mnp (M 0) (M 1) (M 2)
  · -- `L = L'+1`: `≥ 4`-width waist. Reorient to the good `rev M`, apply (d), transfer back.
    apply routeMBoxThresholdFinite_of_rev
    have hgood_rev : deepTailMin (M ∘ Fin.rev) ≤ (M ∘ Fin.rev) 1 :=
      deepTailMin_rev_le_of_waist M hwaist
    have hdgood : DecoratedBoxThresholdFinite (SJDecoration.trivial (M ∘ Fin.rev)) :=
      deeperFlagGood_finite (M ∘ Fin.rev) (SJDecoration.trivial (M ∘ Fin.rev))
        (adm_trivial _ _) hgood_rev hIH
    exact (decoratedBoxThresholdFinite_trivial_iff (M ∘ Fin.rev)).mp hdgood

end DLNFibre.DLN.RLCT
