import DLNFibre.DLN.RLCT.Validate.D1GeChartGlobal
import DLNFibre.DLN.RLCT.Validate.D1GeBlockModel

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeChartGerm` — the BlockParamsGen↔chain bridge (rung 8 prep)

The general-`L` chart `schurChartRawGen` is `ℕ`-indexed (chain form, the home of `partProd`). The
globalisation conjugates by `blockFlatEquivGen : flat ≃L BlockParamsGen H r` (Fin `L`-indexed). The
bridge `chainToBlockGen` / `blockToChainGen` converts between the two — a per-slot width recast
(`deepestChainWidth H s = H s.castSucc` for `s < L`, via `Equiv.sumCongr … (finCongr …)`), the last
plumbing piece before assembling `schurChart_global_gen`.
-/

open Matrix
namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **chain → BlockParamsGen.** Recast a first-`L`-slot chain (`deepestChainWidth` widths) to the
`Fin L`-indexed `BlockParamsGen H r` (per-vertex `H` widths), reindexing each slot `s` by the width
equivalence `deepestChainWidth H s = H s.castSucc`. -/
noncomputable def chainToBlockGen (H : Fin (L + 1) → ℕ) (r : ℕ)
    (Cch : (s : ℕ) → Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ) : BlockParamsGen H r :=
  fun s => Matrix.reindex
    (Equiv.sumCongr (Equiv.refl (Fin r))
      (finCongr (congrArg (· - r) (deepestChainWidth_castSucc H s.val s.isLt).symm)))
    (Equiv.sumCongr (Equiv.refl (Fin r))
      (finCongr (congrArg (· - r) (deepestChainWidth_succ H s.val s.isLt).symm)))
    (Cch s.val)

/-- **BlockParamsGen → chain.** Recast the `Fin L`-indexed `BlockParamsGen H r` to a first-`L`-slot
chain (`deepestChainWidth` widths); slots `≥ L` default to `0` (invisible to `partProd (last+1)`,
which reads only slots `< L`). -/
noncomputable def blockToChainGen (H : Fin (L + 1) → ℕ) (r : ℕ) (P : BlockParamsGen H r) :
    (s : ℕ) → Matrix (Fin r ⊕ Fin (deepestChainWidth H s - r))
      (Fin r ⊕ Fin (deepestChainWidth H (s + 1) - r)) ℝ :=
  fun s =>
    if hs : s < L then
      Matrix.reindex
        (Equiv.sumCongr (Equiv.refl (Fin r))
          (finCongr (congrArg (· - r) (deepestChainWidth_castSucc H s hs))))
        (Equiv.sumCongr (Equiv.refl (Fin r))
          (finCongr (congrArg (· - r) (deepestChainWidth_succ H s hs))))
        (P ⟨s, hs⟩)
    else 0

end DLNFibre.DLN.RLCT
