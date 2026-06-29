import DLNFibre.DLN.RLCT.Validate.RouteMChainFDerivValue
import DLNFibre.DLN.RLCT.Validate.RouteMGenChain

/-!
# `RouteMAgenFDerivValue` — the fderiv VALUE of the chain layers `Cgen` / `Agen` (opaque-width)

Sub-piece 1 (continued) of the opaque-`M` fderiv-as-staircase construction: threading the per-layer
fderiv atoms (`RouteMChainFDerivValue.hasFDerivAt_chainA`/`hasFDerivAt_chainQ`) up through the
chain's compressed-transition `Cgen` and layer `Agen`.

`Cgen k = Bmat k · chainQ(Nblk k) + u • Rmat k` (interior `k < L`), `u • Rfin k` (leaf). `Agen k =
chainA(Nblk k, Wblk k, Cgen(k+1))` (interior), `0` (leaf). Their fderiv VALUES assemble from the
atoms by the matrix-calculus combinators (`HasFDerivAt.matMul`/`.add`/`.smul`), GENERIC in the block
fderivs (passed as hypotheses) — the live-decoder block fderivs discharge them at the wiring stage.

* `hasFDerivAt_Cgen_interior` — the interior `Cgen k` (`k < L`) fderiv value.
* `hasFDerivAt_Cgen_leaf` — the leaf `Cgen k` (`¬ k < L`) fderiv value (`u • Rfin`).
* `hasFDerivAt_Agen_interior` — the interior `Agen k` (`k < L`) fderiv value (via `chainA`).
* `hasFDerivAt_Agen_leaf` — the leaf `Agen k` (`¬ k < L`) fderiv value (the constant `0`).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib calculus + the banked chain atoms).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The interior `Cgen k` fderiv value** (`k < L`). Given the block readers `Bf`/`Nf`/`Rf` (the
decoder's `Bmat k`/`Nblk k`/`Rmat k`) and the radial scalar `uf` with fderivs `dB`/`dN`/`dR`/`du`,
`Cgen (uf x) … k` — i.e. `Bf x · chainQ(Nf x) + uf x • Rf x` — has the product/sum fderiv. Built
from `HasFDerivAt.matMul` (the `Bf · chainQ(Nf)` product, `hasFDerivAt_chainQ` the chaining-row
fderiv), `.add`, `HasFDerivAt.smul` (the `uf • Rf` radial term). -/
theorem hasFDerivAt_Cgen_interior {Nn k : ℕ} (M t : Fin (L + 1) → ℕ)
    (hle : ∀ j, j < L → Text M t (j + 1) ≤ Wext M j) (hk : k < L)
    (uf : (Fin Nn → ℝ) → ℝ)
    (Bf : (Fin Nn → ℝ) → Matrix (Fin (Text M t k)) (Fin (Text M t (k + 1))) ℝ)
    (Nf : (Fin Nn → ℝ) → Matrix (Fin (Text M t (k + 1))) (Fin (Wext M k - Text M t (k + 1))) ℝ)
    (Rf : (Fin Nn → ℝ) → Matrix (Fin (Text M t k)) (Fin (Wext M k)) ℝ)
    (du : (Fin Nn → ℝ) →L[ℝ] ℝ)
    (dB : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin (Text M t k)) (Fin (Text M t (k + 1))) ℝ)
    (dN : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin (Text M t (k + 1))) (Fin (Wext M k - Text M t (k + 1))) ℝ)
    (dR : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin (Text M t k)) (Fin (Wext M k)) ℝ)
    (u : Fin Nn → ℝ)
    (hu : HasFDerivAt uf du u) (hB : HasFDerivAt Bf dB u) (hN : HasFDerivAt Nf dN u)
    (hR : HasFDerivAt Rf dR u) :
    HasFDerivAt
      (fun x => Bf x * chainQ (genWidthEq M t hle k hk) (Nf x) + uf x • Rf x)
      ((matMulBilin (Text M t k) (Text M t (k + 1)) (Wext M k)).precompR (Fin Nn → ℝ)
          (Bf u) (chainQFDeriv (genWidthEq M t hle k hk) dN)
        + (matMulBilin (Text M t k) (Text M t (k + 1)) (Wext M k)).precompL (Fin Nn → ℝ)
          dB (chainQ (genWidthEq M t hle k hk) (Nf u))
        + (uf u • dR + du.smulRight (Rf u))) u :=
  (HasFDerivAt.matMul hB
    (hasFDerivAt_chainQ (genWidthEq M t hle k hk) Nf dN u hN)).add (hu.smul hR)

/-- **The leaf `Cgen k` fderiv value** (`¬ k < L`): `Cgen k = u • Rfin k`, with fderiv
`uf u • dRfin + du.smulRight (Rfin u)` (`HasFDerivAt.smul`). -/
theorem hasFDerivAt_Cgen_leaf {Nn k : ℕ} (M t : Fin (L + 1) → ℕ)
    (uf : (Fin Nn → ℝ) → ℝ)
    (Rfinf : (Fin Nn → ℝ) → Matrix (Fin (Text M t k)) (Fin (Wext M k)) ℝ)
    (du : (Fin Nn → ℝ) →L[ℝ] ℝ)
    (dRfin : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin (Text M t k)) (Fin (Wext M k)) ℝ)
    (u : Fin Nn → ℝ) (hu : HasFDerivAt uf du u) (hRfin : HasFDerivAt Rfinf dRfin u) :
    HasFDerivAt (fun x => uf x • Rfinf x) (uf u • dRfin + du.smulRight (Rfinf u)) u :=
  hu.smul hRfin

/-- **The interior `Agen k` fderiv value** (`k < L`): `Agen k = chainA(Nblk k, Wblk k, Cgen(k+1))`,
fderiv `chainAFDeriv` (`hasFDerivAt_chainA`). Generic in the layer readers `Nf`/`Wf` and the next
compressed transition `Cf = Cgen(k+1)` (whose fderiv is the threaded `Cgen` value). -/
theorem hasFDerivAt_Agen_interior {Nn k : ℕ} (M t : Fin (L + 1) → ℕ)
    (hle : ∀ j, j < L → Text M t (j + 1) ≤ Wext M j) (hk : k < L)
    (Nf : (Fin Nn → ℝ) → Matrix (Fin (Text M t (k + 1))) (Fin (Wext M k - Text M t (k + 1))) ℝ)
    (Wf : (Fin Nn → ℝ) →
      Matrix (Fin (Wext M k - Text M t (k + 1))) (Fin (Wext M (k + 1))) ℝ)
    (Cf : (Fin Nn → ℝ) → Matrix (Fin (Text M t (k + 1))) (Fin (Wext M (k + 1))) ℝ)
    (dN : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin (Text M t (k + 1))) (Fin (Wext M k - Text M t (k + 1))) ℝ)
    (dW : (Fin Nn → ℝ) →L[ℝ]
      Matrix (Fin (Wext M k - Text M t (k + 1))) (Fin (Wext M (k + 1))) ℝ)
    (dC : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin (Text M t (k + 1))) (Fin (Wext M (k + 1))) ℝ)
    (u : Fin Nn → ℝ)
    (hN : HasFDerivAt Nf dN u) (hW : HasFDerivAt Wf dW u) (hC : HasFDerivAt Cf dC u) :
    HasFDerivAt (fun x => chainA (genWidthEq M t hle k hk) (Nf x) (Wf x) (Cf x))
      (chainAFDeriv (genWidthEq M t hle k hk) Nf Wf dN dW dC u) u :=
  hasFDerivAt_chainA (genWidthEq M t hle k hk) Nf Wf Cf dN dW dC u hN hW hC

/-- **The leaf `Agen k` fderiv value** (`¬ k < L`): `Agen k = 0`, fderiv `0` (const). -/
theorem hasFDerivAt_Agen_leaf {Nn k : ℕ} (M : Fin (L + 1) → ℕ) (u : Fin Nn → ℝ) :
    HasFDerivAt
      (fun _ : Fin Nn → ℝ => (0 : Matrix (Fin (Wext M k)) (Fin (Wext M (k + 1))) ℝ))
      (0 : (Fin Nn → ℝ) →L[ℝ] Matrix (Fin (Wext M k)) (Fin (Wext M (k + 1))) ℝ) u :=
  hasFDerivAt_const _ _

end DLNFibre.DLN.RLCT
