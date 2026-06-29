import DLNFibre.DLN.RLCT.Validate.RouteMStaircaseDet

/-!
# `RouteMStairFold` — the general `n`-fold lower-triangular staircase determinant (network-free)

The general `Fin L`-fold generalization of `RouteMStaircaseDet.lowerTri3_det` (which the
`staircase-det-bricks-statement-card.md` defers): a block-lower-triangular endomorphism of a nested
product `V 0 × (V 1 × (… × (V (n−1) × PUnit)))`, whose diagonal blocks are `f 0, …, f (n−1)` and whose
strictly-lower couplings are arbitrary (each layer `s` may feed any lower layer `> s`), has determinant
`∏_{s < n} (f s).det`. This is the linear-map-level det spine the opaque-`M` interior-det assembly applies
per chain layer — the controller's named escape (`coarse-route-grading-obstruction.md`) from the
single-grading `Matrix.BlockTriangular` partition wall.

The encoding recurses on the length `n`:

* `StairProd V n` — the nested product space `V 0 × StairProd (V ∘ succ) (n−1)`, `PUnit` at `n = 0`.
* `stairMap` — the staircase endomorphism: `f 0` on the head, the recursive staircase on the tail, with a
  single coupling `head → tail-product` (the head's contribution into ALL lower layers, packaged as one
  map into the tail nested-product). Built from `lowerTri`.
* `stairMap_det` — `det (stairMap f c) = ∏_{s : Fin n} (f s).det`, by induction peeling one `lowerTri_det`
  per layer.

Because the coupling is a single `V 0 →ₗ StairProd (tail)` map, ANY strictly-lower coupling pattern
(layer `s` into any subset of layers `> s`) is expressible — the nested product collects all lower layers.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (determinant; no analysis).
-/

open scoped BigOperators

noncomputable section

namespace DLNFibre.DLN.RLCT

universe u

/-! ## The nested staircase product space -/

/-- **The nested staircase product** `V 0 × (V 1 × (… × (V (n−1) × PUnit)))`, recursing on the length `n`.
At `n = 0` it is `PUnit` (the empty product); at `n+1` it is `V 0 × StairProd (V ∘ succ) n`. -/
def StairProd (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] : ℕ → Type u
  | 0 => PUnit
  | (n + 1) => V 0 × StairProd (fun k => V (k + 1)) n

instance instAddCommGroupStairProd (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    ∀ n, AddCommGroup (StairProd V n)
  | 0 => (inferInstance : AddCommGroup PUnit)
  | (n + 1) => by
      letI := instAddCommGroupStairProd (fun k => V (k + 1)) n
      exact (inferInstance : AddCommGroup (V 0 × StairProd (fun k => V (k + 1)) n))

instance instModuleStairProd (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    ∀ n, Module ℝ (StairProd V n)
  | 0 => (inferInstance : Module ℝ PUnit)
  | (n + 1) => by
      letI := instAddCommGroupStairProd (fun k => V (k + 1)) n
      letI := instModuleStairProd (fun k => V (k + 1)) n
      exact (inferInstance : Module ℝ (V 0 × StairProd (fun k => V (k + 1)) n))

instance instFiniteStairProd (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] :
    ∀ n, FiniteDimensional ℝ (StairProd V n)
  | 0 => (inferInstance : FiniteDimensional ℝ PUnit)
  | (n + 1) => by
      letI := instAddCommGroupStairProd (fun k => V (k + 1)) n
      letI := instModuleStairProd (fun k => V (k + 1)) n
      letI := instFiniteStairProd (fun k => V (k + 1)) n
      exact (inferInstance : FiniteDimensional ℝ (V 0 × StairProd (fun k => V (k + 1)) n))

/-! ## The staircase endomorphism + its determinant -/

/-- **The staircase coupling datum** over `V` of length `n`: at each level a head-into-tail coupling
`V 0 →ₗ StairProd (tail) (n−1)`. Recursing on `n` keeps the tail type native (`fun k => V (k+1)`), so no
`s+1+k`/`n−1−s` index arithmetic leaks into `stairMap`'s signature. The det discards the couplings;
this datum only fixes the staircase's strictly-lower part. -/
def StairCoupling (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)] :
    ℕ → Type u
  | 0 => PUnit
  | (n + 1) =>
      (V 0 →ₗ[ℝ] StairProd (fun k => V (k + 1)) n) × StairCoupling (fun k => V (k + 1)) n

/-- **The staircase endomorphism** of `StairProd V n`: the head map `f 0`, the recursive staircase on the
tail, and the head-into-tail coupling `c.1 : V 0 →ₗ StairProd (tail) (n−1)` (which packages the head's
feed into ALL lower layers). At `n+1` it is `lowerTri (f 0) (stairMap (tail)) c.1`; at `n = 0` it is the
(unique) endomorphism of `PUnit`. -/
def stairMap (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] :
    (n : ℕ) → ((s : ℕ) → V s →ₗ[ℝ] V s) → StairCoupling V n →
    (StairProd V n →ₗ[ℝ] StairProd V n)
  | 0, _, _ => 0
  | (n + 1), f, c =>
      lowerTri (f 0)
        (stairMap (fun k => V (k + 1)) n (fun s => f (s + 1)) c.2)
        c.1

/-- **The `n`-fold staircase determinant**: `det (stairMap V n f c) = ∏_{s : Fin n} (f s).det` — the
strictly-lower couplings `c` are det-irrelevant. Induction on `n`, peeling one `lowerTri_det` per layer
(the head `f 0`, then the tail staircase by IH), reassembled by `Fin.prod_univ_succ`. The general-`L`
generalization of `lowerTri3_det`; the linear-map-level det spine the opaque-`M` interior-det assembly
applies per chain layer. -/
theorem stairMap_det (V : ℕ → Type u) [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] :
    ∀ (n : ℕ) (f : (s : ℕ) → V s →ₗ[ℝ] V s) (c : StairCoupling V n),
      LinearMap.det (stairMap V n f c) = ∏ s : Fin n, (f s).det
  | 0, f, _ => by
      simp only [stairMap, Finset.univ_eq_empty, Finset.prod_empty]
      -- `StairProd V 0 = PUnit` is a `Subsingleton`, so any endomorphism has det `1`.
      haveI : Subsingleton (StairProd V 0) := (inferInstance : Subsingleton PUnit)
      exact LinearMap.det_eq_one_of_subsingleton _
  | (n + 1), f, c => by
      change LinearMap.det
          (lowerTri (f 0) (stairMap (fun k => V (k + 1)) n (fun s => f (s + 1)) c.2) c.1) = _
      rw [lowerTri_det, stairMap_det (fun k => V (k + 1)) n (fun s => f (s + 1)) c.2,
        Fin.prod_univ_succ]
      rfl

/-! ## Non-vacuity: the staircase fires on a genuine `n = 3` coupling

The general det specializes to the banked `lowerTri3_det` shape and discards genuine nonzero couplings —
the `n`-fold spine is not a hollow generalization. -/

/-- **Non-vacuity (`n = 3`, scalar layers, genuine couplings).** On `V s = ℝ` with diagonal scalars
`a, b, c` (as `mulRight`) and arbitrary nonzero couplings, the 3-fold staircase det is `a·b·c` — the
couplings drop out, matching `lowerTri3_det`'s shape at general length. -/
example (a b c : ℝ) (c0 : ℝ →ₗ[ℝ] StairProd (fun _ : ℕ => ℝ) 2)
    (c1 : ℝ →ₗ[ℝ] StairProd (fun _ : ℕ => ℝ) 1) :
    LinearMap.det
        (stairMap (fun _ : ℕ => ℝ) 3
          (fun s => if s = 0 then LinearMap.mulRight ℝ a
            else if s = 1 then LinearMap.mulRight ℝ b else LinearMap.mulRight ℝ c)
          ⟨c0, ⟨c1, ⟨0, PUnit.unit⟩⟩⟩)
      = a * b * c := by
  rw [stairMap_det]
  simp only [Fin.prod_univ_three, Fin.isValue]
  norm_num [LinearMap.det_ring]

end DLNFibre.DLN.RLCT

end
