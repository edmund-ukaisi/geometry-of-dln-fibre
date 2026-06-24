# Statement card — R2-3b-3 the endpoint-normalization (gauge) AlgEquiv (thread 19)

> **Claim.** On the **unquotiented** coordinate ring `MvPolynomial (RepCoord d) R` over an
> **arbitrary** commutative ring `R`, the endpoint normalization is the linear coordinate change
> implementing the vertex-unit conjugation action `Aᵢ ↦ P_{i+1} · Aᵢ · P_i⁻¹` (`Core.BaseChange`) on
> the generic tuple, for a gauge `P` (one invertible matrix per vertex over `R`). It assembles to an
> `R`-algebra automorphism `gaugeEquiv d P` of `MvPolynomial (RepCoord d) R`, and under it the
> generic product entries transform as `multPoly d r c ↦ (P_last · Matrix.of (multPoly d) · P_0⁻¹) r
> c`. For the **endpoint** normalization the gauge is identity at every interior vertex and carries
> `H` at the source vertex `0`, `L⁻¹` at the target vertex `Fin.last N` — then the transport is
> `L⁻¹ · multPoly · H⁻¹`, normalizing the two endpoint factors only (the `N = 1` coincidence, where
> the single factor is both endpoints, is automatic since `baseChange` is uniform per edge). This is
> the coordinate change the deep product iso `e` (R2-3b-4) uses to turn the chart target
> `mult(A) = L·E·H` into `mult(Ã) = E`.
>
> - **Lean (substitution + equiv):** `DLNFibre.Core.gaugeSub`, `DLNFibre.Core.gaugeEquiv`,
>   `DLNFibre.Core.gaugeEquiv_apply` (`lean/DLNFibre/Core/EndpointNormalization.lean` @ `d82d0538`)
> - **Lean (mult-transport — the payload):** `DLNFibre.Core.aeval_gaugeSub_multPoly`,
>   `DLNFibre.Core.gaugeEquiv_multPoly` (same file/SHA)
> - **Lean (gauge lift):** `DLNFibre.Core.liftGauge`, `liftGauge_mul`, `liftGauge_one`,
>   `liftGauge_inv`, `liftGauge_val_eq`, `liftGauge_inv_val_eq` (same file/SHA)
> - **Lean (product-respecting spine):** `DLNFibre.Core.aeval_gaugeSub_genericTuple`,
>   `map_aeval_multPrefix`, `map_aeval_gaugeSub_mult`, `mult_smul_commRing` (same file/SHA)
> - **Lean (round-trip / composition law):** `DLNFibre.Core.map_aeval_gaugeSub_liftGauge`,
>   `map_aeval_gaugeSub_baseChange`, `aeval_gaugeSub_gaugeSub`, `gaugeSub_one` (same file/SHA)
>
> - **Gloss.**
>   - `liftGauge d P : BaseChangeGroup (MvPolynomial (RepCoord d) R) d` — lift the gauge `P` (units
>     over `R`) into the coordinate ring by pushing each unit matrix through `C` (`Units.map` of
>     `(C : R →+* MvPolynomial (RepCoord d) R).mapMatrix`). `liftGauge_mul`/`_one`/`_inv` are the
>     group-hom facts; `liftGauge_val_eq`/`_inv_val_eq` read the lifted entries as `C`-images.
>   - `gaugeSub d P : RepCoord d → MvPolynomial (RepCoord d) R` — the substitution: `⟨i,(r,c)⟩` maps
>     to the `(r,c)` entry of `baseChange (liftGauge d P) (genericTuple d) i = P_{i+1} · Xᵢ · P_i⁻¹`.
>   - `gaugeEquiv d P : MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R` —
>     `AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))`; `gaugeEquiv_apply` says the
>     forward map is `aeval (gaugeSub d P)`.
>   - `aeval_gaugeSub_multPoly` / `gaugeEquiv_multPoly` — **the mult-transport**:
>     `aeval (gaugeSub d P) (multPoly d r c) = (Units.val (liftGauge d P (Fin.last N)) ·
>     Matrix.of (multPoly d) · Units.val ((liftGauge d P 0)⁻¹)) r c`, i.e. `P_last · multPoly · P_0⁻¹`.
>   - `aeval_gaugeSub_genericTuple` — `aeval (gaugeSub d P)` carries `genericTuple i` to the gauged
>     factor `baseChange (liftGauge d P) (genericTuple d) i` (`aeval_X` on the generators).
>   - `map_aeval_multPrefix` — a coordinate substitution `aeval φ` commutes with the generic prefix
>     product: `(multPrefix (genericTuple) j).map (aeval φ) = multPrefix (φ-image tuple) j` (induction
>     through `multPrefix_succ` + `Matrix.map_mul`; the `aeval`-analog of `map_eval_multPrefix`).
>   - `map_aeval_gaugeSub_mult` — the full product: `(Matrix.of (multPoly d)).map (aeval (gaugeSub P))
>     = mult d (baseChange (liftGauge P) (genericTuple))`.
>   - `mult_smul_commRing` — mult-equivariance over `CommRing`: `mult d (baseChange P A) =
>     P_last · mult d A · P_0⁻¹` (`submult_baseChange` at the full interval; the same statement as
>     `FibreNormalForm.mult_smul` but over the weaker `CommRing`, which the unquotiented-`R` contract
>     needs).
>   - `map_aeval_gaugeSub_liftGauge` — a `C`-lifted (constant) gauge matrix is fixed by
>     `aeval (gaugeSub P)` (`aeval_C`). `map_aeval_gaugeSub_baseChange` / `aeval_gaugeSub_gaugeSub` —
>     the composition law: `aeval (gaugeSub P) ∘ aeval (gaugeSub Q)` on `genericTuple` re-gauges to
>     `baseChange (liftGauge (Q*P)) (genericTuple)`; the round-trips of `gaugeEquiv` collapse by
>     `inv_mul_cancel` / `mul_inv_cancel` + `liftGauge_one` + `baseChange_one`.
>   - `gaugeSub_one` — the identity gauge substitution is `gaugeSub d 1 x = X x`.
>
> - **Proved (unconditional).** All of the above as stated, for **every** `N`, dimension vector `d`,
>   commutative ring `R`, and gauge `P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ`. `gaugeEquiv` is a
>   genuine `R`-algebra **automorphism** (both round-trips closed). The mult-transport
>   `multPoly ↦ P_last · multPoly · P_0⁻¹` holds at the level of the polynomial ring (no evaluation,
>   no field). The `N = 1` coincidence is **automatic** (no separate case) because `baseChange` is the
>   uniform per-edge conjugation reading both endpoint vertices. Sorry-free; axiom-clean `[propext,
>   Classical.choice, Quot.sound]` on `gaugeEquiv`, `gaugeEquiv_multPoly`, `aeval_gaugeSub_multPoly`,
>   `gaugeSub`. Non-vacuity in-file: (i) `gaugeEquiv d 1` reproduces the identity (the `H = L = 1`
>   check); (ii) `gaugeEquiv` available + the transport fires at the concrete `(2,2,2)` gauge
>   `witnessGauge = !![1,1;0,1]` at every vertex over `ℤ`.
>
> - **Assumed.** None. The construction takes the gauge `P` as an explicit argument with no side
>   conditions beyond `[CommRing R]` (the per-vertex matrices being **units** is the invertibility
>   needed; `BaseChangeGroup` packages it).
>
> - **Cited.** `Core.BaseChange` (`baseChange`, `baseChange_apply`/`_mul`/`_one`, `submult_baseChange`,
>   the `MulAction` instance); `Core.Submult` (`mult_eq_submult`, `multPrefix_succ`); `Core.GenericTuple`
>   (`genericTuple`, `genericTuple_apply`); `Core.MultComorphism` (`multPoly`); `Core.OrbitCodim`
>   (`RepCoord`). Mathlib: `MvPolynomial.aeval`/`aeval_X`/`aeval_C`/`algHom_ext`/`algebraMap_eq`,
>   `AlgEquiv.ofAlgHom`, `Matrix.map_mul`/`map_one`/`map_apply`, `Units.map`/`coe_map`/`coe_map_inv`,
>   `RingHom.mapMatrix`, `inv_mul_cancel`/`mul_inv_cancel`.
>
> - **Deferred (named, R2-3b-4 — the next tide).** Instantiating `P` with the **Schur-data
>   unipotents** (`H`, `L` from `mult(A) = L·E·H`), building the product iso
>   `e : Sred ≃ₐ[R] R ⊗_k F_E`, and **descending** the gauge `AlgEquiv` to the reduced chart quotient
>   `Sred` (R2-3b-1+2). **No result here claims `codim (fibre) = C + δ` or discharges
>   `BundleShiftInterface`** — this tide supplies the coordinate change on the unquotiented ring + its
>   mult-transport; it does not yet touch `Sred`, the quotient, or instantiate the endpoint matrices.
>
> - **Status.** sorry-free (AUDIT gate met: whole-library green @ `d82d0538`, `scripts/sorries` 0,
>   `#print axioms` clean on the headlines, non-vacuity shown in-file). Awaiting reviewer fidelity
>   pass. **Aggregator not yet wired** — controller to add `import DLNFibre.Core.EndpointNormalization`
>   to `DLNFibre.lean` at the green-gate.
