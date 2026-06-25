# thread 20 — R2-3b-4: the product iso `e` + descent (THE HARD RUNG, the expedition crux)

**Type:** formalisation (tide) · `OPENED → SPECIFY → CHECKPOINT(no-skip, HARD) → PROVE → AUDIT`. The
final rung of the deep product trivialization `e`, and the rung the whole bundle-shift rests on. Codex
flagged this as "the one precise missing rung." The math is **certified true** (thread 16); the risk is
purely Lean-mechanical. **This is the rung that either fully closes Lemma 4.6's geometry or defines the
expedition's single named residual** — so the SPECIFY checkpoint is mandatory and the honesty boundary is
strict.

## The target
Build, on the pivot chart, the product trivialization
```
e : Sred d r hp hq ≃ₐ[k] SchurLoc (d 0) (d (Fin.last N)) r ⊗[k] FibreAlg d E
```
matching the signature `R2-3a`'s `fibreGenIdeal_isRadical_of_trivialization` consumes
(`R = SchurLoc …`, `S = Sred …`, `e`, `hSred = isReduced_Sred` — already in hand). `E` is the rank
normal form `diag(I_r, 0)`. If reachable, ALSO make `e` an `≃ₐ[SchurLoc]` iso (the `sredSchurAlgebra`
structure) — R2-5 needs the `SchurLoc`-algebra structure for the flat/going-down height-additivity; the
`≃ₐ[k]` is the minimum R2-3a needs.

## The construction (Codex build order steps 5–7; reuse everything landed)
1. **The endpoint gauge from the Schur data.** For `M = mult(A)` of rank `r` (pivot block `Δ` invertible),
   the explicit factorization `M = L · E · H` is
   - `L = [[I_r, 0], [M21·Δ⁻¹, I_{p−r}]]` (lower-unitriangular, `d_N × d_N`),
   - `H = diag(Δ, I_{q−r}) · [[I_r, Δ⁻¹·M12], [0, I_{q−r}]]` (invertible `d_0 × d_0`),

   so that `L⁻¹ · M · H⁻¹ = E` (verify: `L⁻¹ M H⁻¹` with `M22 = M21 Δ⁻¹ M12`). `Δ`, `M12`, `M21` are the
   `SchurLoc` base coordinates; `Δ⁻¹` exists in `SchurLoc` (it inverts `detΔ`), so `L`, `H` are **units
   over `R = SchurLoc`**. The endpoint gauge is `P_0 = H`, `P_last = L⁻¹`, interior `= 1`; then b-3's
   `gaugeEquiv_multPoly` gives `gaugeEquiv (multPoly) = P_last · multPoly · P_0⁻¹ = L⁻¹ · multPoly · H⁻¹`,
   i.e. `mult(Ã) = E` for the gauged tuple `Ã`.
2. **`FE := FibreAlg d E = MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d E`** (R2-3a's `FibreAlg`).
3. **`FE →ₐ[k] Sred`** by quotient-lifting the normalized coordinates; **`Sred →ₐ[R] R ⊗_k FE`** by
   sending original coordinates to de-normalized fibre coordinates (read the gauge `P` from the base
   data). Assemble `e` by `AlgEquiv.ofAlgHom`; prove the inverses on quotient generators
   (`Ideal.Quotient.mk_surjective` + `AlgHom.ext`).

## THE HARD HALF (Codex): the descent
The gauge `gaugeEquiv` is landed on the **unquotiented** ring. The work is to **descend it through the
localization (at `ΔPdeep`) and the quotient (by `IadDeep`)** to `Sred`, and to show the gauged
coordinates **split** as `R ⊗_k FE` (base Schur data ⊗ normalized fibre). Expect: the gauge preserves
`ΔPdeep` up to a unit (so it descends to the localization); it carries `IadDeep` appropriately; the
normalized coordinates separate into the `SchurLoc` generators and the `fibreGenIdeal`-quotient generators.

## SPECIFY-first — HARD no-skip checkpoint
1. SPECIFY: pin (a) the explicit `L`, `H` as `SchurLoc`-units (the `Δ⁻¹` block + the unitriangular
   blocks); (b) the two `AlgHom` directions; (c) **the descent mechanism** — how `gaugeEquiv` passes
   through `Localization.Away ΔPdeep ⧸ IadDeep`, and how the split is proven. Pre-stage uncertain API with
   `example` blocks. **Fire a decorrelated `local-codex-consult` (xhigh)** on the descent + the split;
   save under `threads/20-product-iso-descent/codex/`.
2. **CHECKPOINT — message `main` BEFORE grinding the descent:** the pinned `L`/`H`, the two maps, and the
   descent mechanism + reachability verdict. **Do NOT proceed to grind the descent without this checkpoint.**
   If the descent or the split needs scaffolding Mathlib lacks (a localized-quotient interchange, a
   tensor-decomposition the engine has no handle for), CHECKPOINT a committed partial + report — that is a
   genuine wall, and the right outcome is to close the expedition against `e` (everything else is banked),
   NOT to grind or sorry.
3. PROVE (bank seams: `L`/`H` units, then each `AlgHom` direction, then the descent, then `e` + the
   round-trips) → AUDIT.

## Rules
`cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean` EVERY call (default
cwd = MAIN checkout, different branch); `scripts/lb` only (never bare `lake build`/`cache get`); NEVER
`git add -A`; commit partials frequently and **commit finished work BEFORE going idle** (don't leave a
completed module uncommitted — that caused a near-miss); zero sorry/axiom/native_decide/#exit; `↦`;
`decide +kernel`; name = content. **Core only — never import `DLNFibre.DLN`.** Don't edit the aggregator —
REPORT the import line. **You are the SOLE write-tide on `expedition/fibre-codimension`.**

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on `e` + the round-trips =
`[propext, Classical.choice, Quot.sound]`. Non-vacuity: `e` exhibited at `(2,2,2), r=1` over
`AlgebraicClosure ℚ` (`7 = 3 + 4` dims: `Sred` ≅ `SchurLoc(dim 3) ⊗ F_E(dim 4)`). **CRITICAL honesty
gate:** `e` must be genuinely constructed — every `AlgHom`/round-trip proved sorry-free against the real
objects, NOT against a hypothesis or a placeholder. The moment `e` is real, plug it (with `isReduced_Sred`)
into `fibreGenIdeal_isRadical_of_trivialization` and report that `fibreGenIdeal d E` is now
**unconditionally** radical.

## Scope
**R2-3b-4 only** (build `e`; discharge R2-3a's chain to get `fibreGenIdeal d E` radical unconditionally).
**NOT** R2-5 (`height m_B = δ` + flat/going-down), **NOT** R2-6 (`+C` assembly), **NOT** G3/G4 (lift +
discharge `BundleShiftInterface`) — those are the next tides. **No result here claims `codim = C + δ` or
discharges `BundleShiftInterface`.** Report to `main`: def/theorem names + signatures; green/sorries/axioms;
module path + aggregator line; the descent mechanism used; whether `e` is genuinely built (the headline) or
the descent walled (the residual); the exact handoff to R2-5.
