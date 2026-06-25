# thread 08 — reduce-to-normal-form (G1, formalisation / tide — independent, bankable)

**Type:** formalisation (tide) · `OPENED → SPECIFY → PROVE → AUDIT`. The first concrete rung of the
rank-chart build. **Independent of the G2 crux** — it reduces the fibre-codim problem to a single
normal-form target `E`, and is reusable regardless of how G2/G3 resolve. Safe to build now.

## Goal (a new `Core` module — `DLNFibre/Core/FibreNormalForm.lean`)
For a field `k`, `d : Fin (N+1) → ℕ`, and `B B' : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k` of the
**same rank** (`B.rank = B'.rank`), the fibre codimension is the same:

    codimRepCanonical (fibre d B) = codimRepCanonical (fibre d B')

and in particular `= codimRepCanonical (fibre d E)` for the normal form `E = (rank-r partial identity)`.
This reduces the full Lemma-4.6 problem (all rank-r `B`) to the single fibre over `E`.

## Mechanism (the GL_{d_N}×GL_{d_0} action — over any field, no IsAlgClosed needed)
1. **The end-factor action.** `P = (P_N, P_0) ∈ GL (Fin d_N) k × GL (Fin d_0) k` acts on `Rep_d` by
   `(P • A)_i = A_i` for `0<i<N`, `(P•A)_{last} = P_N · A_{last}`, `(P•A)_0 = A_0 · P_0⁻¹` (act on the two
   END factors only). This is a **linear automorphism** of `Rep_d = Tuple d`.
2. **mult-equivariance.** `mult d (P • A) = P_N · (mult d A) · P_0⁻¹` (telescoping; the inner factors
   cancel). Hence `A ∈ fibre d B ↔ P•A ∈ fibre d (P_N · B · P_0⁻¹)`, i.e. the linear automorphism maps
   `fibre d B` bijectively onto `fibre d (P_N·B·P_0⁻¹)`.
3. **codim-invariance.** A linear automorphism of `Rep_d` induces a `k`-algebra automorphism of the
   coordinate ring `MvPolynomial (RepCoord d) k`; `Ideal.height (vanishingIdeal …)` is invariant under it
   — use `NullstellensatzCodim.height_map_algEquiv` (or the engine's nearest codim-invariance-under-linear-iso
   lemma; probe with `example` first). So `codimRepCanonical (fibre d B) = codimRepCanonical (fibre d (P_N·B·P_0⁻¹))`.
4. **transitivity / normal form.** Any `B` of rank r equals `P_N · E · P_0⁻¹` for some invertible
   `P_N, P_0` and the partial-identity `E` (rank factorization / rank-normal-form over a field — find the
   Mathlib lemma: `Matrix.rank`-based equivalence, `Matrix.exists_…`/`equiv_…`; probe). Chain (2)+(3)+(4):
   same rank ⟹ same fibre codim.

## Read first
- `Core/Setup.lean` (`mult`, `multPrefix_zero/_succ`, `fibre`, `Tuple`, `mem_fibre`).
- `Core/OrbitCodim.lean` (`RepCoord`, `canonicalCoord`, `canonicalCoord_apply`, `codimRepCanonical`).
- `Core/NullstellensatzCodim.lean` (`height_map_algEquiv`, `vanishingIdeal`, the codim defs).
- `Core/Orbit.lean` / `Core/OrbitVariety.lean` (existing `GL_d` action patterns — reuse the linear-action
  + codim-invariance idiom if present; do NOT reinvent).
- `lean/CLAUDE.md` (zero sorry/axiom/native_decide; `decide +kernel`; `↦`; name=content; bedrock).

## Build / process
- **Build via `scripts/lb` from `lean/`, never bare `lake build`, never `lake exe cache get`.**
- SPECIFY-first: pin the action + equivariance + the codim-invariance lemma with `example` blocks before
  the transitivity assembly. The equivariance (step 2) and the rank-normal-form (step 4) are where API
  friction lives — confirm the Mathlib rank-factorization lemma exists before building on it.
- One new module under `Core/`; **Core only — never import `DLNFibre.DLN`.** Report the aggregator
  import line (controller wires `DLNFibre.lean`).

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on the headline =
`[propext, Classical.choice, Quot.sound]`. Witness: on `(2,2,2)`, two rank-1 matrices have equal fibre codim.

## Scope
**Just G1** (the same-rank ⟹ same-fibre-codim reduction + the normal-form corollary). G2 (chart
trivialization), G3 (dim-additivity), G4 (DLN wiring) are later tides — NOT in scope. If the
rank-normal-form or equivariance walls, STOP and report the precise blocker (don't grind / don't sorry).
Don't touch other worktrees or any stash. In-repo memory only.

## Report
(i) theorem names + signatures (the action, equivariance, the same-rank codim equality, the `E` corollary);
(ii) green/sorries/axioms; (iii) module path + aggregator import line; (iv) the Mathlib rank-normal-form
lemma used + any v4.29 friction for the gotchas log.
