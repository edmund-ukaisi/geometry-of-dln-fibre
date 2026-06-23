# thread 05 — comorphism keystone (Tide F1, formalisation / tide — FOUNDATIONAL)

**Type:** formalisation (tide) · `OPENED → BUILD → AUDIT`. The keystone of the Lemma-4.6 build: it
constructs the coordinate-ring map for `mult` that thread-04 found missing, and identifies the fibre's
coordinate ring as a quotient — the object every downstream rung (the height-squeeze) consumes.

## Goal (a new `Core` module — `DLNFibre/Core/MultComorphism.lean`)

`mult` is defined over **any** `CommRing` (`Core.Setup.mult`), so the product-entry polynomials are just
`mult` applied to the GENERIC tuple. Build, for `d : Fin (N+1) → ℕ` over a field `k`:

1. **`multPoly`** — the generic product entries. Let `genericTuple : Tuple (k := MvPolynomial (RepCoord d) k) d`
   have `(genericTuple i) a b = MvPolynomial.X ⟨i, a, b⟩`. Define
   `multPoly d : Fin (d (Fin.last N)) → Fin (d 0) → MvPolynomial (RepCoord d) k :=
     fun r c ↦ (mult d genericTuple) r c`.
   (Reuse the existing `mult`/`multPrefix` over the polynomial ring — do NOT re-derive a recursion.)

2. **`eval_multPoly` (the bridge)** — for every tuple `A : Tuple (k := k) d` and every `(r,c)`:
   `MvPolynomial.eval (canonicalCoord d A) (multPoly d r c) = (mult d A) r c`.
   Proof spine: `MvPolynomial.eval (canonicalCoord d A)` is a ring hom; it commutes with the matrix
   product `multPrefix`/`mult` (induct with `multPrefix_zero`/`multPrefix_succ`, `RingHom.map_matrix_mul`
   or `Matrix.map`-style entrywise), and on a single variable `eval (canonicalCoord A) (X ⟨i,a,b⟩) =
   canonicalCoord d A ⟨i,a,b⟩ = (A i) a b` by `canonicalCoord_apply`. So the generic product evaluates to
   the actual product. This is the load-bearing lemma; everything else is corollary.

3. **Fibre as zero-locus** — `canonicalCoord d '' (fibre d B) =
   MvPolynomial.zeroLocus {multPoly d r c - MvPolynomial.C (B r c) | (r,c)}` (over `k`; `B :
   Matrix (Fin d_N) (Fin d_0) k`). Membership chase via `eval_multPoly` + `mem_fibre` + `Matrix.ext_iff`.

4. **`vanishingIdeal(fibre) = radical(fibre-gen-ideal)`** — with `[IsAlgClosed k]`, let
   `fibreGenIdeal d B := Ideal.span {multPoly d r c - C (B r c) | (r,c)}`; then
   `vanishingIdeal k (canonicalCoord d '' fibre d B) = (fibreGenIdeal d B).radical`
   (the engine's Nullstellensatz: see `NullstellensatzCodim.lean` for `vanishingIdeal`/`zeroLocus`/the
   strong-Nullstellensatz lemma name it uses — `vanishingIdeal_zeroLocus_eq_radical` or similar; find
   the exact name with `rg` over the file and Mathlib).

5. **The comorphism + `Ideal.map` identification** —
   `multComap d : MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k →ₐ[k] MvPolynomial (RepCoord d) k :=
     MvPolynomial.aeval (fun rc ↦ multPoly d rc.1 rc.2)`, and
   `fibreGenIdeal d B = Ideal.map multComap (maxIdealOfPoint B)` where
   `maxIdealOfPoint B = Ideal.span {X rc - C (B rc.1 rc.2) | rc}` (the maximal ideal of the point `B` in
   the target coordinate ring). i.e. the fibre generator-ideal is the extension of `B`'s maximal ideal
   along the comorphism — the "fibre coordinate ring `= R_total ⧸ m_B·R_total`" object F2 needs.

**Stretch (only if cheap):** a clean restatement
`MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(fibre) ≃ₐ (coordinate ring of the fibre)` — skip if it
fights dependent types; (4)+(5) already pin the object.

## Read first
- `Core/Setup.lean` (`mult`, `multPrefix`, `multPrefix_zero/_succ`, `fibre`, `mem_fibre`).
- `Core/OrbitCodim.lean` (`RepCoord`, `canonicalCoord`, `canonicalCoord_apply`, `codimRep[Canonical]`,
  `vanishingIdeal` usage).
- `Core/NullstellensatzCodim.lean` (`vanishingIdeal`, `zeroLocus`, the Nullstellensatz lemma + the
  catenary bridge — F2 consumes this; confirm the exact lemma names by reading the file).
- `lean/CLAUDE.md` (zero sorry/axiom/native_decide; `decide +kernel`; `↦`; name = content; bedrock).

## Build / process
- **Build via `scripts/lb` from `lean/`, never bare `lake build`** (shared mathlib store + global
  semaphore). Do NOT `lake exe cache get`. `scripts/lb DLNFibre.Core.MultComorphism` for the module,
  `scripts/lb` for the whole library before AUDIT.
- **SPECIFY-first**: pin (1)+(2) signatures and get `eval_multPoly` to green before building (3)–(5);
  the bridge is where any API friction surfaces. Pre-stage uncertain Mathlib API (`eval`-is-ringhom over
  matrices, `RingHom.map_matrix_mul`, `aeval`, `Ideal.map`/`radical`/`vanishingIdeal`) with `example`
  blocks kept as durable contracts.
- One new module under `Core/`; controller aggregates `DLNFibre.lean` (do not edit the aggregator
  yourself — report the import line). **Dependency rule: `Core` only, never import `DLNFibre.DLN`.**

## AUDIT gate
`scripts/lb` green (whole library); `scripts/sorries` 0; `#print axioms` on the headline lemmas
`[propext, Classical.choice, Quot.sound]` (no `native_decide`, no new global axiom). Non-vacuity: the
`(2,2,2)` witness (`Setup.tupleWitness`) — `eval_multPoly` at it reproduces `!![1,2;3,7]`.

## Scope
**Just F1** (the comorphism + fibre-ideal identification). The height-squeeze (F2), flatness/sandwich,
and assembly (F3) are subsequent tides — NOT in scope. Don't touch other worktrees or any stash.
In-repo memory only.

## Report
(i) final theorem/def names + signatures (`multPoly`, `eval_multPoly`, the zero-locus identity, the
`vanishingIdeal = radical` identity, `multComap`, the `Ideal.map` identity); (ii) green/sorries/axioms;
(iii) module path + the aggregator import line for the controller; (iv) any API friction found (for the
gotchas log) + whether the `vanishingIdeal = radical` step needed `IsAlgClosed` only or more.
