# thread 19 — R2-3b-3: the endpoint-normalization AlgEquiv (the coordinate change)

**Type:** formalisation (tide) · `OPENED → SPECIFY → CHECKPOINT(no-skip) → PROVE → AUDIT`. The second
rung of the deep product iso `e`. The contract is **pre-staged** in `Core.DeepChartRing` (the
`AlgEquiv.ofAlgHom (aeval toSub)(aeval fromSub)` round-trip `example`); this tide supplies the genuine
endpoint substitution + the round-trip proof. Keep it GENERAL (arbitrary invertible endpoint matrices
over an arbitrary coefficient ring `R`) so R2-3b-4 instantiates `H`, `L` with the Schur-data unipotents.

## Read first
- **`Core.DeepChartRing`** — the pre-staged R2-3b-3 contract (`example`, ~line 327): `toSub fromSub :
  RepCoord d → MvPolynomial (RepCoord d) R`, mutually inverse on generators, assemble via
  `AlgEquiv.ofAlgHom`. Your output instantiates this with the genuine endpoint substitution. Also: the
  `RepCoord`/endpoint indexing this module already navigates (`repStratumEquiv`, the `dStratum` endpoint
  `rfl`s), and `Core.OrbitCodim:97` `RepCoord d = Σ e : Fin N, Fin (d e.succ) × Fin (d e.castSucc)`.
- **`Core.Setup`/`Core.Submult`** — the tuple/edge conventions: which edge is the first factor (`A₁`,
  source side) and which is the last (`A_N`, target side) in `mult d A = A_N ··· A₁` (confirm the order
  + the `N = 1` coincidence where the single factor is BOTH endpoints).
- Synthesis §"G2-3 RECON VERDICT" (the endpoint normalization `Ã₁ = A₁H⁻¹`, `Ã_N = L⁻¹A_N`).

## The construction (general form)
For a chosen edge carrying an `m × n` matrix of variables and an **invertible** matrix `U` over the
coefficient ring `R`, right-multiplication `A ↦ A · U` is the coordinate substitution
`X_{(e,(i,j))} ↦ ∑_l U_{l,j} · X_{(e,(i,l))}` (an `R`-linear change of just that edge's variables);
left-multiplication `A ↦ U · A` is the analogous column/row variant. Both are `R`-algebra endomorphisms
of `MvPolynomial (RepCoord d) R`; composed with the substitution by `U⁻¹` they round-trip (the matrix
product collapses by `Matrix.mul_inv_cancel` / `nonsing_inv`). The endpoint normalization is: right-mult
the **first** factor by `H⁻¹`, left-mult the **last** factor by `L⁻¹`, all other edges fixed.

## Deliverables
1. `endpointSub d (e) (U : invertible over R) : MvPolynomial (RepCoord d) R →ₐ[R] …` (or a direct
   `AlgEquiv`) — the single-edge invertible-matrix coordinate change, with its inverse the `U⁻¹` change.
2. The **endpoint-normalization AlgEquiv** `endpointNormEquiv d r (H L invertible over R) :
   MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R` — first factor `· H⁻¹`, last factor
   `L⁻¹ ·` (handle the `N = 1` coincidence: both apply to the single factor, order matters).
3. The **mult-transport** lemma: under `endpointNormEquiv`, the generic product entries transform as
   `multPoly ↦ (L⁻¹ · multPoly · H⁻¹)` (i.e. `aeval (normalized coords) multPoly = (L⁻¹ M H⁻¹) entries`)
   — the bridge R2-3b-4 needs to turn `mult(A) = B = LEH` into `mult(Ã) = E`. State it cleanly; this is
   the payload (the AlgEquiv alone is just a coordinate change).

## SPECIFY-first — no-skip checkpoint
1. SPECIFY: pin the edge indexing (first/last factor + the `N = 1` coincidence), the substitution map,
   and the round-trip lemma (reduces to `H⁻¹H = 1`). Pin the Mathlib matrix-inverse API
   (`Matrix.nonsing_inv`, `mul_nonsing_inv`, or work with an explicit `Invertible U` / `U⁻¹` over `R`).
   Decide: parametrize by `[Invertible H]`/`[Invertible L]` (cleanest) vs `Matrix.GeneralLinearGroup`.
   Pre-stage the mult-transport with an `example`. **Fire a decorrelated `local-codex-consult` (xhigh)**
   on the substitution + the `N=1` endpoint coincidence; save under `threads/19-endpoint-normalization/codex/`.
2. **CHECKPOINT — report to `main`:** the pinned substitution + round-trip route + the mult-transport
   statement + reachability. Proceed if viable; if the indexing or the transport walls, CHECKPOINT a
   committed partial + report — do NOT grind / sorry.
3. PROVE (bank the single-edge substitution as a seam, then the endpoint equiv, then the transport) → AUDIT.

## Rules
`cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean` EVERY call (default
cwd = MAIN checkout, different branch); `scripts/lb` only (never bare `lake build`/`cache get`); NEVER
`git add -A`; commit partials (no untracked `.lean` left in the package — and **commit before going
idle**: don't leave finished work uncommitted in the working tree); zero sorry/axiom/native_decide/#exit;
`↦`; `decide +kernel`; name = content. **Core only — never import `DLNFibre.DLN`.** Don't edit the
aggregator — REPORT the import line. **You are the SOLE write-tide on `expedition/fibre-codimension`.**

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on the headline AlgEquiv + the
mult-transport = `[propext, Classical.choice, Quot.sound]`. Non-vacuity: the equiv + transport on a
concrete witness (`(2,2,2), r=1`, or `N=1` `dStratum 2 2` with `H = L = 1` reproducing the identity).

## Scope
**R2-3b-3 only** (the endpoint-normalization AlgEquiv + the mult-transport, GENERAL in `H`, `L`, `R`).
R2-3b-4 (instantiate `H`, `L` with the Schur-data unipotents + build `e : Sred ≃ₐ SchurLoc ⊗_k F_E` +
descend to the quotient — the hard rung) is the NEXT tide; R2-3a's `hSred` is **already discharged**
(`isReduced_Sred`), so b-4 needs only `e`. **No result here claims `codim=C+δ` or discharges
`BundleShiftInterface`.** Report to `main`: def/theorem names + signatures; green/sorries/axioms; module
path + aggregator line; the matrix-inverse API used; the exact residual handed to R2-3b-4; v4.29 friction.
