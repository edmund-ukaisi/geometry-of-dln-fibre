# thread 17 — R2-3 the trivialization AlgEquiv + route-(b) reducedness (G2-3, the wall — DE-RISKED)

**Type:** formalisation (tide) · `OPENED → SPECIFY → CHECKPOINT(no-skip) → PROVE → AUDIT`. The recon's
HIGH-risk rung, now **de-risked**: the load-bearing reducedness is CERTIFIED (thread 16 — `F_E` reduced,
`I_E` radical, 11-case Singular + Codex), and the route is fixed (route (b) deferred). This tide builds
the trivialization `AlgEquiv` and carries reducedness through it.

## Read first (your blueprint)
- **`threads/16-cut-ideal-radical/thread.md`** — the certificate: the reducedness verdict, the MECHANISM
  (reducedness descends from the reduced ambient rank locus via the trivialization), route (b), the
  engine handles, and the one Mathlib dependency to pin. **Authoritative.**
- Synthesis §"G2-3 RECON VERDICT" + §"THREAD 16 CERTIFICATE".
- `Core.DeterminantalBasePresentation` (R = `SchurLoc`, `blockAlgEquivLoc`), `Core.DeterminantalBaseElimination`
  (reindex, `blockAlgEquiv`, detΔ bridge), `Core.MultComorphism` (`multPoly`/`multComap`; **point 4**
  `vanishingIdeal(fibre)=radical(fibreGenIdeal)`), `Core.SigmaCodim`/`SigmaComponents` (`sigmaIdeal =
  vanishingIdeal`, RADICAL but REDUCIBLE on the chain — NOT prime; `minimalPrimes_sigmaIdeal_eq`),
  `Core.NullstellensatzCodim:69` (`vanishingIdeal_isRadical`).

## Deliverables
1. **The trivialization AlgEquiv `S ≅ₐ[R] R ⊗_k F_E`** (the core construction): on the pivot chart,
   `S = O(Σ̄^r ∩ chart)` (the reduced `Sred = (MvPol(RepCoord d) k ⧸ sigmaIdeal d r)[1/ΔP]`), `R = SchurLoc`,
   `F_E = k[Ã]/(mult(Ã)−E)`. Via the **endpoint normalization**: `Ã₁ = A₁H⁻¹`, `Ã_N = L⁻¹A_N` (H,L the
   unipotent factors of the target `B = L·E·H`; middles unchanged), so `mult(A)=B ⟺ mult(Ã)=E`, giving
   the product trivialization. The recon verified the LEH transport exact on the `(2,2,2),r=1` anchor;
   reuse `blockAlgEquivLoc`/`IsLocalization.Away.mapₐ` from G2-2.
2. **Route-(b) reducedness chain:** `Sred` reduced (`vanishingIdeal_isRadical`) → via (1) `R ⊗_k F_E`
   reduced → (k→R faithfully flat, char 0) `F_E` reduced → `I_E` radical. **Pin the Mathlib
   tensor-with-a-field reducedness-descent lemma EARLY** (the one open dependency — `Algebra.TensorProduct`
   / faithfully-flat `IsReduced` descent; char 0 ⟹ standard). The clean corollary: the radical-collapse
   of `MultComorphism` pt 4 — `fibreGenIdeal d B = vanishingIdeal(fibre d B)` (the `radical(...)` wrapper drops).
3. **(If quick — else R2-4)** free ⟹ flat: `F_E` free over `k` ⟹ `R ⊗_k F_E` free over `R` ⟹ `S` free
   over `R` ⟹ `Module.Flat R S` ⟹ `HasGoingDown` (the certificate: "one-liner once the AlgEquiv exists").

## SPECIFY-first — no-skip checkpoint
1. SPECIFY: pin the AlgEquiv statement + the endpoint-normalization construction (reuse G2-2's localized
   machinery) + the tensor-reducedness-descent Mathlib lemma (confirm the exact name). Pre-stage uncertain
   API with `example` blocks. **Fire a decorrelated `local-codex-consult`** (xhigh) on the AlgEquiv
   construction; save under `threads/17-trivialization-algequiv/codex/`.
2. **CHECKPOINT — report to `main`:** the pinned AlgEquiv construction + the confirmed tensor-descent
   lemma + reachability. Proceed to PROVE if viable. If the AlgEquiv construction walls (the endpoint
   normalization's localized ideal-transport), CHECKPOINT a committed partial + report — do NOT grind /
   sorry. (The reducedness is certified TRUE, so the only risk here is Lean-mechanical, not mathematical.)
3. PROVE (bank seams — the normalization auto, the comorphism, the product iso, the reducedness chain) → AUDIT.

## Rules
`cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean` explicitly EVERY call
(default cwd is the MAIN checkout, a live different branch); `scripts/lb` only; NEVER `git add -A`; commit
partials frequently (committed seams, no untracked `.lean` left in the package). Zero
sorry/axiom/native_decide. `↦`; `decide +kernel`; name=content. **Core only — never import `DLNFibre.DLN`.**
Don't edit the aggregator — report the import line. **You are the SOLE write-tide on this branch.**

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on the headline AlgEquiv =
`[propext, Classical.choice, Quot.sound]`. Witness: `(2,2,2),r=1` (`S ≅ R ⊗ F_E`, dims `7 = 3 + 4`).

## Scope
**R2-3** (the trivialization AlgEquiv + the route-(b) reducedness; flat/going-down if quick). R2-5
(`height m_B = δ` + minimal-prime relative-height-0) and R2-6 (`+C` assembly + reducibility fold) are
later tides. Report to `main`: theorem/def names + signatures; green/sorries/axioms; module path +
aggregator line; the tensor-descent lemma used; v4.29 friction.

---

## VERDICT (formalisation tide, 2026-06-24) — route-(b) chain DELIVERED; deep iso = R2-3b (deferred)

**Reachability:** the FULL deep `S ≃ₐ[R] R ⊗_k F_E` is a MULTI-TIDE wall, not one tide (decorrelated
xhigh Codex + my analysis converged). The engine has NO deep localized total ring — G2-2's
`blockAlgEquivLoc`/`basePresentationEquiv` are all `N=1` (single matrix `dStratum`); the deep `mult`
is a degree-N product whose rank ideal FACTORS, so the B22-graph trick does NOT port. No shorter route
to `F_E` reduced: reducedness does not descend through arbitrary quotients/special fibres
(`k[t,x]/(x²−t)` obstruction); the injection `R⊗F_E ↪ Sred` IS the hard half of the trivialization.

**Delivered (committed `91c77ff0`, card `996bb363`):** `lean/DLNFibre/Core/FibreReducedTrivialization.lean`
— the two ends of the route-(b) chain + the radical-collapse closer, wired against the trivialization
`e : S ≃ₐ[k] R ⊗_k F_B` + `IsReduced S` as an explicit HYPOTHESIS (not a sorry):
- `isReduced_of_tensor` — the tensor-with-a-field reducedness DESCENT (the one open dependency,
  now a proved Core lemma): `includeRight_injective` + `isReduced_of_injective`, needs only `[Nontrivial R]`.
- `fibreGenIdeal_isRadical_of_trivialization` — the full chain (S reduced → R⊗F reduced → F reduced →
  `fibreGenIdeal` radical).
- `vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization` — the radical-collapse of MultComorphism
  pt 4 (the `radical(·)` wrapper drops). The R2-5/R2-6 consumer.
Green, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`. Non-vacuity in-file.
**Aggregator line (main):** `import DLNFibre.Core.FibreReducedTrivialization`.

**Deferred → R2-3b:** the deep endpoint-normalization product iso `e` itself (new scheme-free affine
scaffolding). Fully de-risked downstream — every consumer of `e` is proved here against the hypothesis.
Codex's build order saved in `codex/algequiv-answer.md`.
