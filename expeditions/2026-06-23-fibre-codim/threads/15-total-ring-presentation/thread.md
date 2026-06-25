# thread 15 — R2-2 localized total-ring presentation (G2-3, formalisation / tide — the SWING factor)

**Type:** formalisation (tide) · `OPENED → SPECIFY/PROBE → CHECKPOINT(no-skip) → (PROVE) → AUDIT`.
The swing factor of G2-3 (the wall). Determines whether the total-presentation build is **M** (reuses
G2-2's machinery — then R2-3 stands on solid ground) or **L** (needs new scheme-free affine scaffolding —
then we certify R2-3's ideal-transport on paper before grinding). **Probe-first; checkpoint with the M/L
verdict before committing the full presentation.** Read the recon verdict in the synthesis (§"G2-3 RECON
VERDICT") + `threads/14-total-presentation-design/{thread.md, codex/q1q2-answer.md}` — that's your blueprint.

## Goal (a new `Core` module — e.g. `TotalRingPresentation.lean`)
Present the **localized total ring** `S := O(Σ̄^r ∩ chart)` as an explicit `R`-algebra quotient, where
`R := Sd` (G2-2's `SchurLoc`, the localized base ring). Concretely, on the pivot chart (detΔ of the
PRODUCT inverted):

> `S ≅ₐ[R] R[ tuple-factor entries ] / (mult(A) − B_univ)`  — the rep ring localized, modulo the cut
> ideal `(mult(A)=B)`, as an algebra over the base ring `R` via the localized comorphism.

This is the prerequisite for R2-3 (the endpoint-normalization `AlgEquiv` `S ≅ R ⊗_k F_E`). Deliverables:
1. The localized total ring `S` + the localized comorphism `R → S` (reuse G2-2's `blockAlgEquivLoc` /
   `IsLocalization.Away.mapₐ` scalar-tower pattern if it ports — THAT is the M/L question).
2. The quotient presentation `S ≅ R[factor entries]/(cut ideal)` (or the cut-ideal handle the AlgEquiv needs).

## SPECIFY/PROBE-first — no-skip checkpoint (the M/L verdict)
1. Probe whether the localized total-ring presentation reuses G2-2's `blockAlgEquivLoc`/`IsLocalization`
   scalar-tower machinery (⟹ **M**) or needs new affine-presentation scaffolding (⟹ **L**). Pin the exact
   statement + the cut-ideal handle. **Fire a decorrelated `local-codex-consult`** (authenticated, xhigh)
   on the presentation construction; save under `threads/15-total-ring-presentation/codex/`.
2. **CHECKPOINT — report to `main`: the M/L verdict + the pinned presentation + reachability.** If M
   (reuses G2-2), proceed to PROVE the presentation. If L (new scaffolding) OR the cut-ideal handle is
   unclear, STOP and report — the controller will route a pen-and-paper certification of the R2-3
   endpoint-normalization ideal-transport before any further formaliser work. Do NOT grind a doomed
   presentation or commit a `sorry`.
3. PROVE the presentation to green (if M), then AUDIT.

## Reuse (don't rebuild)
G2-2's `Core.DeterminantalBasePresentation` (`blockAlgEquivLoc`, `basePresentationEquiv` = R = Sd),
`Core.DeterminantalBaseElimination` (reindex, `blockAlgEquiv`, detΔ bridge), `Core.MultComorphism`
(`multPoly`/`multComap`/the fibre ideal), `Core.GraphIdealHeight`, the catenary/affine-domain engines.
The endpoint-normalization MATH (`mult(A)=B ⟺ mult(Ã)=E` via `Ã₁=A₁H⁻¹, Ã_N=L⁻¹A_N`) is verified exact
on the anchor — R2-3 formalizes it; R2-2 builds the presentation it transports.

## Rules
Build via `scripts/lb` from `…/fibre-codim/lean` (`cd` explicitly EVERY call — default cwd is the MAIN
checkout, a different live branch); NEVER bare `lake build`/`cache get`; NEVER `git add -A`. Zero
sorry/axiom/native_decide. `↦`; `decide +kernel`; one-line docstrings; name=content. **Core only — never
import `DLNFibre.DLN`.** Don't edit the aggregator — report the import line. Don't touch other worktrees.
Commit partials frequently (committed seams only). In-repo memory only.

## Scope
**Just R2-2** (the localized total-ring presentation + the M/L verdict). R2-3 (the endpoint-normalization
AlgEquiv — the wall), R2-4/5/6 are later. Report to `main`: the M/L verdict; if proved — theorem/def
names + signatures, green/sorries/axioms, module path + aggregator line; the decorrelated-Codex read;
v4.29 friction. CHECKPOINT before grinding if it's L.
