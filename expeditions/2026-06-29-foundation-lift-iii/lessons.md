# Lessons — `foundation-lift-iii`

The proven craft from #14 (dimension stack) and FL-II carries over — see
`expeditions/2026-06-29-foundation-lift/lessons.md` (L0–L5). The load-bearing ones to **apply every rung**:

- **L2 — transitive-consumer sweep.** After a namespace move, `rg` every moved identifier across all of
  `DLNFibre/` + full-build; transitive/unqualified consumers (no direct import) break only in the
  full-aggregator build.
- **L3 — gate next-rung dispatch on the prior formaliser's completion notification**, not a clean-tree
  snapshot (a formaliser can return for a review-driven follow-up + `git reset` and race a concurrent agent).
  Per-rung push + a strict build-gate + a clean committed base are the safety net.
- **L4 — `longLine` counts codepoints, not bytes** (`≤`/`≃`/`⟹` etc.); reflow against the linter's `:N:100`
  column.
- **L5 — under sustained box load, re-gate at phase boundaries + crux rungs, not every low-risk re-home.** For
  verbatim re-home rungs the formaliser's own fresh full-aggregator green is sufficient; the authoritative
  controller re-gate lands at the phase boundary + on the flagged crux rungs.

New lessons specific to this expedition accumulate below.

- **L6 — splitting a file can sever an *incidental transitive instance* import.** A monolithic file often
  acquires instances (`Module.Free`, `Module.Flat`, …) transitively via an import it needs for *one* half of
  its content. Splitting that half out severs the chain, so the other half loses instances it silently relied
  on — surfacing only in the full build, as a missing-instance error, not in the moved declaration's own text.
  Fix with the **honest minimal import** that actually provides the instance (here `Mathlib.LinearAlgebra.Basis.VectorSpace`
  → `Module.Free.of_divisionRing` → `Flat`), not by re-importing the heavy module the split removed. Generalises
  L2 (transitive *consumer* sweep) to transitive *instance-provider* breaks: a green full-aggregator build after
  a split is necessary, and a missing-instance error there is the expected symptom, not a regression.

- **L7 — a `DLNFibre.Core.X` namespace SHADOWS Mathlib's root `X` for files that `open X` inside
  `namespace DLNFibre.Core`.** P2.2's first home `DLNFibre.Core.AlgebraicGeometry.Group.Orbit` created a
  `DLNFibre.Core.AlgebraicGeometry` segment; three sibling files doing `open AlgebraicGeometry` from inside
  `namespace DLNFibre.Core` then resolved to the (empty) local segment, not Mathlib's — `Scheme`/`Spec`/etc.
  became "unknown identifier" only in the full build. **Rule:** a new file mirroring a Mathlib target declares
  its content in the **bare Mathlib-mirror namespace** (`namespace AlgebraicGeometry.Group.Orbit`, like
  `CotangentLocalization`'s `namespace Ideal` / `CotangentJacobian`'s `namespace MvPolynomial`), NOT a
  `DLNFibre.Core.`-prefixed one — both the correct eventual file-move target AND shadow-safe.
