import Mathlib.Data.Matrix.Basic

/-!
# `DLNFibre.Core` — the engine (network-free)

The reusable core: the geometry of tuples of composable matrices via type-A quiver
representations — orbits ↔ Kostant partitions ↔ rank patterns, the orbit-closure order, and the
`Ext` codimension that yields the codimension `C` and the number `θ` of top-dimensional components.

**Dependency rule:** `DLNFibre.Core` must never import `DLNFibre.DLN`. The arrows point
`DLN → Core → Mathlib`. Keeping `Core` network-free is what makes it reusable on its own
(and extractable to a standalone package later if a second consumer appears).

Stub — populated by the formalisation expeditions; see `../../theory/setup.md` and `ROADMAP.md`.
-/

namespace DLNFibre.Core

end DLNFibre.Core
