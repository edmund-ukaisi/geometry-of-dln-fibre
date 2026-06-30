import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Measurable-space instance for matrices

This file exposes the basic measurable-space instance for finite matrix types
as the corresponding Pi measurable space.  It is intentionally independent of
the Aoyagi chart-topology development.
-/

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The measurable space on matrices is the Pi measurable space on entries. -/
instance instMeasurableSpaceMatrix {m n R : Type*} [MeasurableSpace R] :
    MeasurableSpace (Matrix m n R) :=
  inferInstanceAs (MeasurableSpace (m → n → R))

end Aoyagi
end DLN
end DLNFibre
