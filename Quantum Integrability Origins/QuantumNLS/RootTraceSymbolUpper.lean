import Mathlib
import QuantumNLS.RootTraceSymbolFinal
import QuantumNLS.PhysicalUpperTraceIdentity

/-!
# R-7E0532E7 `eq:root-cos-phase`: the actual quantum cosine identity on the whole upper half-plane, unconditionally

`RootTraceSymbolFinal.traceSymbolIdentity` discharges the sole premise `PhysicalTraceSymbolDependency.TraceSymbolIdentity L κ u`
of Sol's `PhysicalUpperTraceIdentity.upper_cosine` (analytic continuation from the high half-plane, read-only).  Hence for
`κ > 0` and every nonzero physical `L²` class `u`, for every `z` with `Im z > 0`:

`2 cos (boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) z) = L2SpatialTransfer.discriminant κ u z`.

(The trace-symbol identity itself holds for every `z ∈ ℂ`, `RootTraceSymbolFinal.traceSymbol_all`.)
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace QuantumNLS.RootTraceSymbolUpper

open QuantumNLS.PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)]

theorem upper_cosine {κ : ℝ} (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    2 * Complex.cos (QuantumNLS.SpatialTransfer.boundaryPhase L κ
        (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) z) =
      QuantumNLS.L2SpatialTransfer.discriminant κ u z :=
  QuantumNLS.PhysicalUpperTraceIdentity.upper_cosine hκ hu
    (QuantumNLS.RootTraceSymbolFinal.traceSymbolIdentity hκ.le u) hz

end QuantumNLS.RootTraceSymbolUpper

#print axioms QuantumNLS.RootTraceSymbolUpper.upper_cosine
