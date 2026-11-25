import Mathlib
import NlsGge.Atomic.M.M009Support3
import NlsGge.Atomic.M.M009Support5

/- S4A PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target NlsGge/Atomic/M/M016CutFreeConnected.lean,
   namespace NlsGge.ThirdConsultation.MPrimitive (the namespace of cutFreeFiber; root may move it). Support for the M016
   complex chart, step 4 (S4a in proof development/M016CHART_STOP.md; no packet increment). Head VERBATIM from that STOP.
   ROUTE CHOICE: neither a new complement-of-segments topology proof nor h789's chain-constancy alternative is needed.
   The landed MPrimitive.cutFreeFiber_polygonal (M009Support3:230; built from the landed isolating family
   exists_isolating_family38) shows that any two points of the cut-free fiber are joined by a finite chain of straight
   segments inside the fiber, and the landed MPrimitive.polygonal_isPreconnected (M009Support5:28) turns that into
   preconnectedness. This is exactly the step used inside the landed M011Support1.good_of_good.
   Grep (2026-11-02): Mathlib d13f23b7 has complement-connectedness only for countable sets / subspaces of codim > 1
   (Set.Countable.isConnected_compl_of_one_lt_rank, isConnected_compl_of_one_lt_codim), which does not apply to
   segments; NlsGge has no exported `cutFreeFiber_isPreconnected`. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive

theorem cutFreeFiber_isPreconnected (φ : PotPair) (hφ : φ ∈ gkW) :
    IsPreconnected (NlsGge.ThirdConsultation.MPrimitive.cutFreeFiber φ) :=
  polygonal_isPreconnected (cutFreeFiber_polygonal φ hφ)

end NlsGge.ThirdConsultation.MPrimitive
