import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.Clopen

namespace NlsGge.Atomic.LIB085

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty clopen subset of a real normed space is the whole space.

The imported `NormedSpace.instPathConnectedSpace` is Mathlib's straight-segment
construction: it applies `Convex.isPathConnected` to `univ`, whose paths are
`Path.segment x y`. -/
theorem nonempty_clopen_eq_univ {U : Set E}
    (hU : IsClopen U) (hne : U.Nonempty) : U = Set.univ :=
  hU.eq_univ hne

end NlsGge.Atomic.LIB085
