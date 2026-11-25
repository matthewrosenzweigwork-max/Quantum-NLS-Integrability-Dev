import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# LIB-075: bounded invertibility is preserved by adjoints

The inverse used below is Mathlib's totalized `ContinuousLinearMap.inverse`;
every use is justified by the actual `IsInvertible` hypothesis, which means
that the operator is the forward map of a continuous linear equivalence.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Atomic.LIB

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- If a bounded operator on a complete Hilbert space is invertible, then its
adjoint is invertible, with the adjoint of the genuine inverse as a two-sided
inverse. -/
private theorem adjoint_isInvertible_of_isInvertible (T : H →L[𝕜] H)
    (hT : T.IsInvertible) : T.adjoint.IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
  · rw [← ContinuousLinearMap.adjoint_comp, hT.inverse_comp_self,
      ContinuousLinearMap.adjoint_id]
  · rw [← ContinuousLinearMap.adjoint_comp, hT.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]

/-- A bounded operator on a real or complex complete Hilbert space is a
continuous linear equivalence exactly when its adjoint is. -/
theorem adjoint_isInvertible_iff (T : H →L[𝕜] H) :
    T.adjoint.IsInvertible ↔ T.IsInvertible := by
  constructor
  · intro hTadj
    have hT : T.adjoint.adjoint.IsInvertible :=
      adjoint_isInvertible_of_isInvertible T.adjoint hTadj
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hT
  · exact adjoint_isInvertible_of_isInvertible T

/-- Under the genuine bounded invertibility hypothesis, the adjoint of the
inverse is the inverse of the adjoint. -/
theorem inverse_adjoint_eq_adjoint_inverse (T : H →L[𝕜] H)
    (hT : T.IsInvertible) : T.inverse.adjoint = T.adjoint.inverse := by
  symm
  apply ContinuousLinearMap.inverse_eq
  · rw [← ContinuousLinearMap.adjoint_comp, hT.inverse_comp_self,
      ContinuousLinearMap.adjoint_id]
  · rw [← ContinuousLinearMap.adjoint_comp, hT.self_comp_inverse,
      ContinuousLinearMap.adjoint_id]

end NlsGge.Atomic.LIB
