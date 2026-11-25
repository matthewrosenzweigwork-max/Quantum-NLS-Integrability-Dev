import NlsGge.Spectral.ComplexZsLocalPicardAnyInitialSourcePiV4
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false

noncomputable section

namespace NlsGge.SpectralFoundations

local instance vacuousMatrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedAddCommGroup

local instance vacuousMatrixNormedSpace :
    NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) :=
  instAnyInitialSourcePiNormedSpace

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivWithinAt_matrix_of_notMem_closure
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Matrix (Fin 2) (Fin 2) ℂ) (s : Set ℝ) (x : ℝ)
    (h : x ∉ closure s) : HasDerivWithinAt F v s x := by
  have hF : HasFDerivWithinAt F
      (ContinuousLinearMap.toSpanSingleton ℝ v) s x :=
    HasFDerivWithinAt.of_notMem_closure h
  simpa using hF.hasDerivWithinAt

end NlsGge.SpectralFoundations

end
