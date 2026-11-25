import NlsGge.GK38.AbelianActualGlobalSolution
import NlsGge.GK38.AbelianSolutionProjectionRigidity

/-! Uncompiled concrete pointwise rigidity with actual P4 inverse discharge. -/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5Actual_gap_solution_pointwise_unique38 (n : ℤ) (u : PhysicalL2) :
    ∃! t : P3RealSpace38 n, t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t=0 :=
  p5Actual_gap_solution_pointwise_unique_of_inverse38 n (p5ActualSolution_real_inverse38 n) u

theorem p5Actual_solution_projection_homeomorph38 (n : ℤ) :
    ∃ H : p5RealSolutionSpace38 n ≃ₜ PhysicalL2,
      (H : p5RealSolutionSpace38 n → PhysicalL2)=p5RealSolutionProjection38 n :=
  p5SolutionProjection_homeomorph_of_actual_inverse38 n (p5ActualSolution_real_inverse38 n)

end
end NlsGge.GK38
