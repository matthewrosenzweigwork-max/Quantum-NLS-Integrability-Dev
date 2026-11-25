import Mathlib
import NlsGge.Ramer.FiniteGaussian

                                                                                                                          
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

open NlsGge.Ramer

theorem finite_ramer_density_identity
    {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (K : V → V) (x : V) (hK : DifferentiableAt ℝ K x) :
    finiteRamerDensity (fun y : V => y + K y) x =
        |finiteDet2 (fderiv ℝ K x)| *
          Real.exp (-finiteGaussianDivergence K x - ‖K x‖ ^ 2 / 2) ∧
      |finiteDet2 (fderiv ℝ K x)| *
          Real.exp (-finiteGaussianDivergence K x - ‖K x‖ ^ 2 / 2) =
        |(fderiv ℝ (fun y : V => y + K y) x).det| *
          Real.exp ((‖x‖ ^ 2 - ‖x + K x‖ ^ 2) / 2) := by
  have hD : fderiv ℝ (fun y : V => y + K y) x =
      ContinuousLinearMap.id ℝ V + fderiv ℝ K x := by
    rw [fderiv_fun_add differentiableAt_fun_id hK, fderiv_fun_id]
  have key := abs_finiteDet2_mul_exp_eq (fderiv ℝ K x) x (K x)
  have e2 : |finiteDet2 (fderiv ℝ K x)| *
          Real.exp (-finiteGaussianDivergence K x - ‖K x‖ ^ 2 / 2) =
        |(fderiv ℝ (fun y : V => y + K y) x).det| *
          Real.exp ((‖x‖ ^ 2 - ‖x + K x‖ ^ 2) / 2) := by
    rw [hD]
    unfold finiteGaussianDivergence
    rw [key]
    congr 2
    ring
  refine ⟨?_, e2⟩
  rw [e2]
  unfold finiteRamerDensity
  congr 2
  ring

end
end NlsGge.ThirdConsultation.R
