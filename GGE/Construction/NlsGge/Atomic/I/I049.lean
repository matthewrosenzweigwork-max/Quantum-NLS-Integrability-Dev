import Mathlib
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Hierarchy.FullEnergyExistenceW01_38
import NlsGge.Hierarchy.RelativePartition38

                                                                                           
                                                                                                              
                                                                     
set_option autoImplicit false
open NlsGge.HierarchyRiccati.Core NlsGge.Pilot

namespace NlsGge.ThirdConsultation.I
noncomputable section

theorem i049 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ c : BoundedCoefficients 1 2,
        (∀ z : FourierPlane N,
          (∀ i : Fin (2 * N + 1), ‖z i‖ ≤
            Real.exp (-(20 * Real.pi * ((N : ℝ) + 1))) / (2 * (N : ℝ) + 1)) →
          fullEnergy38 c N z ≤ 1) ∧
        Real.exp (-(C * (N : ℝ) ^ 2)) ≤ fullPartition38 c N := by
  obtain ⟨C, hC, h⟩ := partition_lower_bochner38
  refine ⟨C, hC, fun N hN c => ⟨fun z hz => ?_, h N hN c⟩⟩
  refine energy_le_one_on_small38 N hN c z ?_
  have hd : (0:ℝ) < 2 * (N : ℝ) + 1 := by positivity
  have hsum : planeAmp38 z ≤ ∑ _i : Fin (2 * N + 1),
      Real.exp (-(20 * Real.pi * ((N : ℝ) + 1))) / (2 * (N : ℝ) + 1) :=
    Finset.sum_le_sum fun i _ => hz i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
  rw [hcast, mul_div_cancel₀ _ hd.ne'] at hsum
  exact hsum

end
end NlsGge.ThirdConsultation.I
