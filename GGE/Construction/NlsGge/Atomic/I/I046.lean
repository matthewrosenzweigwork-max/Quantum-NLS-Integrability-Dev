import Mathlib
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38

                                                                                                                                          
                                                                                                                       
                                                                                                                                              
set_option autoImplicit false
open NlsGge.HierarchyRiccati.Core NlsGge.Pilot

namespace NlsGge.ThirdConsultation.I

theorem i046 (N : ℕ) (z : FourierPlane N) :
    (∀ (a : ℕ) (x : ℝ),
      ‖iteratedDeriv a (planeReal N z) x‖ ≤
        planeAmp38 z * (2 * Real.pi * (N : ℝ)) ^ a) ∧
    (∀ (k : ℕ) (q : Jet →₀ ℕ),
      riccatiJetWeightHomAfterComponents q = k → 1 ≤ degJ38 q →
      ∀ x : ℝ,
        (∏ i ∈ q.support, ‖riccatiJetFunction (planeReal N z) i x‖ ^ (q i)) ≤
          planeAmp38 z * planeK38 N z ^ (k - 1)) ∧
    (∀ j : ℕ, |localCharge38 (planeReal N z) j| ≤
      planeAmp38 z ^ 2 * (4 : ℝ) ^ (2 * j) * ((2 * j).factorial : ℝ) *
        planeK38 N z ^ (2 * j)) := by
  have hA : 0 ≤ planeAmp38 z := planeAmp38_nonneg z
  refine ⟨fun a x => ?_, fun k q hw hd x => ?_, fun j => ?_⟩
  · rw [iteratedDeriv_planeReal]
    refine (norm_planeReal_le38 N _ x).trans ?_
    unfold planeAmp38
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => norm_iterate_derivativePlane38 N z a i
  · exact monomial_norm_bound38 (fun v => riccatiJetFunction (planeReal N z) v x) (planeAmp38 z)
      (2 * Real.pi * (N : ℝ)) (planeK38 N z) hA (by positivity) (one_le_planeK38 N z)
      (le_max_of_le_right (le_max_right _ _)) (le_max_of_le_right (le_max_left _ _))
      (fun v => norm_riccatiJetFunction_planeReal_le38 N z v x) k q hw hd
  · exact localCharge38_plane_bound_all N j z

end NlsGge.ThirdConsultation.I
