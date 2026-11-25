import Mathlib
import NlsGge.Spectral.F04LiteralBounds38
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import NlsGge.NLS38.PhysicalFlow38
import NlsGge.Schur.PhysicalH1ComplexCarrierSchurBridge
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.WeightedHilbert

                                                                                                                      
                                                                                                                            
                                                                                                                  
                                                                                                                      
set_option autoImplicit false

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.HierarchyRiccati.Core NlsGge.NLS38 NlsGge.Schur
open Set Filter Topology

namespace NlsGge.ThirdConsultation.F
noncomputable section

namespace F005Aux

theorem rate_eq_weight (m : ℕ) (β : ℕ → ℝ) (n : ℤ) :
    finiteHierarchyRate38 m β n = finiteWeightE02_38 m β (2 * Real.pi * n) := by
  unfold finiteHierarchyRate38 finiteHierarchyW38 finiteWeightE02_38
  rfl

theorem exists_weighted_preimage (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∃ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)),
      physicalH1ComplexCarrierToL2Actual22 w = u ∧ ‖w‖ = ‖physicalSobolevL2 1 u hu‖ := by
  have hw : ∀ n : ℤ, 0 ≤ sobolevModeWeight (1 : ℝ) n := fun n =>
    (Real.rpow_pos_of_pos (japaneseBracket_pos n) _).le
  have hmem : physicalFourier u ∈ weightedSubmodule (sobolevModeWeight (1 : ℝ)) :=
    (weightedCoordinates_mem_l2_iff (sobolevModeWeight (1 : ℝ)) hw (physicalFourier u)).2 hu
  let w : WeightedHilbert (sobolevModeWeight (1 : ℝ)) := ⟨physicalFourier u, hmem⟩
  refine ⟨w, ?_, ?_⟩
  · apply physicalFourier_injective38
    funext n
    rw [physicalH1ComplexCarrierToL2Actual22_fourier]
  · have h1 := weightedHilbert_hasSum (sobolevModeWeight (1 : ℝ)) w
    have h2 := physicalSobolevL2_norm_sq 1 u hu
    have h3 : ‖w‖ ^ 2 = ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
      rw [h2]
      exact h1.tsum_eq.symm
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h3

end F005Aux

open F005Aux in
theorem f005 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ B → ∀ n : ℤ,
        ∀ lam ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
          |finiteWeightE02_38 m β (2 * lam) - finiteHierarchyRate38 m β n| ≤
            C * finiteHierarchyRate38 m β n / japaneseBracket n ^ 2 := by
  obtain ⟨C, hC, hCb⟩ := finiteWeight_gap_rel_le38 m β hβ (max 1 B) (le_max_left 1 B)
  refine ⟨C, hC, fun u hu hnorm n lam hl => ?_⟩
  obtain ⟨w, hΦ, hnw⟩ := F005Aux.exists_weighted_preimage u hu
  have hwB : ‖w‖ ≤ max 1 B := by
    rw [hnw]; exact hnorm.trans (le_max_right 1 B)
  subst hΦ
  have key := hCb w hwB n lam hl
  rw [F005Aux.rate_eq_weight]
  exact key

end
end NlsGge.ThirdConsultation.F

