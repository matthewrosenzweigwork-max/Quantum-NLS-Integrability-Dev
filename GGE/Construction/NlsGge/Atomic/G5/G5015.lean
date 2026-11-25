import Mathlib
import NlsGge.Atomic.G5.G5012
import NlsGge.Atomic.G5.G5012Sup2
import NlsGge.Atomic.G5.G5013
import NlsGge.Atomic.G5.G5014
import NlsGge.Atomic.G1.G1086
import NlsGge.Atomic.LIB.LIB022

                                                                                                                  
                                                                                                                            
                                                                         
                                                                                                                            
                                                                                                                    
                                                                                                                           
                                                                                                                      
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5015_weight_zero (x : ℂ) (n : ℤ) :
    Real.rpow (japaneseBracket n) (2 * (0 : ℝ)) * ‖x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [mul_zero, Real.rpow_eq_pow, Real.rpow_zero, one_mul]

theorem g5015_sq_summable (u : PhysicalL2) :
    Summable (fun n : ℤ => ‖reflectedFourierL2 u n‖ ^ 2) := by
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp (reflectedFourierL2 u).2
  simpa using h

theorem g5015_sobolev_zero (u : PhysicalL2) : physicalSobolev 0 u := by
  unfold physicalSobolev SobolevSquareSummable
  simp only [g5015_weight_zero]
  exact g5015_sq_summable u

theorem g5015_norm_zero (w : PhysicalL2) : physicalSobolevNorm 0 w = ‖w‖ := by
  unfold physicalSobolevNorm
  simp only [g5015_weight_zero]
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (reflectedFourierL2 w)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _), LinearIsometryEquiv.norm_map]

theorem g5015_approx_of
    (hd : ∀ r : ℝ, 0 ≤ r → ∀ u : PhysicalL2,
      physicalSobolev r u → ∀ ε : ℝ, 0 < ε →
      ∃ v : PhysicalL2,
        finiteGap v ∧ physicalSobolev r v ∧
        physicalSobolevNorm r (v-u) < ε)
    (u : PhysicalL2) :
    ∃ v : ℕ → PhysicalL2, Tendsto v atTop (𝓝 u) ∧ ∀ k : ℕ, finiteGap (v k) := by
  have hex : ∀ k : ℕ, ∃ v : PhysicalL2, finiteGap v ∧ ‖v - u‖ < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨v, hv, -, hn⟩ := hd 0 le_rfl u (g5015_sobolev_zero u) (1 / ((k : ℝ) + 1))
      Nat.one_div_pos_of_nat
    rw [g5015_norm_zero] at hn
    exact ⟨v, hv, hn⟩
  choose v hv hvn using hex
  refine ⟨v, ?_, hv⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hvn k).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

theorem g5015_approx (u : PhysicalL2) :
    ∃ v : ℕ → PhysicalL2, Tendsto v atTop (𝓝 u) ∧ ∀ k : ℕ, finiteGap (v k) :=
  g5015_approx_of G1_086.2 u

theorem g5015_hs_compact (v : PhysicalL2)
    (hs : Summable (fun j : Bool × ℤ =>
      ‖(jacobianAdjoint v - ContinuousLinearMap.id ℝ PhysicalL2) (physicalFourierBasis j)‖ ^ 2)) :
    IsCompactOperator (jacobianAdjoint v - ContinuousLinearMap.id ℝ PhysicalL2) := by
  refine NlsGge.Atomic.G5.compact_of_hilbertSchmidt physicalFourierHilbertBasis _ ?_
  simpa only [physicalFourierHilbertBasis_apply] using hs

theorem g5015_compact_of_limit (u : PhysicalL2) (v : ℕ → PhysicalL2)
    (hv : Tendsto v atTop (𝓝 u)) (hcont : Continuous jacobianAdjoint)
    (hK : ∀ k : ℕ, IsCompactOperator (jacobianAdjoint (v k) - ContinuousLinearMap.id ℝ PhysicalL2)) :
    IsCompactOperator (jacobianAdjoint u - ContinuousLinearMap.id ℝ PhysicalL2) := by
  have hT : Tendsto (fun k : ℕ => jacobianAdjoint (v k) - ContinuousLinearMap.id ℝ PhysicalL2) atTop
      (𝓝 (jacobianAdjoint u - ContinuousLinearMap.id ℝ PhysicalL2)) :=
    ((hcont.tendsto u).comp hv).sub_const _
  exact NlsGge.Atomic.compact_of_operatorNorm_limit hK hT

theorem G5015 (u : PhysicalL2) :
  IsCompactOperator (jacobianAdjoint u - ContinuousLinearMap.id ℝ PhysicalL2) := by
  obtain ⟨v, hv, hfg⟩ := g5015_approx u
  exact g5015_compact_of_limit u v hv G5012.2.1 (fun k => g5015_hs_compact (v k) (G5013 (v k) (hfg k)))

end
end NlsGge.GKDefinitionDesign
