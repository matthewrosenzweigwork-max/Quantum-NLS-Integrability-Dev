import Mathlib
import NlsGge.Atomic.KSN.KSN012Host

                                                                                                                             
                                                                                                                    
                                                                                                            
                                                                                                              
                                                                                                          
                                                                                                             
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn018_scaleWeight_pos (s : ℝ) (n : ℤ) : 0 < scaleWeight s n := by
  unfold scaleWeight bracket
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) s

theorem ksn018_ratio_le (N : ℕ) (hN : 1 ≤ N) (n : ℤ) : scaleWeight 1 n / scaleWeight (N : ℝ) n ≤ 1 := by
  rw [div_le_one (ksn018_scaleWeight_pos _ n)]
  unfold scaleWeight
  exact Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) (by exact_mod_cast hN)

/-- The lowered stored coefficient. -/
def ksn018_lowerFun (N : ℕ) (x : PairScale (N : ℝ)) (j : Bool × ℤ) : ℂ :=
  ((scaleWeight 1 j.2 / scaleWeight (N : ℝ) j.2 : ℝ) : ℂ) * x j

theorem ksn018_lowerFun_norm_le (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ)) (j : Bool × ℤ) :
    ‖ksn018_lowerFun N x j‖ ≤ ‖x j‖ := by
  unfold ksn018_lowerFun
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (div_nonneg (ksn018_scaleWeight_pos _ _).le (ksn018_scaleWeight_pos _ _).le)]
  exact mul_le_of_le_one_left (norm_nonneg _) (ksn018_ratio_le N hN j.2)

theorem ksn018_lowerFun_mem (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ)) :
    Memℓp (ksn018_lowerFun N x) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  have h := (memℓp_gen_iff hp).1 x.2
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) h
  exact Real.rpow_le_rpow (norm_nonneg _) (ksn018_lowerFun_norm_le N hN x j) hp.le

/-- The lowering map as a continuous ℂ-linear map of norm ≤ 1. -/
def ksn018_lower (N : ℕ) (hN : 1 ≤ N) : PairScale (N : ℝ) →L[ℂ] PairScale 1 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨ksn018_lowerFun N x, ksn018_lowerFun_mem N hN x⟩
      map_add' := fun x y => by
        ext j
        simp only [ksn018_lowerFun, lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        ext j
        simp only [ksn018_lowerFun, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    1 (fun x => by
      rw [one_mul]
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      refine lp.norm_le_of_forall_sum_le hp (norm_nonneg _) (fun s => ?_)
      have hx := lp.sum_rpow_le_norm_rpow hp x s
      refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) hx
      exact Real.rpow_le_rpow (norm_nonneg _) (ksn018_lowerFun_norm_le N hN x j) hp.le)

theorem ksn018_lower_apply (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ)) (j : Bool × ℤ) :
    ksn018_lower N hN x j = ksn018_lowerFun N x j := rfl

theorem ksn018_lower_norm_le (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ)) :
    ‖ksn018_lower N hN x‖ ≤ ‖x‖ := by
  have h := (ksn018_lower N hN).le_opNorm x
  have h1 : ‖ksn018_lower N hN‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  calc ‖ksn018_lower N hN x‖ ≤ ‖ksn018_lower N hN‖ * ‖x‖ := h
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖x‖ := one_mul _

theorem ksn018_raw_lower (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ)) (b : Bool) (n : ℤ) :
    rawCoefficient 1 (ksn018_lower N hN x) b n = rawCoefficient (N : ℝ) x b n := by
  unfold rawCoefficient
  rw [ksn018_lower_apply]
  unfold ksn018_lowerFun
  have h1 : ((scaleWeight 1 n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ksn018_scaleWeight_pos 1 n).ne'
  have h2 : ((scaleWeight (N : ℝ) n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ksn018_scaleWeight_pos (N : ℝ) n).ne'
  push_cast
  field_simp

theorem ksn018_pairPotential_lower (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ)) :
    pairPotential 1 (by norm_num) (ksn018_lower N hN x) = pairPotential (N : ℝ) (Nat.cast_nonneg N) x := by
  unfold pairPotential
  refine Prod.ext ?_ ?_
  · show physicalFourierL2.symm _ = physicalFourierL2.symm _
    congr 1
    exact Subtype.ext (funext fun n => ksn018_raw_lower N hN x true n)
  · show physicalFourierL2.symm _ = physicalFourierL2.symm _
    congr 1
    exact Subtype.ext (funext fun n => ksn018_raw_lower N hN x false n)

theorem ksn018_lower_mem_complexDomain (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ))
    (hx : x ∈ complexDomain (N : ℝ) (Nat.cast_nonneg N)) :
    ksn018_lower N hN x ∈ complexDomain 1 (by norm_num) := by
  show pairPotential 1 (by norm_num) (ksn018_lower N hN x) ∈ sourceBetaW
  rw [ksn018_pairPotential_lower]; exact hx

theorem ksn018_lower_isRealPair (N : ℕ) (hN : 1 ≤ N) (x : PairScale (N : ℝ))
    (hx : IsRealPair (N : ℝ) x) : IsRealPair 1 (ksn018_lower N hN x) := by
  intro n
  rw [ksn018_raw_lower, ksn018_raw_lower]
  exact hx n

end
end NlsGge.ThirdConsultation.KSN
