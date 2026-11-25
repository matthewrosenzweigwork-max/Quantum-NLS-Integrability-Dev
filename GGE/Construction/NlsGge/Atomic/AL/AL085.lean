import Mathlib
import NlsGge.Atomic.AL.AL080
import NlsGge.Hierarchy.ALFreeFields38

                                                                               
                                                
                                                                                                 
                                                                                            
                                                                                      
                                                                                               
                                                                                                 
set_option autoImplicit false

open NlsGge.Pilot NlsGge.AblowitzLadik NlsGge.Weights Filter Topology

namespace NlsGge.ThirdConsultation.AL

theorem al085 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (s : ℝ) :
    let b : ℕ → ℝ := fun N =>
      alEdgeRatio38 c.val N * sobolevModeWeight (-s) (N : ℤ)
    Tendsto b atTop atTop ∧
    ∀ᶠ N : ℕ in atTop, 0 < b N ∧ ∀ g : ℤ → ℂ,
      b N * ‖g (N : ℤ)‖ ^ 2 ≤ alESqNorm38 c.val s N g := by
  intro b
  have hA := al080Aux.admissible c
  refine ⟨alEdgeCoeff_tendsto_top38 hA s, ?_⟩
  have hcpos : ∀ k : ℤ, 0 < alRateCont38 c.val k := fun k =>
    (alRateComp_pos38 hA k).trans_le (alRateComp_le_cont38 hA k)
  have hwpos : ∀ k : ℤ, 0 < sobolevModeWeight (-s) k := fun k =>
    (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight (-s) n)).out k
  filter_upwards [alRateFree_ge38 hA] with N hN
  have hfN : 0 < alRateFree38 c.val N (N : ℤ) := by
    have h := hN (N : ℤ) (by simp)
    have h2 := alRateComp_pos38 hA (N : ℤ)
    linarith
  have hbpos : 0 < b N := by
    show 0 < alEdgeRatio38 c.val N * sobolevModeWeight (-s) (N : ℤ)
    unfold alEdgeRatio38
    exact mul_pos (div_pos (hcpos _) hfN) (hwpos _)
  refine ⟨hbpos, fun g => ?_⟩
  have hnonneg : ∀ k ∈ Finset.Icc (-(N : ℤ)) N,
      0 ≤ alRateCont38 c.val k * sobolevModeWeight (-s) k * ‖alUhCoef38 c.val N g k‖ ^ 2 :=
    fun k _ => mul_nonneg (mul_nonneg (hcpos k).le (hwpos k).le) (sq_nonneg _)
  have hmem : (N : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := Finset.mem_Icc.2 ⟨by omega, le_rfl⟩
  have hle := Finset.single_le_sum hnonneg hmem
  have hU : alUhCoef38 c.val N g (N : ℤ) = g (N : ℤ) / ((Real.sqrt (alRateFree38 c.val N (N : ℤ)) : ℝ) : ℂ) := by
    unfold alUhCoef38
    rw [if_pos (by simp)]
  have hnorm : ‖alUhCoef38 c.val N g (N : ℤ)‖ ^ 2 = ‖g (N : ℤ)‖ ^ 2 / alRateFree38 c.val N (N : ℤ) := by
    rw [hU, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt hfN.le]
  have heq : b N * ‖g (N : ℤ)‖ ^ 2 =
      alRateCont38 c.val (N : ℤ) * sobolevModeWeight (-s) (N : ℤ) * ‖alUhCoef38 c.val N g (N : ℤ)‖ ^ 2 := by
    rw [hnorm]
    show alEdgeRatio38 c.val N * sobolevModeWeight (-s) (N : ℤ) * ‖g (N : ℤ)‖ ^ 2 = _
    unfold alEdgeRatio38
    field_simp
  unfold alESqNorm38
  rw [heq]
  exact hle

end NlsGge.ThirdConsultation.AL
