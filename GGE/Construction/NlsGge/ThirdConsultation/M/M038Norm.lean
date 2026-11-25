import NlsGge.Atomic.M.M006

                                                                                                
                                                                                                   
                                                                                             
                                                                  
set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M.M038Norm

open NlsGge.Pilot NlsGge.HierarchyRiccati.Core NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.M

theorem one_add_pow_le (m : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
  rcases le_total x 1 with h | h
  · have h1 : 1 + x ≤ 2 := by linarith
    have h2 : (1 + x) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) h1 m
    have h3 : (1 : ℝ) ≤ 1 + x ^ m := by linarith [pow_nonneg hx m]
    calc (1 + x) ^ m ≤ 2 ^ m := h2
      _ = 2 ^ m * 1 := (mul_one _).symm
      _ ≤ 2 ^ m * (1 + x ^ m) := mul_le_mul_of_nonneg_left h3 (by positivity)
  · have h1 : 1 + x ≤ 2 * x := by linarith
    have h2 : (1 + x) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    have h3 : x ^ m ≤ 1 + x ^ m := by linarith
    calc (1 + x) ^ m ≤ (2 * x) ^ m := h2
      _ = 2 ^ m * x ^ m := mul_pow 2 x m
      _ ≤ 2 ^ m * (1 + x ^ m) := mul_le_mul_of_nonneg_left h3 (by positivity)

theorem weight_eq (m : ℕ) (n : ℤ) :
    sobolevModeWeight (m : ℝ) n = (1 + (n : ℝ) ^ 2) ^ m := by
  unfold sobolevModeWeight japaneseBracket
  show Real.sqrt (1 + (n : ℝ) ^ 2) ^ (2 * (m : ℝ)) = (1 + (n : ℝ) ^ 2) ^ m
  rw [show (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2 by positivity)]

theorem bound_w (m : ℕ) (n : ℤ) :
    sobolevModeWeight (m : ℝ) n ≤ 2 ^ m * (1 + |(n : ℝ)| ^ (2 * m)) := by
  rw [weight_eq]
  have h1 := one_add_pow_le m ((n : ℝ) ^ 2) (sq_nonneg _)
  have h2 : ((n : ℝ) ^ 2) ^ m = |(n : ℝ)| ^ (2 * m) := by
    rw [pow_mul, sq_abs]
  rw [h2] at h1
  exact h1

theorem core (m : ℕ) (x : SobolevHilbert (m : ℝ)) (Z0 ZT : PhysicalL2)
    (h0 : ∀ n : ℤ, physicalFourier Z0 n =
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n)
    (hT : ∀ n : ℤ, physicalFourier ZT n =
      riccatiSobolevJetCoefficientL2Recovery28Second m m x n) :
    ‖x‖ ^ 2 ≤ 2 ^ m * (1 + ((2 * Real.pi) ^ (2 * m))⁻¹) * (‖Z0‖ ^ 2 + ‖ZT‖ ^ 2) := by
  have hpi : (2 * Real.pi) ^ (2 * m) ≠ 0 := by positivity
  have hsumX : HasSum (fun n : ℤ => sobolevModeWeight (m : ℝ) n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) (‖x‖ ^ 2) :=
    weightedHilbert_hasSum (sobolevModeWeight (m : ℝ))
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x)
  have hZ0 : HasSum (fun n : ℤ => ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2)
      (‖Z0‖ ^ 2) := by
    have e : (fun n : ℤ => ‖physicalFourier Z0 n‖ ^ 2) =
        fun n : ℤ => ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 :=
      funext fun n => congrArg (fun z : ℂ => ‖z‖ ^ 2) (h0 n)
    have h := hasSum_physicalFourier_sq Z0
    rw [e] at h
    exact h
  have hsqT : ∀ n : ℤ, ‖physicalFourier ZT n‖ ^ 2 =
      (2 * Real.pi) ^ (2 * m) *
        (|(n : ℝ)| ^ (2 * m) * ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
    intro n
    rw [hT n, riccatiSobolevJetCoefficient_norm_sqL2Recovery28Second]
    ring
  have hT2 : HasSum (fun n : ℤ => |(n : ℝ)| ^ (2 * m) *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2)
      (((2 * Real.pi) ^ (2 * m))⁻¹ * ‖ZT‖ ^ 2) := by
    have e : (fun n : ℤ => |(n : ℝ)| ^ (2 * m) *
        ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) =
        fun n : ℤ => ((2 * Real.pi) ^ (2 * m))⁻¹ * ‖physicalFourier ZT n‖ ^ 2 :=
      funext fun n => by
        rw [hsqT n, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
    rw [e]
    exact (hasSum_physicalFourier_sq ZT).mul_left (((2 * Real.pi) ^ (2 * m))⁻¹)
  have hG := (hZ0.mul_left (2 ^ m)).add (hT2.mul_left (2 ^ m))
  have hcmp : ∀ n : ℤ, sobolevModeWeight (m : ℝ) n *
      ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 ≤
      2 ^ m * ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 +
        2 ^ m * (|(n : ℝ)| ^ (2 * m) *
          ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2) := by
    intro n
    have hb := bound_w m n
    have hn : 0 ≤ ‖(show WeightedHilbert (sobolevModeWeight (m : ℝ)) from x) n‖ ^ 2 :=
      sq_nonneg _
    have hm := mul_le_mul_of_nonneg_right hb hn
    nlinarith [hm]
  have hmain := hasSum_le hcmp hsumX hG
  have h2m : (0 : ℝ) ≤ 2 ^ m := by positivity
  have hc0 : (0 : ℝ) ≤ ((2 * Real.pi) ^ (2 * m))⁻¹ := by positivity
  calc ‖x‖ ^ 2 ≤ 2 ^ m * ‖Z0‖ ^ 2 + 2 ^ m * (((2 * Real.pi) ^ (2 * m))⁻¹ * ‖ZT‖ ^ 2) := hmain
    _ ≤ 2 ^ m * (1 + ((2 * Real.pi) ^ (2 * m))⁻¹) * (‖Z0‖ ^ 2 + ‖ZT‖ ^ 2) := by
      nlinarith [mul_nonneg h2m (sq_nonneg ‖ZT‖), mul_nonneg (mul_nonneg h2m hc0) (sq_nonneg ‖Z0‖)]

theorem norm_sq_le (m : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ u : SobolevR m,
    ‖u‖ ^ 2 ≤ K * (topDerivativeNorm m u ^ 2 + ‖physicalOfSobolev u‖ ^ 2) := by
  refine ⟨2 ^ m * (1 + ((2 * Real.pi) ^ (2 * m))⁻¹), by positivity, fun u => ?_⟩
  have hx : ‖ordinarySobolevCoordinates m u‖ ^ 2 = ‖u‖ ^ 2 :=
    ordinarySobolevCoordinates_norm_sq m u
  have h0 : ∀ n : ℤ, physicalFourier (physicalOfSobolev u) n =
      (show WeightedHilbert (sobolevModeWeight (m : ℝ)) from ordinarySobolevCoordinates m u) n := by
    intro n
    unfold physicalOfSobolev
    rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier,
      riccatiSobolevJetCoefficientL2Recovery28Second, pow_zero, one_mul]
  have hT : ∀ n : ℤ, physicalFourier
      (riccatiSobolevIteratedDerivativeL2CLMRecovery30First m m le_rfl
        (ordinarySobolevCoordinates m u)) n =
      riccatiSobolevJetCoefficientL2Recovery28Second m m (ordinarySobolevCoordinates m u) n :=
    fun n => riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier m m le_rfl
      (ordinarySobolevCoordinates m u) n
  have h := core m (ordinarySobolevCoordinates m u) (physicalOfSobolev u)
    (riccatiSobolevIteratedDerivativeL2CLMRecovery30First m m le_rfl
      (ordinarySobolevCoordinates m u)) h0 hT
  rw [hx] at h
  refine h.trans (le_of_eq ?_)
  unfold topDerivativeNorm
  ring

end NlsGge.ThirdConsultation.M.M038Norm

end
