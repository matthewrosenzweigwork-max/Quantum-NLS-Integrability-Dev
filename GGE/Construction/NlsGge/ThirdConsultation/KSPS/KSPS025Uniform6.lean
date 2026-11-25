import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU3
import NlsGge.ThirdConsultation.KSPS.KSPS023Host

                                                                                 
                                                                                                             
                                                                                                            
                                                                                                                     
                                                                                                       
                                                                                                               
                                                                                                                
                                                                                        
                                                                                       
                                                                                                                        
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS025U6
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS
open Metric

theorem phasePoly_le {N : ℕ} (φ : SobolevC N) (j : ℕ) (L : ℝ)
    (hI : ∀ k ∈ Finset.Icc 1 j, ‖integralRiccatiLeft φ k‖ ≤ L) (w : ℂ) (hw : ‖w‖ ≤ 1) :
    ‖NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ j w‖ ≤ j * L * ‖w‖ := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial
  rw [norm_mul, Complex.norm_I, one_mul]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.Icc 1 j,
      ‖((2 * Complex.I) ^ k)⁻¹ * integralRiccatiLeft φ k * w ^ k‖ ≤ L * ‖w‖ := by
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hc : ‖((2 * Complex.I) ^ k)⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_pow, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hwk : ‖w‖ ^ k ≤ ‖w‖ := pow_le_of_le_one (norm_nonneg _) hw (by omega)
    have hL : 0 ≤ L := (norm_nonneg _).trans (hI k hk)
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖((2 * Complex.I) ^ k)⁻¹‖ * ‖integralRiccatiLeft φ k‖ * ‖w‖ ^ k
        ≤ 1 * L * ‖w‖ := by
          apply mul_le_mul (mul_le_mul hc (hI k hk) (norm_nonneg _) zero_le_one) hwk
            (pow_nonneg (norm_nonneg _) _) (by positivity)
      _ = L * ‖w‖ := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  push_cast
  ring

theorem phasePoly_differentiable {N : ℕ} (φ : SobolevC N) (j : ℕ) :
    Differentiable ℂ (NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ j) := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial
  exact (differentiable_const _).mul (Differentiable.fun_sum (fun k _ =>
    (differentiable_const _).mul (differentiable_pow k)))

theorem iterate_zero {N : ℕ} (φ : SobolevC N) :
    NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ 0 = fun _ => 0 := rfl

theorem iterate_succ {N : ℕ} (φ : SobolevC N) (j : ℕ) :
    NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ (j + 1) = fun z =>
      -NlsGge.ThirdConsultation.KSPSRiccati.phasePolynomial φ (j + 1)
        (z / ((Real.pi : ℂ) + z * NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ j z)) := rfl

/-- The iterates are differentiable and bounded by one on the disc of radius `1/(K L + 1)`. -/
theorem iterate_bound {N : ℕ} (φ : SobolevC N) (K : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hI : ∀ k : ℕ, 1 ≤ k → k ≤ K → ‖integralRiccatiLeft φ k‖ ≤ L) :
    ∀ j : ℕ, j ≤ K → ∀ z : ℂ, ‖z‖ < 1 / (K * L + 1) →
      ‖NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ j z‖ ≤ 1 ∧
      DifferentiableAt ℂ (NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ j) z := by
  have hKL : 0 ≤ (K : ℝ) * L := by positivity
  have hR1 : 1 / ((K : ℝ) * L + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  intro j
  induction j with
  | zero =>
    intro _ z _
    rw [iterate_zero]
    exact ⟨by simp, differentiableAt_const _⟩
  | succ j ih =>
    intro hj z hz
    obtain ⟨hb, hd⟩ := ih (by omega) z hz
    set ζ := NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ j with hζ
    have hz1 : ‖z‖ ≤ 1 := hz.le.trans hR1
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hzζ : ‖z * ζ z‖ ≤ 1 := by
      rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg (ζ z)]
    have hden : 2 ≤ ‖(Real.pi : ℂ) + z * ζ z‖ := by
      have h1 := norm_sub_norm_le ((Real.pi : ℂ)) (-(z * ζ z))
      rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at h1
      linarith
    have hden0 : (Real.pi : ℂ) + z * ζ z ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hden; linarith
    have hw : ‖z / ((Real.pi : ℂ) + z * ζ z)‖ ≤ ‖z‖ / 2 := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
    have hw1 : ‖z / ((Real.pi : ℂ) + z * ζ z)‖ ≤ 1 := hw.trans (by linarith)
    have hP := phasePoly_le φ (j + 1) L
      (fun k hk => hI k (Finset.mem_Icc.mp hk).1 ((Finset.mem_Icc.mp hk).2.trans hj)) _ hw1
    refine ⟨?_, ?_⟩
    · rw [iterate_succ, norm_neg]
      refine hP.trans ?_
      have hjK : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hj
      have hz2 : ‖z‖ * ((K : ℝ) * L + 1) < 1 := by
        rwa [lt_div_iff₀ (by linarith)] at hz
      have h3 : ((j + 1 : ℕ) : ℝ) * L ≤ K * L := mul_le_mul_of_nonneg_right hjK hL
      have h4 : ((j + 1 : ℕ) : ℝ) * L * ‖z / ((Real.pi : ℂ) + z * ζ z)‖ ≤ K * L * (‖z‖ / 2) :=
        mul_le_mul h3 hw (norm_nonneg _) hKL
      nlinarith [norm_nonneg z]
    · rw [iterate_succ]
      have hinner : DifferentiableAt ℂ (fun z => z / ((Real.pi : ℂ) + z * ζ z)) z :=
        differentiableAt_id.div ((differentiableAt_const _).add (differentiableAt_id.mul hd)) hden0
      exact ((phasePoly_differentiable φ (j + 1)).differentiableAt.comp z hinner).neg

/-- Cauchy's estimate for the inverse-phase coefficients. -/
theorem spectralCoefficient_le {N : ℕ} (φ : SobolevC N) (K : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hI : ∀ k : ℕ, 1 ≤ k → k ≤ K → ‖integralRiccatiLeft φ k‖ ≤ L) (k : ℕ) (hk : k ≤ K) :
    ‖NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k‖ ≤ (2 * (K * L + 1)) ^ k := by
  have hKL : 0 ≤ (K : ℝ) * L := by positivity
  set R0 : ℝ := 1 / (K * L + 1) with hR0
  have hR0p : 0 < R0 := by positivity
  set r : ℝ := R0 / 2 with hr
  have hrp : 0 < r := by positivity
  have hb := iterate_bound φ K L hL hI k hk
  have hdiff : DiffContOnCl ℂ (NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ k) (ball 0 r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball (0 : ℂ) hrp.ne']
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    exact (hb z (by linarith)).2.differentiableWithinAt
  have hC : ∀ z ∈ sphere (0 : ℂ) r,
      ‖NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ k z‖ ≤ 1 := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    exact (hb z (by linarith)).1
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hrp hdiff hC
  unfold NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient
  have hf : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hf]
  have hrinv : (2 * ((K : ℝ) * L + 1)) = 1 / r := by
    rw [hr, hR0]; field_simp
  rw [hrinv, one_div, inv_pow]
  calc ‖iteratedDeriv k (NlsGge.ThirdConsultation.KSPSRiccati.inversePhaseIterate φ k) 0‖
      ≤ (k.factorial : ℝ) * 1 / r ^ k := hcau
    _ = (r ^ k)⁻¹ * (k.factorial : ℝ) := by ring

/-- Ball-uniform bound of the inverse-phase coefficients of orders `k ≤ N + 1`. -/
theorem spectralCoefficient_uniform (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ k : ℕ, k ≤ N + 1 →
      ‖NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k‖ ≤ D := by
  obtain ⟨L, hL, hIb⟩ := NlsGge.ThirdConsultation.KSPSU3.integralRiccatiLeft_uniform N hN B₀ hB₀
  set q : ℝ := 2 * (((N + 1 : ℕ) : ℝ) * L + 1) with hq
  have hq1 : 1 ≤ q := by
    have : 0 ≤ ((N + 1 : ℕ) : ℝ) * L := by positivity
    linarith
  refine ⟨q ^ (N + 1), by positivity, fun φ hφ k hk => ?_⟩
  refine (spectralCoefficient_le φ (N + 1) L hL (fun j h1 h2 => hIb φ hφ j h1 h2) k hk).trans ?_
  exact pow_le_pow_right₀ hq1 hk

theorem div_pow_norm_le (c : ℂ) (n : ℤ) (k : ℕ) (hk : 1 ≤ k) : ‖c / (n : ℂ) ^ k‖ ≤ ‖c‖ := by
  by_cases hn : n = 0
  · subst hn
    rw [Int.cast_zero, zero_pow (by omega), div_zero, norm_zero]
    exact norm_nonneg _
  · rw [norm_div, norm_pow, Complex.norm_intCast]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    exact div_le_self (norm_nonneg _) (one_le_pow₀ h1)

/-- Ball-uniform bound of `spectralPolynomial φ n - n π` at every label. -/
theorem spectralPolynomial_sub_le (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ → ∀ n : ℤ,
      ‖spectralPolynomial φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D := by
  obtain ⟨D, hD, hb⟩ := spectralCoefficient_uniform N hN B₀ hB₀
  refine ⟨((N : ℝ) + 1) * D, by positivity, fun φ hφ n => ?_⟩
  unfold spectralPolynomial
  rw [add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ k ∈ Finset.Icc 1 (N + 1),
      ‖NlsGge.ThirdConsultation.KSPSRiccati.spectralCoefficient φ k / (n : ℂ) ^ k‖ ≤ D := fun k hk =>
    (div_pow_norm_le _ n k (Finset.mem_Icc.mp hk).1).trans (hb φ hφ k (Finset.mem_Icc.mp hk).2)
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  push_cast
  ring

end
end NlsGge.ThirdConsultation.KSPS025U6
