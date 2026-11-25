import Mathlib
import NlsGge.Atomic.M.M016MassAssembly

                                                                                                        
                                                                   
                                                                                                                     
                                                                                               
                                                                                                             
                                                                                                                             
                                                                    
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016AssemblyAux

open NlsGge.ThirdConsultation.M016MassAux NlsGge.ThirdConsultation.M016DysonAux

theorem sqrt_norm_coverRep (f : PhysicalL2) :
    Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖NlsGge.GK38.coverRep38 f s‖ ^ 2) = ‖f‖ := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_sq_coverRep38_one,
    Real.sqrt_sq (norm_nonneg _)]

/-- Quantitative ray bound: `|e^{-t}Δ(it) − 1| ≤ e^{-2t} + M/(2t) + (M/t)²`, `M = ‖φ₁‖‖φ₂‖`, for `t ≥ M + 1`. -/
theorem ray_bound (φ : PotPair) (t : ℝ) (ht : ‖φ.1‖ * ‖φ.2‖ + 1 ≤ t) :
    ‖(Real.exp (-t) : ℂ) * NlsGge.GK38.discrim φ (Complex.I * t) - 1‖ ≤
      Real.exp (-(2 * t)) + ‖φ.1‖ * ‖φ.2‖ / (2 * t) + (‖φ.1‖ * ‖φ.2‖ / t) ^ 2 := by
  set M : ℝ := ‖φ.1‖ * ‖φ.2‖ with hMdef
  have hM0 : 0 ≤ M := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have ht0 : 0 < t := by linarith
  have hMeq : Real.sqrt (∫ s in Ioc (0 : ℝ) 1, ‖NlsGge.GK38.coverRep38 φ.1 s‖ ^ 2) *
      Real.sqrt (∫ r in Ioc (0 : ℝ) 1, ‖NlsGge.GK38.coverRep38 φ.2 r‖ ^ 2) = M := by
    rw [sqrt_norm_coverRep, sqrt_norm_coverRep]
  set Pt := ∫ s in Ioc (0 : ℝ) 1, ∫ r in Ioc (0 : ℝ) 1,
    (pairW t s r : ℂ) * NlsGge.GK38.coverRep38 φ.1 s * NlsGge.GK38.coverRep38 φ.2 r with hPt
  have h1 : trOne (dysonTerm φ t 1) = 0 := trOne_odd φ t 0
  have h3 : trOne (dysonTerm φ t 3) = 0 := trOne_odd φ t 1
  have hsig : ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k) =
      ((Real.exp t : ℂ) + (Real.exp (-t) : ℂ)) + (Real.exp t : ℂ) * Pt := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [trOne_zero, trOne_two φ t ht0.le, h1, h3]
    ring
  have e1 : (Real.exp (-t) : ℂ) * (Real.exp t : ℂ) = 1 := by rw [cexp_mul]; simp
  have e2 : (Real.exp (-t) : ℂ) * (Real.exp (-t) : ℂ) = (Real.exp (-(2 * t)) : ℂ) := by
    rw [cexp_mul]; congr 2; ring
  have hid : (Real.exp (-t) : ℂ) * NlsGge.GK38.discrim φ (Complex.I * t) - 1 =
      (Real.exp (-(2 * t)) : ℂ) + Pt + (Real.exp (-t) : ℂ) *
        (NlsGge.GK38.discrim φ (Complex.I * t) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k)) := by
    rw [hsig]
    linear_combination (1 + Pt) * e1 + e2
  -- order two
  have hc : (1 - Real.exp (-(2 * t))) / (2 * t) * M ≤ M / (2 * t) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.exp_pos (-(2 * t))]) (by positivity)
  have hP : ‖Pt‖ ≤ M / (2 * t) := by
    have := Q_norm_le t ht0 (memLp_coverRep38 φ.1) (memLp_coverRep38 φ.2)
    rw [hMeq] at this
    exact this.trans hc
  -- remainder
  have hS := (schur_pot φ t ht0).2
  rw [hMeq] at hS
  have hA : majA φ t ≤ M / (2 * t) := (majA_le_schur φ t ht0).trans (hS.trans hc)
  have hW : majW φ t 1 ≤ M / (2 * t) := (majW_le_schur φ t ht0).trans (hS.trans hc)
  have hA0 := majA_nonneg φ t
  have hhalf : M / (2 * t) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]; nlinarith
  have hA1 : majA φ t < 1 := by linarith
  have hrem := dyson_remainder_le φ t hA1
  have hfrac : majA φ t / (1 - majA φ t) ≤ M / t := by
    rw [div_le_div_iff₀ (by linarith) ht0]
    have : M / (2 * t) * t = M / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hA ht0.le]
  have hsum : majA φ t + majW φ t 1 ≤ M / t := by
    have : M / (2 * t) + M / (2 * t) = M / t := by field_simp; ring
    linarith
  have hexp : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hR : ‖(Real.exp (-t) : ℂ) * (NlsGge.GK38.discrim φ (Complex.I * t) -
      ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k))‖ ≤ (M / t) ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-t) * ‖NlsGge.GK38.discrim φ (Complex.I * ↑t) -
          ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k)‖
        ≤ Real.exp (-t) * (Real.exp t * (majA φ t + majW φ t 1) * (majA φ t / (1 - majA φ t))) :=
          mul_le_mul_of_nonneg_left hrem (Real.exp_pos _).le
      _ = (majA φ t + majW φ t 1) * (majA φ t / (1 - majA φ t)) := by
          rw [← mul_assoc, ← mul_assoc, hexp, one_mul]
      _ ≤ (M / t) * (M / t) :=
          mul_le_mul hsum hfrac (div_nonneg hA0 (by linarith)) (by positivity)
      _ = (M / t) ^ 2 := by ring
  rw [hid]
  calc ‖(Real.exp (-(2 * t)) : ℂ) + Pt + (Real.exp (-t) : ℂ) *
        (NlsGge.GK38.discrim φ (Complex.I * t) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k))‖
      ≤ ‖(Real.exp (-(2 * t)) : ℂ)‖ + ‖Pt‖ + ‖(Real.exp (-t) : ℂ) *
        (NlsGge.GK38.discrim φ (Complex.I * t) - ∑ k ∈ Finset.range 4, trOne (dysonTerm φ t k))‖ :=
        norm_add₃_le
    _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        linarith

/-- **(S5a)** Uniform ray estimate on `L²`-bounded potential pairs. -/
theorem discrim_ray_uniform (M : ℝ) :
    ∃ T : ℝ, ∀ φ : PotPair, ‖φ.1‖ ≤ M → ‖φ.2‖ ≤ M → ∀ t : ℝ, T ≤ t →
      ‖(Real.exp (-t) : ℂ) * NlsGge.GK38.discrim φ (Complex.I * t) - 1‖ ≤ 1 / 4 := by
  refine ⟨8 * (M ^ 2 + 1), fun φ h1 h2 t ht => ?_⟩
  have hn1 := norm_nonneg φ.1
  have hn2 := norm_nonneg φ.2
  have hMφ : ‖φ.1‖ * ‖φ.2‖ ≤ M ^ 2 := by nlinarith
  have hMφ0 : 0 ≤ ‖φ.1‖ * ‖φ.2‖ := mul_nonneg hn1 hn2
  have hT1 : 1 ≤ M ^ 2 + 1 := by nlinarith [sq_nonneg M]
  have ht8 : 8 ≤ t := by nlinarith
  have ht0 : 0 < t := by linarith
  have hb := ray_bound φ t (by nlinarith)
  have he : Real.exp (-(2 * t)) ≤ 1 / 16 := by
    have h := Real.add_one_le_exp (2 * t)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hq : ‖φ.1‖ * ‖φ.2‖ / t ≤ 1 / 8 := by
    rw [div_le_iff₀ ht0]; nlinarith
  have hq2 : (‖φ.1‖ * ‖φ.2‖ / t) ^ 2 ≤ 1 / 64 := by
    have h0 : 0 ≤ ‖φ.1‖ * ‖φ.2‖ / t := div_nonneg hMφ0 ht0.le
    nlinarith
  have hq1 : ‖φ.1‖ * ‖φ.2‖ / (2 * t) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

end NlsGge.ThirdConsultation.M016AssemblyAux
