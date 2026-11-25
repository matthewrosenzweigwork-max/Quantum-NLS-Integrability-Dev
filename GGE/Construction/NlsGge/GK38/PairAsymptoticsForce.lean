import NlsGge.GK38.PairAsymptoticsDecay
import NlsGge.GK38.PairAsymptoticsVolterra

/-! # F5: locally uniform weighted smallness of the first Volterra forcing -/

set_option autoImplicit false

open Filter Topology MeasureTheory Set Metric

namespace NlsGge.GK38

noncomputable section

theorem pairForce38_zero_one (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    pairForce38 φ z t 0 1 = Complex.I *
      ∫ s : ℝ in 0..(t : ℝ),
        Complex.exp (Complex.I * (-z) * ((t : ℂ) - 2 * s)) * potRepFst38 φ s := by
  have hi := intervalIntegrable_osc _ (intervalIntegrable_coverRep38_one φ.1) (-z) t.2
  rw [pairForce38_entry, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  have hphase : -(Complex.I * z * (((t : ℝ) - 2 * s : ℝ) : ℂ)) =
      Complex.I * (-z) * ((t : ℂ) - 2 * s) := by push_cast; ring
  simp [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two, hphase]
  ring

theorem pairForce38_one_zero (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    pairForce38 φ z t 1 0 = (-Complex.I) *
      ∫ s : ℝ in 0..(t : ℝ),
        Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * potRepSnd38 φ s := by
  have hi := intervalIntegrable_osc _ (intervalIntegrable_coverRep38_one φ.2) z t.2
  rw [pairForce38_entry, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  have hphase : Complex.I * z * (((t : ℝ) - 2 * s : ℝ) : ℂ) =
      Complex.I * z * ((t : ℂ) - 2 * s) := by push_cast; ring
  simp [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two, hphase]
  ring

theorem pairForce38_diagonal (φ : PotPair) (z : ℂ) (t : Icc (0 : ℝ) 1) (i : Fin 2) :
    pairForce38 φ z t i i = 0 := by
  rw [pairForce38_entry]
  fin_cases i <;> simp [freeE, potCoeff38, Matrix.mul_apply, Fin.sum_univ_two]

/-- Appendix D.1 controls both off-diagonal entries, uniformly near each potential. -/
theorem pairForce38_decay (φ₀ : PotPair) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 φ₀, ∃ R : ℝ, ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      ∀ t : Icc (0 : ℝ) 1, ∀ i j : Fin 2,
        ‖pairForce38 φ z t i j‖ ≤ ε * Real.exp (|z.im| * (t : ℝ)) := by
  obtain ⟨R₁, h₁⟩ := integral_osc_cover_decay φ₀.1 hε
  obtain ⟨R₂, h₂⟩ := integral_osc_cover_decay φ₀.2 hε
  refine ⟨ball φ₀ (ε / 2), ball_mem_nhds _ (half_pos hε), max R₁ R₂,
    fun φ hφ z hz t i j => ?_⟩
  have hφ' : ‖φ - φ₀‖ ≤ ε / 2 := (mem_ball_iff_norm.mp hφ).le
  have hf₁ : ‖φ.1 - φ₀.1‖ ≤ ε / 2 := (norm_fst_le (φ - φ₀)).trans hφ'
  have hf₂ : ‖φ.2 - φ₀.2‖ ≤ ε / 2 := (norm_snd_le (φ - φ₀)).trans hφ'
  have hb₁ := h₁ φ.1 hf₁ (-z) (by simpa using (le_max_left _ _).trans hz) t t.2
  have hb₂ := h₂ φ.2 hf₂ z ((le_max_right _ _).trans hz) t t.2
  fin_cases i <;> fin_cases j
  all_goals dsimp only
  · rw [pairForce38_diagonal, norm_zero]; positivity
  · change ‖pairForce38 φ z t 0 1‖ ≤ ε * Real.exp (|z.im| * (t : ℝ))
    rw [pairForce38_zero_one, norm_mul, Complex.norm_I, one_mul]
    simpa only [potRepFst38, Complex.neg_im, abs_neg] using hb₁
  · change ‖pairForce38 φ z t 1 0‖ ≤ ε * Real.exp (|z.im| * (t : ℝ))
    rw [pairForce38_one_zero, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact hb₂
  · rw [pairForce38_diagonal, norm_zero]; positivity

end

end NlsGge.GK38
