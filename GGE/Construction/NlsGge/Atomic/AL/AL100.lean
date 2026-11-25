import NlsGge.Hierarchy.ALPlaneWaveGap38

namespace NlsGge.Atomic.AL100

open NlsGge.AblowitzLadik

theorem alPlaneGauge_period_L38 (L : ℕ) [NeZero L] (k : ℤ) :
    alPlaneGaugeInv38 (Complex.exp (((Real.pi * k / L : ℝ) : ℂ) * Complex.I)) L =
      ((-1 : ℂ) ^ k) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have huL : (Complex.exp (((Real.pi * k / L : ℝ) : ℂ) * Complex.I)) ^ L = (-1 : ℂ) ^ k := by
    rw [← Complex.exp_nat_mul]
    have : (L : ℂ) * (((Real.pi * k / L : ℝ) : ℂ) * Complex.I) =
        (k : ℂ) * (Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hσ : ((-1 : ℂ) ^ k)⁻¹ = (-1 : ℂ) ^ k := by
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩ <;> simp [zpow_add₀, zpow_mul]
  unfold alPlaneGaugeInv38
  rw [huL, hσ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem alPlaneWave_monodromy_constant38
    (L : ℕ) [NeZero L] (k : ℤ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t / (L : ℝ) < 1) (lam : ℝ) :
    alMonodromy38 (alPlaneWave38 L k t)
      (Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I)) =
      ((-1 : ℂ) ^ k) •
        (alPlaneB38 (t / (L : ℝ)) (Real.pi * k / L)
          (Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I))) ^ L ∧
    Matrix.trace
      (alPlaneB38 (t / (L : ℝ)) (Real.pi * k / L)
        (Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I))) / 2 =
      ((Real.cos (lam / (L : ℝ) - Real.pi * k / L) /
        Real.sqrt (1 - (t / (L : ℝ)) ^ 2) : ℝ) : ℂ) := by
  have hs0 : 0 ≤ t / (L : ℝ) := by positivity
  have hM : alMonodromy38 (alPlaneWave38 L k t)
      (Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I)) =
      alPlaneGaugeInv38 (Complex.exp (((Real.pi * k / L : ℝ) : ℂ) * Complex.I)) L *
        (alPlaneB38 (t / (L : ℝ)) (Real.pi * k / L)
          (Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I))) ^ L :=
    alPlanePartial38 L k ht0 ht1 _ L le_rfl
  refine ⟨?_, ?_⟩
  · rw [hM, alPlaneGauge_period_L38, Matrix.smul_mul, Matrix.one_mul]
  · obtain ⟨-, htr⟩ := alPlaneB_data38 hs0 ht1 (Real.pi * k / L) (lam / (L : ℝ))
    have htrB : Matrix.trace (alPlaneB38 (t / (L : ℝ)) (Real.pi * k / L)
        (Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I))) =
        ((((Real.sqrt (1 - (t / (L : ℝ)) ^ 2) : ℝ) : ℂ))⁻¹ *
            Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I) *
            (Complex.exp ((((Real.pi * k / L) : ℝ) : ℂ) * Complex.I))⁻¹) +
        ((((Real.sqrt (1 - (t / (L : ℝ)) ^ 2) : ℝ) : ℂ))⁻¹ *
            (Complex.exp ((((lam / (L : ℝ)) : ℝ) : ℂ) * Complex.I))⁻¹ *
            Complex.exp ((((Real.pi * k / L) : ℝ) : ℂ) * Complex.I)) := by
      simp [Matrix.trace_fin_two, alPlaneB38]
    rw [htrB]
    linear_combination (1 / 2 : ℂ) * htr

end NlsGge.Atomic.AL100
