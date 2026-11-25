import QuantumNLS.TerraMultiRound74SmallY

/-! Uniform small-parameter control on H¹-bounded sets, using the accepted
first-moment identity and the exact Fourier Sobolev norm. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.TerraMultiRound74UniformSmall
open QuantumNLS.PhysicalTensor QuantumNLS.TranslatedCorrelation QuantumNLS.FreeLimit
open QuantumNLS.Sobolev QuantumNLS.Fourier
open QuantumNLS.TerraMultiRound64FieldIdentity QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.TerraMultiRound64FirstIdentity QuantumNLS.TerraMultiRound62FreeMoments
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59PolynomialProperty
open QuantumNLS.Reg014Moments QuantumNLS.TerraMultiRound74SmallY

variable {L : ℝ} [Fact (0 < L)]

theorem free_second_le_norm (u : Hk L 1) :
    (∫ t : ℝ, t ^ 2 ∂(freeMeasure L u.val)) ≤ ‖u‖ ^ 2 := by
  have hu := representative_hsq (L := L) 1 u
  have hi : Integrable (fun t : ℝ => t ^ 2) (freeMeasure L u.val) := by
    simpa using (free_even_integrable_iff_hsq u.val 1).mpr hu
  have hs := (free_even_integrable_iff_summable u.val 1).mp (by simpa using hi)
  have hm := free_finite_moment u.val 1 (by simpa using hi)
  simp only [mul_one] at hm hs
  rw [hm, WField.norm_sq_eq_tsum]
  apply Summable.tsum_le_tsum _ (by simpa [QuantumNLS.RootWeightedCellsR26.momentum,
    QuantumNLS.Fourier.freq, ← fourierL2_apply] using hs) u.summable
  intro n
  rw [← fourierL2_apply]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simp only [Nat.cast_one, def002]
  simp only [QuantumNLS.Fourier.sobolevWeight, show (2 : ℝ) * 1 = 2 by norm_num]
  have hfreq : QuantumNLS.RootWeightedCellsR26.momentum L n = QuantumNLS.Fourier.freq L n := rfl
  rw [hfreq]
  change (QuantumNLS.Fourier.freq L n) ^ 2 ≤ (1 + |QuantumNLS.Fourier.freq L n|) ^ 2
  have hpow : |QuantumNLS.Fourier.freq L n| ^ 2 ≤
      (1 + |QuantumNLS.Fourier.freq L n|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (le_add_of_nonneg_left (by norm_num)) 2
  simpa only [sq_abs, Real.rpow_two] using hpow

/-- The small-Y coefficient can be chosen uniformly on every H¹-bounded set. -/
theorem physical_small_uniform (κ : ℝ) (hκ : 0 < κ) (B : Set (Hk L 1))
    (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ B, ∀ Y : ℝ, 0 < Y →
      |Dfun κ hκ 2 u.val Y| ≤ C * Y ^ 2 := by
  obtain ⟨U, hU⟩ := isBounded_iff_forall_norm_le.mp hB
  obtain ⟨R, hR⟩ := RealPolynomial_bounded (R1field_polynomial (L := L) κ) U
  refine ⟨2 * U ^ 2 + max R 0, by positivity, ?_⟩
  intro u hu Y hY
  have hn := hU u hu
  have hnorm : ‖u‖ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hf := free_second_le_norm u
  have hr := hR u hn
  have hr' : R1field (L := L) κ u ≤ max R 0 := (le_abs_self _).trans (hr.trans (le_max_left _ _))
  have hi : Integrable (fun t : ℝ => t ^ 2) (freeMeasure L u.val) := by
    simpa using (free_even_integrable_iff_hsq u.val 1).mpr (representative_hsq 1 u)
  have hm := free_finite_moment u.val 1 (by simpa using hi)
  simp only [mul_one] at hm
  have hid := first_field_identity κ hκ u
  rw [← hm] at hid
  have hb := physical_small κ hκ u Y hY
  nlinarith [sq_nonneg Y, mul_nonneg (sq_nonneg Y) (show 0 ≤ U ^ 2 - ‖u‖ ^ 2 by linarith),
    mul_nonneg (sq_nonneg Y) (show 0 ≤ ‖u‖ ^ 2 - ∫ t : ℝ, t ^ 2 ∂(freeMeasure L u.val) by linarith),
    mul_nonneg (sq_nonneg Y) (show 0 ≤ max R 0 - R1field (L := L) κ u by linarith)]

#print axioms free_second_le_norm
#print axioms physical_small_uniform
end QuantumNLS.TerraMultiRound74UniformSmall
