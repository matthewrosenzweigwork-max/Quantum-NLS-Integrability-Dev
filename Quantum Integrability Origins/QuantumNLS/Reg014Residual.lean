import QuantumNLS.TerraMultiRound64REG004

/-! REG-014 support: explicit uniform bounds for the integrated correlation Taylor
remainder.  The accepted fixed-field theory (REG-006 / REG-007) proves the
integrated remainder is little-oh; here the same global Taylor estimate and the same
exponential orthant majorant are used to give a bound whose constant depends only on
an upper bound for the norms of the factors. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.Reg014Residual
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.CorrelationTaylor
open QuantumNLS.TerraMultiRound48Orthant QuantumNLS.TerraMultiRound48OrthantMoment
open QuantumNLS.TerraMultiRound49TaylorBound QuantumNLS.TerraMultiRound49IntegratedLittleO
open QuantumNLS.TerraMultiRound51CorrelationExpansion

variable {L : ℝ} [Fact (0 < L)]

/-- The orthant integral of the exponential density (a number depending only on `n`). -/
def Iexp (n : ℕ) : ℝ :=
  ∫ t : Fin n → ℝ, (∏ i, Real.exp (-t i))
    ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))

/-- The orthant moment of the exponential density (a number depending only on `n`, `d`). -/
def Imom (n d : ℕ) : ℝ :=
  ∫ t : Fin n → ℝ, (∏ i, Real.exp (-t i)) * (∑ i, |t i|) ^ d
    ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))

theorem Iexp_nonneg (n : ℕ) : 0 ≤ Iexp n := by
  unfold Iexp
  exact integral_nonneg (fun t => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))

theorem Imom_nonneg (n d : ℕ) : 0 ≤ Imom n d := by
  unfold Imom
  exact integral_nonneg (fun t => mul_nonneg (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))
    (pow_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) _))

/-- The integrated Taylor residual obeys the scale power times an explicit constant. -/
theorem residual_norm_le {n m k d : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k)
    (hd : d + 1 ≤ 2 * k) (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) :
    ‖integratedResidual f d paths z‖ ≤
      |z| ^ (d + 1) * (majorantConstant f d * Imom n (d + 1)) := by
  by_cases hz : z = 0
  · subst hz
    rw [integratedResidual_zero hk f hd paths]
    simp
  · have hzpow : 0 < |z| ^ (d + 1) := pow_pos (abs_pos.mpr hz) _
    have h1 := normalized_integral_eq f d paths z
    have hint : Integrable (fun t : Fin n → ℝ => majorantConstant f d *
        ((∏ i, Real.exp (-t i)) * (∑ i, |t i|) ^ (d + 1)))
        (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) :=
      (orthant_sum_moment n (d + 1)).const_mul _
    have h3 : ‖(z ^ (d + 1))⁻¹ • integratedResidual f d paths z‖ ≤
        majorantConstant f d * Imom n (d + 1) := by
      rw [h1]
      have hpt : ∀ t : Fin n → ℝ, ‖((∏ i, Real.exp (-t i) : ℝ) : ℂ) * remainder f d paths z t‖ ≤
          majorantConstant f d * ((∏ i, Real.exp (-t i)) * (∑ i, |t i|) ^ (d + 1)) := by
        intro t
        have hp : 0 ≤ ∏ i : Fin n, Real.exp (-t i) :=
          Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
        calc
          _ ≤ (∏ i : Fin n, Real.exp (-t i)) *
              (majorantConstant f d * (∑ i, |t i|) ^ (d + 1)) :=
            mul_le_mul_of_nonneg_left (remainder_bound hk f hd paths z t) hp
          _ = _ := by ring
      have hb := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
      rw [integral_const_mul] at hb
      exact hb
    simp only [norm_smul, norm_inv, norm_pow, Real.norm_eq_abs] at h3
    exact (inv_mul_le_iff₀ hzpow).mp h3

/-- The integrated correlation is bounded by the sup bound of the correlation. -/
theorem correlation_norm_le {n m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k)
    (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ) :
    ‖integratedCorrelation f paths z‖ ≤
      (L * Fourier.cL L ^ (m + 2) * ∏ j, ‖f j‖) * Iexp n := by
  unfold integratedCorrelation Iexp
  have hint : Integrable (fun t : Fin n → ℝ => (L * Fourier.cL L ^ (m + 2) * ∏ j, ‖f j‖) *
      ∏ i, Real.exp (-t i))
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) :=
    (orthant_exp_integrable n).const_mul _
  have hpt : ∀ t : Fin n → ℝ, ‖((∏ i, Real.exp (-t i) : ℝ) : ℂ) *
      Cfun f (TerraMultiRound48Leading.scaledShift paths z t)‖ ≤
      (L * Fourier.cL L ^ (m + 2) * ∏ j, ‖f j‖) * ∏ i, Real.exp (-t i) := by
    intro t
    have hp : 0 ≤ ∏ i : Fin n, Real.exp (-t i) :=
      Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    calc
      _ ≤ (∏ i : Fin n, Real.exp (-t i)) * (L * Fourier.cL L ^ (m + 2) * ∏ j, ‖f j‖) :=
        mul_le_mul_of_nonneg_left (norm_Cfun_le hk f _) hp
      _ = _ := mul_comm _ _
  have hb := norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at hb
  exact hb

/-- The printed constant `Bfull` is a fixed constant times the product of the factor norms. -/
theorem Bfull_factor (m k : ℕ) : ∃ c : ℝ, 0 ≤ c ∧
    ∀ f : Fin (m + 2) → Hk L k, Bfull f = c * ∏ j, ‖f j‖ := by
  refine ⟨(max 1 (2 * Real.pi / L)) ^ (2 * k) * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
    (((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (CorrelationConstrainedSumGen.Ckc k) ^ (m + 2)) *
    ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2), ?_, fun f => rfl⟩
  have hL : 0 < L := Fact.out
  have h1 : 0 ≤ CorrelationConstrainedSumGen.Ckc k := Real.sqrt_nonneg _
  positivity

/-- If every factor has norm at most `U`, then the product of the norms is at most `U^(m+2)`. -/
theorem prod_norm_le {m k : ℕ} (f : Fin (m + 2) → Hk L k) (U : ℝ)
    (hf : ∀ j, ‖f j‖ ≤ U) : ∏ j, ‖f j‖ ≤ U ^ (m + 2) := by
  calc ∏ j, ‖f j‖ ≤ ∏ _j : Fin (m + 2), U :=
        Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hf j)
    _ = U ^ (m + 2) := by simp

/-- Uniform bound for the integrated residual in terms of an upper bound `U` for the factors. -/
theorem residual_uniform {n m k d : ℕ} (hk : 1 ≤ k) (hd : d + 1 ≤ 2 * k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : ℝ), 0 ≤ U → ∀ (f : Fin (m + 2) → Hk L k),
      (∀ j, ‖f j‖ ≤ U) → ∀ (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ),
      ‖integratedResidual f d paths z‖ ≤ |z| ^ (d + 1) * (K * U ^ (m + 2)) := by
  obtain ⟨c, hc, hBf⟩ := Bfull_factor (L := L) m k
  have hq : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by positivity
  refine ⟨2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * c) * ((m + 2 : ℕ) : ℝ) ^ (d + 1) * Imom n (d + 1),
    by have := Imom_nonneg n (d + 1); positivity, ?_⟩
  intro U hU f hf paths z
  refine (residual_norm_le hk f hd paths z).trans ?_
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg z) _)
  have hP := prod_norm_le f U hf
  have hIm := Imom_nonneg n (d + 1)
  have hmaj : majorantConstant f d ≤ 2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * c) *
      ((m + 2 : ℕ) : ℝ) ^ (d + 1) * U ^ (m + 2) := by
    unfold majorantConstant
    rw [hBf f]
    have h1 : c * ∏ j, ‖f j‖ ≤ c * U ^ (m + 2) := mul_le_mul_of_nonneg_left hP hc
    have h2 : ((m + 2 : ℕ) : ℝ) ^ (2 * k) * (c * ∏ j, ‖f j‖) ≤
        ((m + 2 : ℕ) : ℝ) ^ (2 * k) * (c * U ^ (m + 2)) :=
      mul_le_mul_of_nonneg_left h1 (pow_nonneg hq _)
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2)
    have h4 := mul_le_mul_of_nonneg_right h3 (pow_nonneg hq (d + 1))
    calc _ ≤ _ := h4
      _ = _ := by ring
  calc majorantConstant f d * Imom n (d + 1)
      ≤ (2 * (((m + 2 : ℕ) : ℝ) ^ (2 * k) * c) * ((m + 2 : ℕ) : ℝ) ^ (d + 1) * U ^ (m + 2)) *
        Imom n (d + 1) := mul_le_mul_of_nonneg_right hmaj hIm
    _ = _ := by ring

/-- Uniform bound for the integrated correlation. -/
theorem correlation_uniform {n m k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : ℝ), 0 ≤ U → ∀ (f : Fin (m + 2) → Hk L k),
      (∀ j, ‖f j‖ ≤ U) → ∀ (paths : Fin (m + 2) → Finset (Fin n)) (z : ℝ),
      ‖integratedCorrelation f paths z‖ ≤ K * U ^ (m + 2) := by
  have hL : 0 < L := Fact.out
  have hcL : 0 ≤ Fourier.cL L := Real.sqrt_nonneg _
  refine ⟨L * Fourier.cL L ^ (m + 2) * Iexp n,
    by have := Iexp_nonneg n; positivity, ?_⟩
  intro U hU f hf paths z
  refine (correlation_norm_le hk f paths z).trans ?_
  have hP := prod_norm_le f U hf
  have hI := Iexp_nonneg n
  have h1 : L * Fourier.cL L ^ (m + 2) * ∏ j, ‖f j‖ ≤ L * Fourier.cL L ^ (m + 2) * U ^ (m + 2) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  calc _ ≤ (L * Fourier.cL L ^ (m + 2) * U ^ (m + 2)) * Iexp n :=
        mul_le_mul_of_nonneg_right h1 hI
    _ = _ := by ring

#print axioms residual_norm_le
#print axioms correlation_norm_le
#print axioms Bfull_factor
#print axioms residual_uniform
#print axioms correlation_uniform
end QuantumNLS.Reg014Residual
