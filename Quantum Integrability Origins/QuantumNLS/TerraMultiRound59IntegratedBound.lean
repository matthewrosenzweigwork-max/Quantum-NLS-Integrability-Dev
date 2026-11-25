import QuantumNLS.TerraMultiRound59IntegratedForm

/-! A factor-product bound for the integrated correlation coefficient. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound59IntegratedBound
open QuantumNLS.TranslatedCorrelation QuantumNLS.CorrelationTaylor
open QuantumNLS.CorrelationConstrainedSumGen
open QuantumNLS.TerraMultiRound48OrthantMoment QuantumNLS.TerraMultiRound49TaylorPath
open QuantumNLS.TerraMultiRound48Leading
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound51TaylorCoeff
open QuantumNLS.TerraMultiRound59IntegratedForm

variable {L : ℝ} [Fact (0 < L)]

def core (L : ℝ) (m k : ℕ) : ℝ :=
  (max 1 (2 * Real.pi / L)) ^ (2 * k) * L ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
    (((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2)) *
    ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2)

def moment (n d : ℕ) : ℝ :=
  ∫ t : Fin n → ℝ, (∏ i, Real.exp (-t i)) * (∑ i, |t i|) ^ d ∂
    (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ))))

def bound (L : ℝ) (n m k d : ℕ) : ℝ :=
  ‖(Nat.factorial d : ℝ)⁻¹‖ * ((m + 2 : ℕ) : ℝ) ^ d * |core L m k| *
    ((m + 2 : ℕ) : ℝ) ^ d * moment n d

theorem integrated_coeff_bound {n m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) (f : Fin (m + 2) → Hk L k) :
    ‖integratedCoeff (Cfun f) paths d‖ ≤ bound L n m k d * ∏ j, ‖f j‖ := by
  let q : ℝ := ((m + 2 : ℕ) : ℝ)
  let P : ℝ := ∏ j, ‖f j‖
  let A : ℝ := ‖(Nat.factorial d : ℝ)⁻¹‖ * q ^ d * |core L m k| * q ^ d * P
  have hP : 0 ≤ P := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : Bfull f ≤ |core L m k| * P := by
    change core L m k * P ≤ |core L m k| * P
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hP
  have hB0 : 0 ≤ Bfull f := Bfull_nonneg hk f
  let G : (Fin n → ℝ) → ℝ := fun t =>
    (∏ i, Real.exp (-t i)) * (∑ i, |t i|) ^ d
  have hg : Integrable (fun t => A * G t)
      (Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) :=
    (orthant_sum_moment n d).const_mul A
  have hpoint : ∀ t : Fin n → ℝ,
      ‖((∏ i, Real.exp (-t i) : ℝ) : ℂ) * pathCoeff (Cfun f) paths d t‖ ≤ A * G t := by
    intro t
    have hp : 0 ≤ ∏ i : Fin n, Real.exp (-t i) :=
      Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le)
    have ht : 0 ≤ ∑ i : Fin n, |t i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hs : ‖scaledShift paths 1 t‖ ≤ q * ∑ i, |t i| := by
      calc
        _ ≤ eucl (scaledShift paths 1 t) := norm_le_eucl _
        _ ≤ q * (|1| * ∑ i, |t i|) := eucl_scaledShift_le paths 1 t
        _ = _ := by simp
    have hdv := iteratedFDeriv_apply_le hk f hd (0 : Fin (m + 2) → ℝ) (scaledShift paths 1 t)
    have hpow : ‖scaledShift paths 1 t‖ ^ d ≤ (q * ∑ i, |t i|) ^ d :=
      pow_le_pow_left₀ (norm_nonneg _) hs _
    have hest : ‖pathCoeff (Cfun f) paths d t‖ ≤
        A * (∑ i, |t i|) ^ d := by
      unfold pathCoeff
      rw [norm_smul]
      calc
        _ ≤ ‖(Nat.factorial d : ℝ)⁻¹‖ * (q ^ d * Bfull f * ‖scaledShift paths 1 t‖ ^ d) :=
          mul_le_mul_of_nonneg_left hdv (norm_nonneg _)
        _ ≤ ‖(Nat.factorial d : ℝ)⁻¹‖ * (q ^ d * (|core L m k| * P) * (q * ∑ i, |t i|) ^ d) := by
          gcongr
        _ = A * (∑ i, |t i|) ^ d := by dsimp [A]; rw [mul_pow]; ring
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    calc
      _ ≤ (∏ i, Real.exp (-t i)) * (A * (∑ i, |t i|) ^ d) :=
        mul_le_mul_of_nonneg_left hest hp
      _ = A * G t := by dsimp [G]; ring
  unfold integratedCoeff
  calc
    _ ≤ ∫ t, A * G t ∂(Measure.pi (fun _ : Fin n => volume.restrict (Ioi (0 : ℝ)))) :=
      norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpoint)
    _ = bound L n m k d * ∏ j, ‖f j‖ := by
      rw [integral_const_mul]
      dsimp [A, G, bound, moment, P, q]
      ring

#print axioms integrated_coeff_bound
end QuantumNLS.TerraMultiRound59IntegratedBound
