import QuantumNLS.TerraMultiRound77MomentContinuity
import QuantumNLS.TerraMultiRound77ActionCriteria

/-! Real-order free moment continuity on the actual Sobolev carrier. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.FreeLimit QuantumNLS.Fourier QuantumNLS.Sobolev
namespace QuantumNLS.TerraMultiRound77FreeContinuity

/-- The mass plus the homogeneous moment defines a positive auxiliary weight. -/
def powerWeight (L s : ℝ) : PosWeight where
  w n := 1 + |QuantumNLS.Fourier.freq L n| ^ (2*s)
  pos n := by positivity

theorem powerWeight_le (L s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    (powerWeight L s).w n ≤ 2 * (def002 L s).w n := by
  have h1 : 1 ≤ (def002 L s).w n := one_le_def002 L hs n
  have h2 : |QuantumNLS.Fourier.freq L n| ^ (2*s) ≤ (def002 L s).w n := by
    change |QuantumNLS.Fourier.freq L n| ^ (2*s) ≤ (1 + |QuantumNLS.Fourier.freq L n|) ^ (2*s)
    exact Real.rpow_le_rpow (abs_nonneg _) (by linarith [abs_nonneg (QuantumNLS.Fourier.freq L n)]) (by positivity)
  change 1 + |QuantumNLS.Fourier.freq L n| ^ (2*s) ≤ _
  linarith

variable {L : ℝ} [Fact (0 < L)]

def powerInclusion (s : ℝ) (hs : 0 ≤ s) : H02 L s →L[ℂ] WField L (powerWeight L s) :=
  fieldIncl _ _ (by norm_num) (powerWeight_le L s hs)

theorem power_series_summable (s : ℝ) (hs : 0 ≤ s) (u : H02 L s) :
    Summable (fun n : ℤ => |QuantumNLS.Fourier.freq L n| ^ (2*s) * ‖fourierL2 L u.val n‖ ^ 2) := by
  have h := (powerInclusion (L := L) s hs u).summable
  apply h.of_nonneg_of_le
  · intro n; positivity
  · intro n
    change |QuantumNLS.Fourier.freq L n| ^ (2*s) * ‖fourierL2 L u.val n‖ ^ 2 ≤
      (1 + |QuantumNLS.Fourier.freq L n| ^ (2*s)) * ‖fourierL2 L (powerInclusion s hs u).val n‖ ^ 2
    have hv : (powerInclusion s hs u).val = u.val := rfl
    rw [hv]
    nlinarith [sq_nonneg ‖fourierL2 L u.val n‖]

theorem free_power_integrable (s : ℝ) (hs : 0 ≤ s) (u : H02 L s) :
    Integrable (fun x : ℝ => |x| ^ (2*s)) (freeMeasure L u.val) := by
  change Integrable (fun x : ℝ => |x| ^ (2*s)) (Measure.sum (fun n : ℤ =>
    ENNReal.ofReal (‖coeff L (u.val : AddCircle L → ℂ) n‖^2) •
      Measure.dirac (2 * Real.pi * n / L)))
  rw [integrable_sum_dirac_iff (fun n => by simp)]
  have h := power_series_summable s hs u
  apply h.congr
  intro n
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← fourierL2_apply]
  simp only [QuantumNLS.Fourier.freq]
  ring

theorem free_power_eq_series (s : ℝ) (hs : 0 ≤ s) (u : H02 L s) :
    (∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u.val) =
      ∑' n : ℤ, |QuantumNLS.Fourier.freq L n| ^ (2*s) * ‖fourierL2 L u.val n‖ ^ 2 := by
  have h := free_power_integrable s hs u
  change Integrable (fun x : ℝ => |x|^(2*s)) (Measure.sum (fun n : ℤ =>
    ENNReal.ofReal (‖coeff L (u.val : AddCircle L → ℂ) n‖^2) •
      Measure.dirac (2 * Real.pi * n / L))) at h
  have he := (hasSum_integral_measure h).tsum_eq.symm
  convert he using 1
  · rfl
  · apply tsum_congr
    intro n
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul,
      ← fourierL2_apply]
    simp only [QuantumNLS.Fourier.freq]
    ring

/-- The homogeneous free moment is the difference of two continuous squared
norms, giving continuity without a higher-order hypothesis. -/
theorem free_power_continuous (s : ℝ) (hs : 0 ≤ s) :
    Continuous (fun u : H02 L s => ∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u.val) := by
  have heq : (fun u : H02 L s => ∫ x : ℝ, |x| ^ (2*s) ∂freeMeasure L u.val) =
      fun u => ‖powerInclusion s hs u‖^2 - ‖u.val‖^2 := by
    funext u
    rw [free_power_eq_series s hs u, WField.norm_sq_eq_tsum]
    have hv : (powerInclusion s hs u).val = u.val := rfl
    rw [hv]
    have hsum := power_series_summable s hs u
    have hmass : Summable (fun n : ℤ => ‖fourierL2 L u.val n‖ ^ 2) :=
      PosWeight.summable_sq_of_lp (fourierL2 L u.val)
    have hnorm : (∑' n : ℤ, ‖fourierL2 L u.val n‖ ^ 2) = ‖u.val‖^2 := by
      rw [← hsNormSq_zero_fourierL2 L u.val]
      simp [hsNormSq, sobolevWeight]
    have hsplit : (∑' n : ℤ, (powerWeight L s).w n * ‖fourierL2 L u.val n‖^2) =
        (∑' n : ℤ, ‖fourierL2 L u.val n‖^2) +
          ∑' n : ℤ, |QuantumNLS.Fourier.freq L n| ^ (2*s) * ‖fourierL2 L u.val n‖^2 := by
      rw [← hmass.tsum_add hsum]
      apply tsum_congr
      intro n
      dsimp [powerWeight]
      ring
    rw [hsplit, hnorm]
    ring
  rw [heq]
  exact ((powerInclusion (L := L) s hs).continuous.norm.pow 2).sub
    (((H02.toL2 (L := L) hs).continuous.norm).pow 2)

/-- Same-order physical moment continuity in the low range on H^s. -/
theorem physical_power_continuous (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs0 : 0 < s) (hs : s < 1/2) :
    Continuous (fun u : H02 L s => ∫ x : ℝ, |x| ^ (2*s) ∂PhysicalQuantumMeasure.measure hκ u.val) := by
  rw [continuous_iff_seqContinuous]
  intro u v hu
  apply QuantumNLS.TerraMultiRound77MomentContinuity.physical_moment_tendsto_of_free hκ
    (fun j => (u j).val) v.val s hs0 hs
  · exact ((H02.toL2 (L := L) hs0.le).continuous.tendsto v).comp hu
  · exact fun j => free_power_integrable s hs0.le (u j)
  · exact free_power_integrable s hs0.le v
  · exact ((free_power_continuous (L := L) s hs0.le).tendsto v).comp hu

#print axioms powerWeight_le
#print axioms power_series_summable
#print axioms free_power_integrable
#print axioms free_power_eq_series
#print axioms free_power_continuous
#print axioms physical_power_continuous
end QuantumNLS.TerraMultiRound77FreeContinuity
