import QuantumNLS.TerraMultiRound66SmoothQuartic
import QuantumNLS.TerraMultiRound65FourthCore

/-! Smooth identification of the fourth-order Riccati correction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound41Coefficients
open QuantumNLS.TerraMultiRound65FifthRecursion QuantumNLS.TerraMultiRound66SmoothQuartic
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevE1 QuantumNLS.TranslatedCorrelation QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59SourceRecursion
namespace QuantumNLS.TerraMultiRound66SmoothCorrection

theorem smooth_recursive_correction (L κ : ℝ) {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    (∫ x in (0 : ℝ)..L, conj (f x) *
      (aseq κ f 5 x - iteratedDeriv 4 f x)) =
      (κ : ℂ) * (∫ x in (0 : ℝ)..L,
        6 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) +
        (deriv (fun y => ((‖f y‖^2 : ℝ) : ℂ)) x)^2) +
      2 * (κ : ℂ)^2 * (∫ x in (0 : ℝ)..L, ((‖f x‖^6 : ℝ) : ℂ)) := by
  let Q : ℝ → ℂ := fun x =>
      -conj (f x) * conj (deriv (deriv f) x) * f x^2
      - 6 * conj (f x) * conj (deriv f x) * f x * deriv f x
      - 5 * (conj (f x))^2 * (deriv f x)^2
      - 6 * (conj (f x))^2 * f x * deriv (deriv f) x
  let S : ℝ → ℂ := fun x => ((‖f x‖^6 : ℝ) : ℂ)
  have cf : Continuous f := hf.smooth.continuous
  have cf' : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf.smooth).2.continuous
  have cf'' : Continuous (deriv (deriv f)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf.smooth).2).2.continuous
  have hQ : IntervalIntegrable Q volume 0 L := by
    apply Continuous.intervalIntegrable
    dsimp [Q]
    fun_prop
  have hS : IntervalIntegrable S volume 0 L := by
    apply Continuous.intervalIntegrable
    dsimp [S]
    fun_prop
  have hfour : iteratedDeriv 4 f = deriv (deriv (deriv (deriv f))) := by
    change iteratedDeriv (3 + 1) f = _
    rw [iteratedDeriv_succ]
    change deriv (iteratedDeriv (2 + 1) f) = _
    rw [iteratedDeriv_succ]
    change deriv (deriv (iteratedDeriv (1 + 1) f)) = _
    rw [iteratedDeriv_succ]
    change deriv (deriv (deriv (iteratedDeriv (0 + 1) f))) = _
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
  calc
    _ = ∫ x in (0 : ℝ)..L, (κ : ℂ) * Q x + 2 * (κ : ℂ)^2 * S x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [aseq_five κ hf, hfour]
      dsimp [Q, S]
      have hz : conj (f x) * f x = ((‖f x‖^2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      have hz6 : ((‖f x‖^6 : ℝ) : ℂ) = (conj (f x) * f x)^3 := by
        rw [hz]
        push_cast
        ring
      rw [hz6]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hQ.const_mul _) (hS.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rw [smooth_quartic_integral L hf]

/-- The REG-004 correction agrees with the explicit expression on smooth fields. -/
theorem smooth_Rfield_correction (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (v : Hk L 1) (f : ℝ → ℂ)
    (hrep : physRep L 1 (coordinates (L := L) 1 v) = f) (hf : SmoothPeriodic L f) :
    ((Rfield (L := L) 2 (by omega) κ v : ℝ) : ℂ) =
      (κ : ℂ) * (∫ x in (0 : ℝ)..L,
        6 * ((‖f x‖^2 * ‖deriv f x‖^2 : ℝ) : ℂ) +
        (deriv (fun y => ((‖f y‖^2 : ℝ) : ℂ)) x)^2) +
      2 * (κ : ℂ)^2 * (∫ x in (0 : ℝ)..L, ((‖f x‖^6 : ℝ) : ℂ)) := by
  have h := R_source_smooth L 2 (by omega) κ hκ (coordinates (L := L) 1 v) f (by norm_num; exact hrep) hf
  simp only [show 2 * 2 + 1 = 5 by norm_num, show 2 * 2 = 4 by norm_num,
    neg_one_sq, one_mul] at h
  change ((Rfield (L := L) 2 (by omega) κ v : ℝ) : ℂ) = _ at h
  rw [h, smooth_recursive_correction L κ hf]

#print axioms smooth_recursive_correction
#print axioms smooth_Rfield_correction
end QuantumNLS.TerraMultiRound66SmoothCorrection
