import NlsGge.GK38.DirichletChar
import NlsGge.GK38.PairAsymptoticsTriangularProbe
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # D1: exact triangular constant characteristic, including the zero parameter

This calculation is independent of the Dirichlet labelling or product theorem.
The exponential integral is used only at a proved nonzero frequency. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_triangle_upper_right38 (a z : ℂ) (hz : z ≠ 0) :
    monodromyPair (constL2 a, 0) z 0 1 = Complex.I * a * Complex.sin z / z := by
  have hc : 2 * Complex.I * z ≠ 0 := mul_ne_zero dirichlet_denominator_ne_zero38 hz
  have hci : IntervalIntegrable (fun s : ℝ => Complex.exp ((2 * Complex.I * z) * s)) volume 0 1 := by
    exact (by fun_prop : Continuous (fun s : ℝ => Complex.exp ((2 * Complex.I * z) * s))).intervalIntegrable _ _
  have hphase (s : ℝ) : Complex.exp (Complex.I * (-z) * (1 - 2 * s)) =
      Complex.exp (-(Complex.I * z)) * Complex.exp ((2 * Complex.I * z) * s) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hae : (fun s : ℝ => Complex.exp (Complex.I * (-z) * (1 - 2 * s)) *
      potRepFst38 (constL2 a, 0) s) =ᵐ[volume]
      fun s => (Complex.exp (-(Complex.I * z)) * a) * Complex.exp ((2 * Complex.I * z) * s) := by
    filter_upwards [coverRep38_const_ae a] with s hs
    rw [hphase]
    simp only [potRepFst38, hs]
    ring
  have hexp : Complex.exp (-(Complex.I * z)) * Complex.exp (2 * Complex.I * z) =
      Complex.exp (Complex.I * z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [triangularMonodromy_eq38]
  change freeE z 1 0 1 + pairForce38 (constL2 a, 0) z ⟨1, zero_le_one, le_rfl⟩ 0 1 = _
  rw [show freeE z 1 0 1 = 0 from by simp [freeE], zero_add, pairForce38_zero_one]
  change Complex.I * (∫ s : ℝ in 0..1, Complex.exp (Complex.I * (-z) * (1 - 2 * s)) *
    potRepFst38 (constL2 a, 0) s) = _
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [hae] with s hs _ using hs),
    intervalIntegral.integral_const_mul, integral_exp_mul_complex hc]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
  rw [Complex.sin]
  have hp : Complex.exp (-z * Complex.I) = Complex.exp (-(Complex.I * z)) := by congr 1; ring
  have hm : Complex.exp (z * Complex.I) = Complex.exp (Complex.I * z) := by congr 1; ring
  rw [hp, hm]
  field_simp [hz, Complex.I_ne_zero]
  simp only [Complex.I_sq, show Complex.I * z * 2 = 2 * Complex.I * z from by ring]
  linear_combination a * hexp

theorem dirichlet_triangle_entries38 (u : PhysicalL2) (z : ℂ) :
    monodromyPair (u, 0) z 0 0 = freeE z 1 0 0 ∧
    monodromyPair (u, 0) z 1 1 = freeE z 1 1 1 ∧
    monodromyPair (u, 0) z 1 0 = 0 := by
  rw [triangularMonodromy_eq38]
  simp [Matrix.add_apply, Matrix.of_apply, pairForce38_diagonal, triangularForce_lower_left38, freeE]

/-- The constant triangular characteristic at zero is evaluated separately from the nonzero formula. -/
theorem dirichlet_triangle_zero38 (a : ℂ) :
    dirichletChar (constL2 a, 0) 0 = -a / 2 := by
  obtain ⟨h00, h11, h10⟩ := dirichlet_triangle_entries38 (constL2 a) 0
  have h01 : monodromyPair (constL2 a, 0) 0 0 1 = Complex.I * a := by
    rw [monodromyPair_eq_fundPair, triangularConst_upper_right_zero38]
    simp
  rw [dirichletChar_eq, h00, h11, h10, h01]
  simp only [freeE, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_add]
  field_simp
  ring

/-- The exact nonzero-parameter formula; no assertion is made by substituting zero into a quotient. -/
theorem dirichlet_triangle_nonzero38 (a z : ℂ) (hz : z ≠ 0) :
    dirichletChar (constL2 a, 0) z = (1 - a / (2 * z)) * Complex.sin z := by
  obtain ⟨h00, h11, h10⟩ := dirichlet_triangle_entries38 (constL2 a) z
  have hfree : freeE z 1 1 1 - freeE z 1 0 0 = Complex.sin z * (2 * Complex.I) := by
    have hh := dirichletChar_zero z
    rw [dirichletChar_eq, monodromyPair_zero_potential] at hh
    have he : freeE z 1 1 0 = 0 ∧ freeE z 1 0 1 = 0 := by simp [freeE]
    simp only [he.1, he.2, zero_add, sub_zero] at hh
    exact (div_eq_iff dirichlet_denominator_ne_zero38).mp hh
  rw [dirichletChar_eq, h00, h11, h10, dirichlet_triangle_upper_right38 a z hz]
  field_simp [hz, Complex.I_ne_zero]
  linear_combination z * hfree

end
end NlsGge.GK38
