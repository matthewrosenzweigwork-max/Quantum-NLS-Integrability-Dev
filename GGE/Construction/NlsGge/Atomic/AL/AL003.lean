                                                                                                                                                                                                                                                         
                                                                                
import Mathlib
import NlsGge.Hierarchy.ALTransferDefs38

                                                                                            
                                                                                                
                                                                                               
                                                                                
                                                                                                            
                                                                                                 
                                                      
                              

set_option autoImplicit false

open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

theorem al003_J_herm : (!![(1 : ℂ), 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-- Positivity of the quadratic form of a Hermitian 2x2 matrix with positive (0,0) entry
    and positive determinant, written with the entries as in the proof of `al003`. -/
theorem al003_pd (d01 d11 : ℂ) (r dr : ℝ) (hr : 0 < r) (hdr : 0 < dr)
    (hdet : (r : ℂ) * d11 - d01 * starRingEnd ℂ d01 = (dr : ℂ)) (x y : ℂ)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < (starRingEnd ℂ x * ((r : ℂ) * x + d01 * y)
      + starRingEnd ℂ y * (starRingEnd ℂ d01 * x + d11 * y)).re := by
  have key : (r : ℂ) * (starRingEnd ℂ x * ((r : ℂ) * x + d01 * y)
      + starRingEnd ℂ y * (starRingEnd ℂ d01 * x + d11 * y))
      = ((Complex.normSq ((r : ℂ) * x + d01 * y) : ℝ) : ℂ)
        + ((dr * Complex.normSq y : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [map_add, map_mul, Complex.conj_ofReal]
    linear_combination (starRingEnd ℂ y * y) * hdet
  have hre := congrArg Complex.re key
  rw [Complex.re_ofReal_mul, Complex.add_re (↑(Complex.normSq ((r : ℂ) * x + d01 * y))),
    Complex.ofReal_re, Complex.ofReal_re] at hre
  have hpos : 0 < Complex.normSq ((r : ℂ) * x + d01 * y) + dr * Complex.normSq y := by
    have h1 := Complex.normSq_nonneg ((r : ℂ) * x + d01 * y)
    by_cases hy : y = 0
    · have hx : x ≠ 0 := hxy.resolve_right (fun h => h hy)
      have hz' : (r : ℂ) * x + d01 * y ≠ 0 := by
        rw [hy, mul_zero, add_zero]
        exact mul_ne_zero (Complex.ofReal_ne_zero.2 hr.ne') hx
      have h3 := Complex.normSq_pos.2 hz'
      have h2 : 0 ≤ dr * Complex.normSq y := mul_nonneg hdr.le (Complex.normSq_nonneg y)
      linarith
    · have h3 := Complex.normSq_pos.2 hy
      nlinarith [mul_pos hdr h3]
  have hpos2 : 0 < r * (starRingEnd ℂ x * ((r : ℂ) * x + d01 * y)
      + starRingEnd ℂ y * (starRingEnd ℂ d01 * x + d11 * y)).re := by
    rw [hre]; exact hpos
  exact pos_of_mul_pos_right hpos2 hr.le

theorem al003 (a z : ℂ) (ha : ‖a‖ < 1) (hz : 1 < ‖z‖) :
  let J : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]
  let D := (alTransfer38 a z).conjTranspose * J * alTransfer38 a z - J
  D.IsHermitian ∧
  D 0 0 = (((‖z‖^2-1)/(1-‖a‖^2) : ℝ) : ℂ) ∧
  D.det = ((((‖z‖^2-1)^2)/(‖z‖^2*(1-‖a‖^2)) : ℝ) : ℂ) ∧
  0 < (D 0 0).re ∧ 0 < D.det.re ∧
  ∀ v : Fin 2 → ℂ, v ≠ 0 →
    0 < (dotProduct (fun i => star (v i)) (D.mulVec v)).re := by
  intro J D
  have hp1 : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hQ : 1 < ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hw0 : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz0
  have hab : a * starRingEnd ℂ a = ((‖a‖ : ℂ)) ^ 2 := Complex.mul_conj' a
  have hzz : starRingEnd ℂ z * z = ((‖z‖ : ℂ)) ^ 2 := by
    rw [mul_comm]; exact Complex.mul_conj' z
  have hs2 : Real.sqrt (1 - ‖a‖ ^ 2) * Real.sqrt (1 - ‖a‖ ^ 2) = 1 - ‖a‖ ^ 2 :=
    Real.mul_self_sqrt hp1.le
  have hs_pos : 0 < Real.sqrt (1 - ‖a‖ ^ 2) := Real.sqrt_pos.2 hp1
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ)⁻¹ := ⟨_, rfl⟩
  have hcs : starRingEnd ℂ c = c := by
    rw [hc, map_inv₀, Complex.conj_ofReal]
  have hcc : c * c * (1 - (‖a‖ : ℂ) ^ 2) = 1 := by
    have hss : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ)
        = 1 - (‖a‖ : ℂ) ^ 2 := by
      rw [← Complex.ofReal_mul, hs2]; push_cast <;> ring
    have hne : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs_pos.ne'
    rw [hc, ← hss]
    field_simp
  have hcc' : c * c * (1 - a * starRingEnd ℂ a) = 1 := by rw [hab]; exact hcc
  have hne1 : (1 : ℂ) - a * starRingEnd ℂ a ≠ 0 := by
    intro h
    have := hcc'
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have hT : alTransfer38 a z
      = c • (!![z, a; starRingEnd ℂ a, z⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hc]; rfl
  have e00 : D 0 0 = c * c * (starRingEnd ℂ z * z - a * starRingEnd ℂ a) - 1 := by
    simp [D, J, hT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.star_def, hcs] <;> ring
  have e01 : D 0 1 = c * c * a * (starRingEnd ℂ z - z⁻¹) := by
    simp [D, J, hT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.star_def, hcs] <;> ring
  have e11 : D 1 1 = c * c * (a * starRingEnd ℂ a - (starRingEnd ℂ z)⁻¹ * z⁻¹) + 1 := by
    simp [D, J, hT, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.star_def, hcs] <;> ring
  have herm : D.IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_mul _ al003_J_herm).sub al003_J_herm
  have hD10 : D 1 0 = starRingEnd ℂ (D 0 1) := by
    have h := herm.apply 0 1
    rw [← h]
    exact (star_star (D 1 0)).symm
  have e10 : D 1 0 = c * c * starRingEnd ℂ a * (z - (starRingEnd ℂ z)⁻¹) := by
    rw [hD10, e01]
    simp [map_mul, map_sub, map_inv₀, hcs] <;> ring
  have hzu : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
  have hwv : starRingEnd ℂ z * (starRingEnd ℂ z)⁻¹ = 1 := mul_inv_cancel₀ hw0
  have hdetc : D.det = (((‖z‖^2-1)^2/(‖z‖^2*(1-‖a‖^2)) : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, e00, e11, e01, e10]
    push_cast
    rw [← hzz, ← hab]
    have hden : (starRingEnd ℂ z * z) * (1 - a * starRingEnd ℂ a) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hw0 hz0) hne1
    rw [eq_div_iff hden]
    linear_combination
      (-(starRingEnd ℂ z * z) * (a ^ 2 * (starRingEnd ℂ a) ^ 2 * c ^ 2
        - a * starRingEnd ℂ a * c ^ 2 * z⁻¹ * z - a * starRingEnd ℂ a * c ^ 2
          * (starRingEnd ℂ z)⁻¹ * starRingEnd ℂ z + a * starRingEnd ℂ a
        + c ^ 2 * z⁻¹ * (starRingEnd ℂ z)⁻¹ * starRingEnd ℂ z * z
        - z⁻¹ * (starRingEnd ℂ z)⁻¹ + z⁻¹ * z + (starRingEnd ℂ z)⁻¹ * starRingEnd ℂ z
        - starRingEnd ℂ z * z - 1)) * hcc'
      + (-(starRingEnd ℂ z) * (c ^ 2 * (starRingEnd ℂ z)⁻¹ * starRingEnd ℂ z * z
        - c ^ 2 * z - (starRingEnd ℂ z)⁻¹ + z)) * hzu
      + (-(starRingEnd ℂ z * z) + 1) * hwv
  have hr : 0 < (‖z‖ ^ 2 - 1) / (1 - ‖a‖ ^ 2) := div_pos (by linarith) hp1
  have hdr : 0 < (‖z‖ ^ 2 - 1) ^ 2 / (‖z‖ ^ 2 * (1 - ‖a‖ ^ 2)) :=
    div_pos (pow_pos (by linarith) 2) (mul_pos (by nlinarith [norm_nonneg z]) hp1)
  have hD00r : D 0 0 = (((‖z‖ ^ 2 - 1) / (1 - ‖a‖ ^ 2) : ℝ) : ℂ) := by
    rw [e00]
    push_cast
    rw [← hzz, ← hab, eq_div_iff hne1]
    linear_combination (starRingEnd ℂ z * z - a * starRingEnd ℂ a) * hcc'
  refine ⟨herm, hD00r, hdetc, ?_, ?_, ?_⟩
  · rw [hD00r, Complex.ofReal_re]; exact hr
  · rw [hdetc, Complex.ofReal_re]; exact hdr
  · intro v hv
    have hxy : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hv
      funext i
      fin_cases i <;> simp [h.1, h.2]
    have hdot : dotProduct (fun i => star (v i)) (D.mulVec v)
        = starRingEnd ℂ (v 0) * (D 0 0 * v 0 + D 0 1 * v 1)
          + starRingEnd ℂ (v 1) * (D 1 0 * v 0 + D 1 1 * v 1) := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Complex.star_def] <;> ring
    have hdetpd : (((‖z‖ ^ 2 - 1) / (1 - ‖a‖ ^ 2) : ℝ) : ℂ) * D 1 1
        - D 0 1 * starRingEnd ℂ (D 0 1)
        = (((‖z‖ ^ 2 - 1) ^ 2 / (‖z‖ ^ 2 * (1 - ‖a‖ ^ 2)) : ℝ) : ℂ) := by
      have h := hdetc
      rw [Matrix.det_fin_two, hD00r, hD10] at h
      exact h
    rw [hdot, hD00r, hD10]
    exact al003_pd (D 0 1) (D 1 1) _ _ hr hdr hdetpd (v 0) (v 1) hxy

end NlsGge.ThirdConsultation.AL
