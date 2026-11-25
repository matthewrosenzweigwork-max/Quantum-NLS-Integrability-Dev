                                                                                                                                                                                                                                                         
                                                                                
import Mathlib
import NlsGge.Hierarchy.ALGaussianNormalizer38

                                                                                            
                                                                                                       
                                                                                                        
                                                                                    
                                                                                          
                                                                                                
                                                                                              
                                                                                
                                                                    
                              

set_option autoImplicit false

open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

noncomputable def fourierMatrix (L : ℕ) [NeZero L] : Matrix (ZMod L) (ZMod L) ℂ :=
  fun j k => ZMod.stdAddChar (k * j)

theorem al043_stdConj {L : ℕ} [NeZero L] (x : ZMod L) :
    star (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  have h := AddChar.starComp_apply (R := ZMod L) (by rw [ZMod.ringChar_zmod_n]; exact NeZero.pos L)
    (φ := (ZMod.stdAddChar : AddChar (ZMod L) ℂ)) x
  rw [show star (ZMod.stdAddChar x : ℂ) = starRingEnd ℂ (ZMod.stdAddChar x) from rfl, h]
  simp [AddChar.inv_apply]

theorem al043_sum {L : ℕ} [NeZero L] (t : ZMod L) :
    ∑ k : ZMod L, ZMod.stdAddChar (t * k) = if t = 0 then (L : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod L) (R' := ℂ) (ψ := ZMod.stdAddChar) t
    (ZMod.isPrimitive_stdAddChar L)
  simp only [mul_comm] at h ⊢
  rw [h]
  split_ifs <;> simp [ZMod.card]

theorem al043_orth (L : ℕ) [NeZero L] :
    Matrix.conjTranspose (fourierMatrix L) * fourierMatrix L =
      (L : ℂ) • (1 : Matrix (ZMod L) (ZMod L) ℂ) := by
  ext i j
  have key : ∀ k : ZMod L, star (fourierMatrix L k i) * fourierMatrix L k j
      = ZMod.stdAddChar ((j - i) * k) := by
    intro k
    simp only [fourierMatrix]
    rw [al043_stdConj, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [Finset.sum_congr rfl (fun k _ => key k), al043_sum]
  by_cases h : i = j
  · subst h; simp
  · have h' : j - i ≠ 0 := fun h0 => h (by
      have := sub_eq_zero.1 h0; exact this.symm)
    simp [h, h']

theorem al043_detsq (L : ℕ) [NeZero L] :
    ‖Matrix.det (fourierMatrix L)‖ ^ 2 = (L : ℝ) ^ L := by
  have hmat : (ZMod.dft : (ZMod L → ℂ) ≃ₗ[ℂ] (ZMod L → ℂ)).toLinearMap
      = Matrix.toLin' (Matrix.of (fun k j : ZMod L => ZMod.stdAddChar (-(j * k)))) := by
    apply LinearMap.ext
    intro Φ
    funext k
    rw [LinearEquiv.coe_toLinearMap, ZMod.dft_apply, Matrix.toLin'_apply]
    simp [Matrix.mulVec, dotProduct, smul_eq_mul]
  have hNF : (Matrix.of (fun k j : ZMod L => ZMod.stdAddChar (-(j * k))))
      = (fourierMatrix L).map (starRingEnd ℂ) := by
    ext k j
    simp only [Matrix.of_apply, Matrix.map_apply, fourierMatrix]
    exact (al043_stdConj _).symm
  have hdet : Matrix.det (Matrix.of (fun k j : ZMod L => ZMod.stdAddChar (-(j * k))))
      = starRingEnd ℂ (Matrix.det (fourierMatrix L)) := by
    rw [hNF]
    exact (RingHom.map_det (starRingEnd ℂ) (fourierMatrix L)).symm
  have hdetC : LinearMap.det (Matrix.toLin' (Matrix.of (fun k j : ZMod L => ZMod.stdAddChar (-(j * k)))))
      = Matrix.det (Matrix.of (fun k j : ZMod L => ZMod.stdAddChar (-(j * k)))) :=
    LinearMap.det_toLin' _
  have hR : LinearMap.det (dftR38 (L := L)) = ‖Matrix.det (fourierMatrix L)‖ ^ 2 := by
    unfold dftR38
    rw [hmat, LinearMap.det_restrictScalars, hdetC, hdet,
      Algebra.norm_complex_apply, Complex.normSq_conj, Complex.normSq_eq_norm_sq]
  have h1 := abs_det_dftR38 (L := L)
  rw [hR] at h1
  rw [abs_of_nonneg (sq_nonneg _)] at h1
  exact h1

theorem al043 (L : ℕ) [NeZero L] :
    Matrix.conjTranspose (fourierMatrix L) * fourierMatrix L =
      (L : ℂ) • (1 : Matrix (ZMod L) (ZMod L) ℂ) ∧
    ‖Matrix.det (fourierMatrix L)‖ =
      Real.rpow (L : ℝ) ((L : ℝ) / 2) ∧
    (∀ z : ZMod L → ℂ, ∀ j : ZMod L,
      synthR38 z j = ((L : ℂ)⁻¹) * ∑ k, fourierMatrix L j k * z k) ∧
    |LinearMap.det (synthR38 (L := L)).toLinearMap| =
      ((L : ℝ)⁻¹) ^ (2 * L) * ‖Matrix.det (fourierMatrix L)‖ ^ 2 ∧
    |LinearMap.det (synthR38 (L := L)).toLinearMap| = ((L : ℝ)⁻¹) ^ L := by
  have hdetsq := al043_detsq L
  have hy : Real.rpow (L : ℝ) ((L : ℝ) / 2) ^ 2 = (L : ℝ) ^ L := by
    rw [show Real.rpow (L : ℝ) ((L : ℝ) / 2) = (L : ℝ) ^ ((L : ℝ) / 2) from rfl,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
    congr 1
    push_cast <;> ring
  have hnorm : ‖Matrix.det (fourierMatrix L)‖ = Real.rpow (L : ℝ) ((L : ℝ) / 2) :=
    (sq_eq_sq₀ (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)).1 (hdetsq.trans hy.symm)
  have hsyn : |LinearMap.det (synthR38 (L := L)).toLinearMap| = ((L : ℝ) ^ L)⁻¹ := by
    have h := congrArg abs (det_synth_mul38 (L := L))
    rw [abs_mul, abs_det_dftR38 (L := L), abs_one] at h
    exact eq_inv_of_mul_eq_one_left h
  refine ⟨al043_orth L, hnorm, ?_, ?_, ?_⟩
  · intro z j
    show ZMod.dft.symm z j = _
    rw [ZMod.invDFT_apply]
    simp only [fourierMatrix, smul_eq_mul]
  · rw [hsyn, hdetsq, pow_mul', inv_pow]
    field_simp <;> ring
  · rw [hsyn, inv_pow]

end NlsGge.ThirdConsultation.AL
