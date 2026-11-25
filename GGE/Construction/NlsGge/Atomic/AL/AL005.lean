                                                                                                                                              
                                                                                         
import Mathlib
import NlsGge.Hierarchy.ALFloquetMonotone38
import NlsGge.Hierarchy.ALMonodromyAlgebra38

                                                                                                                                                                                       
                                                                                   
                                                                                                           
                                                                                                                 
                                                           

set_option autoImplicit false
open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

theorem al005 {L : ℕ} [NeZero L] (α : ZMod L → ℂ)
    (hα : IsALField38 α) (z : ℂ) (hz : 1 < ‖z‖) :
    (∀ (w : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
      (alMonodromy38 α z).mulVec v = w • v → ‖w‖ ≠ 1) ∧
    ∃ wPlus wMinus : ℂ, wPlus ≠ wMinus ∧ wPlus * wMinus = 1 ∧ 1 < ‖wPlus‖ ∧ ‖wMinus‖ < 1 ∧
      ∀ w : ℂ,
        w ^ 2 - (alMonodromy38 α z).trace * w + 1 = 0 ↔ w = wPlus ∨ w = wMinus := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    linarith [norm_nonneg (1 : ℂ)]
  have hdet : (alMonodromy38 α z).det = 1 := det_alMonodromy38 hα hz0
  have hc1 : ∀ (w : ℂ) (v : Fin 2 → ℂ), v ≠ 0 →
      (alMonodromy38 α z).mulVec v = w • v → ‖w‖ ≠ 1 :=
    fun w v hv h => no_unimodular_multiplier38 α hα z hz w v hv h
  set M := alMonodromy38 α z with hM
  set t := M.trace with ht
  -- every root of the characteristic quadratic is a Floquet multiplier
  have hroot : ∀ w : ℂ, w ^ 2 - t * w + 1 = 0 → ‖w‖ ≠ 1 := by
    intro w hw
    have hdet_formula : (M - w • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det =
        M.det - w * M.trace + w ^ 2 := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
      simp [Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply]
      ring
    have hdw : (M - w • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
      rw [hdet_formula, hdet]
      linear_combination hw
    obtain ⟨v, hv, hv0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdw
    apply hc1 w v hv
    have h2 : M.mulVec v = (w • (1 : Matrix (Fin 2) (Fin 2) ℂ)).mulVec v :=
      sub_eq_zero.1 (by rw [← Matrix.sub_mulVec]; exact hv0)
    rw [h2]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.one_apply]

  refine ⟨hc1, ?_⟩
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (t ^ 2 - 4) (n := 2) (by norm_num)
  set a : ℂ := (t + s) / 2 with ha
  set b : ℂ := (t - s) / 2 with hb
  have hsum : a + b = t := by rw [ha, hb]; ring
  have hprod : a * b = 1 := by
    rw [ha, hb]
    have : (t + s) / 2 * ((t - s) / 2) = (t ^ 2 - s ^ 2) / 4 := by ring
    rw [this, hs]
    ring
  have hqa : a ^ 2 - t * a + 1 = 0 := by
    rw [ha]
    have : ((t + s) / 2) ^ 2 - t * ((t + s) / 2) + 1 = (s ^ 2 - t ^ 2) / 4 + 1 := by ring
    rw [this, hs]
    ring
  have hqb : b ^ 2 - t * b + 1 = 0 := by
    rw [hb]
    have : ((t - s) / 2) ^ 2 - t * ((t - s) / 2) + 1 = (s ^ 2 - t ^ 2) / 4 + 1 := by ring
    rw [this, hs]
    ring
  have ha1 : ‖a‖ ≠ 1 := hroot a hqa
  have hb1 : ‖b‖ ≠ 1 := hroot b hqb
  have hnorm : ‖a‖ * ‖b‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  have hab : a ≠ b := by
    intro h
    have hs0 : s = 0 := by
      have : a - b = s := by rw [ha, hb]; ring
      rw [h, sub_self] at this
      exact this.symm
    -- then a = b = t/2 and a^2 = 1, contradicting ‖a‖ ≠ 1
    have ha2 : a ^ 2 = 1 := by
      have : a ^ 2 = (t ^ 2) / 4 := by rw [ha, hs0]; ring
      rw [this]
      have ht2 : t ^ 2 = 4 := by
        have := hs
        rw [hs0] at this
        linear_combination -this
      rw [ht2]
      norm_num
    have : ‖a‖ = 1 := by
      have h2 : ‖a‖ ^ 2 = 1 := by rw [← norm_pow, ha2, norm_one]
      have hnn := norm_nonneg a
      nlinarith [h2, hnn]
    exact ha1 this
  by_cases hA : 1 < ‖a‖
  · refine ⟨a, b, hab, hprod, hA, ?_, ?_⟩
    · nlinarith [hnorm, norm_nonneg b, hA]
    · intro w
      constructor
      · intro hw
        have hfac : (w - a) * (w - b) = 0 := by
          linear_combination hw - w * hsum + hprod
        rcases mul_eq_zero.1 hfac with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (sub_eq_zero.1 h)
      · rintro (rfl | rfl)
        · exact hqa
        · exact hqb
  · have hA' : ‖a‖ < 1 := lt_of_le_of_ne (not_lt.1 hA) ha1
    refine ⟨b, a, hab.symm, by rw [mul_comm]; exact hprod, ?_, ?_, ?_⟩
    · nlinarith [hnorm, norm_nonneg a, hA']
    · exact hA'
    · intro w
      constructor
      · intro hw
        have hfac : (w - b) * (w - a) = 0 := by
          linear_combination hw - w * hsum + hprod
        rcases mul_eq_zero.1 hfac with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (sub_eq_zero.1 h)
      · rintro (rfl | rfl)
        · exact hqb
        · exact hqa

end NlsGge.ThirdConsultation.AL
