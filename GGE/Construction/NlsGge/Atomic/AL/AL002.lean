                                                                                                                                                                                                                                                         
                                                                                
import Mathlib
import NlsGge.Hierarchy.ALMonodromyAlgebra38

                                                                                            
                               
                                                                                                          
                                                                                            
                                                                                                    
                                                                                

set_option autoImplicit false

open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

theorem al002_sigma_sq :
    (!![(0 : ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![(0 : ℂ), 1; 1, 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem al002_step (a z : ℂ) :
    alTransfer38 a (star (z⁻¹)) =
      !![(0 : ℂ), 1; 1, 0] * (alTransfer38 a z).map (starRingEnd ℂ) * !![(0 : ℂ), 1; 1, 0] := by
  unfold alTransfer38
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.head_cons, Matrix.head_fin_const] <;>
    simp [Complex.star_def, map_mul, map_inv₀, Complex.conj_ofReal, star_inv₀] <;> ring

theorem al002_conj_mul (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    !![(0 : ℂ), 1; 1, 0] * (X * Y) * !![(0 : ℂ), 1; 1, 0]
      = (!![(0 : ℂ), 1; 1, 0] * X * !![(0 : ℂ), 1; 1, 0])
        * (!![(0 : ℂ), 1; 1, 0] * Y * !![(0 : ℂ), 1; 1, 0]) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const] <;> ring

theorem al002_partial {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) (k : ℕ) :
    !![(0 : ℂ), 1; 1, 0] * (alPartial38 α z k).map (starRingEnd ℂ) * !![(0 : ℂ), 1; 1, 0]
      = alPartial38 α (star (z⁻¹)) k := by
  induction k with
  | zero =>
    simp only [alPartial38]
    rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _), Matrix.mul_one]
    exact al002_sigma_sq
  | succ k ih =>
    simp only [alPartial38]
    rw [Matrix.map_mul, al002_conj_mul, ← al002_step (α (k : ZMod L)) z, ih]

theorem al002 {L : ℕ} [NeZero L] (α : ZMod L → ℂ)
    (hα : IsALField38 α) :
  let σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
  let σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]
  (∀ z : ℂ, z ≠ 0 →
    alMonodromy38 α (star (z⁻¹)) =
      σ₁ * (alMonodromy38 α z).map (starRingEnd ℂ) * σ₁) ∧
  (∀ z : ℂ, alMonodromy38 α (-z) =
    (-1 : ℂ)^L • (σ₃ * alMonodromy38 α z * σ₃)) ∧
  (∀ θ : ℝ,
    ((alMonodromy38 α (Complex.exp ((θ : ℂ)*Complex.I))).trace / 2).im = 0) ∧
  (∀ θ : ℝ,
    ‖(alMonodromy38 α (Complex.exp (((θ+Real.pi : ℝ) : ℂ)*Complex.I))).trace / 2‖ =
    ‖(alMonodromy38 α (Complex.exp ((θ : ℂ)*Complex.I))).trace / 2‖) := by
  intro σ₁ σ₃
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z _
    exact (al002_partial α z L).symm
  · intro z
    exact alMonodromy38_neg α z
  · intro θ
    have hz : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    have h := alMonodromy38_trace_im α hz
    rw [Complex.div_ofNat_im, h]
    simp
  · intro θ
    have he : Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I)
        = -Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [show (((θ + Real.pi : ℝ)) : ℂ) * Complex.I
          = (θ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [he, trace_alMonodromy38_neg, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul]

end NlsGge.ThirdConsultation.AL
