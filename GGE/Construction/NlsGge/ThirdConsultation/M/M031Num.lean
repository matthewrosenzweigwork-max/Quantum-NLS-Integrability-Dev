import Mathlib
import NlsGge.Atomic.LIB.LIB028

   
                                                                                                                     

                                                                                                                   
                                                                                           
                                                         
                                                                                                                    
                                                                                                       
                                                                             
  

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026 NlsGge.Atomic.LIB027

namespace NlsGge.ThirdConsultation.M

theorem sourceInterval_norm_sq_eq_integral (f : SourceIntervalL2) :
    ‖f‖ ^ 2 = ∫ x in Ioc (0 : ℝ) 1, ‖f x‖ ^ 2 := by
  have h := sourceInterval_inner_eq_integral f f
  rw [inner_self_eq_norm_sq_to_K, intervalIntegral.integral_of_le zero_le_one] at h
  have h2 : (fun x => star (f x) * f x) = fun x => (((‖f x‖ ^ 2 : ℝ)) : ℂ) := by
    funext x
    rw [show star (f x) = (starRingEnd ℂ) (f x) from rfl, Complex.conj_mul']
    push_cast
    ring
  rw [h2, integral_complex_ofReal] at h
  have h' : ((‖f‖ ^ 2 : ℝ) : ℂ) = ((∫ x in Ioc (0 : ℝ) 1, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
    exact h
  exact Complex.ofReal_injective h'

theorem h1PairValue_norm_sq (g : H1Pair) :
    ‖h1PairValue g‖ ^ 2 = ‖(g true).value‖ ^ 2 + ‖(g false).value‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_bool]
  rfl

theorem isRealType_zero : IsRealType (0 : SourcePairL2) := by
  unfold IsRealType
  simp only [WithLp.ofLp_zero, Pi.zero_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (0 : SourceIntervalL2), Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))]
    with x h1 h2
  rw [h1, Pi.star_apply, h2]
  simp

/-- E1: the imaginary part of an eigenvalue is carried by the potential term alone. -/
theorem zs_eigen_im_eq (P : SourcePairL2) (bc : ZSBoundaryCondition) (g : H1Pair)
    (hg : HasZSBoundaryCondition bc g) (x : ℂ) (heig : zsApply P g = x • h1PairValue g) :
    x.im * ‖h1PairValue g‖ ^ 2 =
      (inner ℂ (h1PairValue g) (zsApply P g) - inner ℂ (h1PairValue g) (zsApply 0 g)).im := by
  have hsym := NlsGge.Atomic.LIB028.zs_boundary_domain_symmetric isRealType_zero bc g g hg hg
  have hc := inner_conj_symm (𝕜 := ℂ) (h1PairValue g) (zsApply 0 g)
  rw [hsym] at hc
  have hreal : (inner ℂ (h1PairValue g) (zsApply 0 g)).im = 0 := Complex.conj_eq_iff_im.mp hc
  have hx : inner ℂ (h1PairValue g) (zsApply P g) = x * ((‖h1PairValue g‖ : ℂ)) ^ 2 := by
    rw [heig, inner_smul_right, inner_self_eq_norm_sq_to_K]
    rfl
  rw [Complex.sub_im, hreal, sub_zero, hx, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- E2: the potential term is bounded by the a.e. sup bounds of the two components. -/
theorem zs_potential_inner_le (P : SourcePairL2) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), ‖P true t‖ ≤ M₁)
    (h₂ : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), ‖P false t‖ ≤ M₂) (g : H1Pair) :
    ‖inner ℂ (h1PairValue g) (zsApply P g) - inner ℂ (h1PairValue g) (zsApply 0 g)‖ ≤
      (M₁ + M₂) / 2 * ‖h1PairValue g‖ ^ 2 := by
  have hI (φ : SourcePairL2) : Integrable (fun x =>
      star ((g true).value x) *
          zsExpression φ (fun c x => (g c).value x) (fun c x => (g c).derivative x) true x +
        star ((g false).value x) *
          zsExpression φ (fun c x => (g c).value x) (fun c x => (g c).derivative x) false x)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((Lp.memLp (g true).value).star.integrable_mul (zsExpression_memLp φ g true)).add
      ((Lp.memLp (g false).value).star.integrable_mul (zsExpression_memLp φ g false))
  have hz : ∀ c : Bool, ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), (0 : SourcePairL2) c x = 0 := by
    intro c
    have h0 := Lp.coeFn_zero ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))
    filter_upwards [h0] with x hx
    exact hx
  have hint : inner ℂ (h1PairValue g) (zsApply P g) - inner ℂ (h1PairValue g) (zsApply 0 g) =
      ∫ x in Ioc (0 : ℝ) 1, (star ((g true).value x) * (P true x * (g false).value x) +
        star ((g false).value x) * (P false x * (g true).value x)) := by
    rw [zs_action_right_pairing, zs_action_right_pairing, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one, ← integral_sub (hI P) (hI 0)]
    apply integral_congr_ae
    filter_upwards [hz true, hz false] with x hx1 hx2
    simp only [zsExpression, hx1, hx2, Bool.not_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    ring
  have hA : Integrable (fun x => ‖(g true).value x‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (Lp.memLp (g true).value).norm.integrable_sq
  have hB : Integrable (fun x => ‖(g false).value x‖ ^ 2) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (Lp.memLp (g false).value).norm.integrable_sq
  rw [hint, h1PairValue_norm_sq, sourceInterval_norm_sq_eq_integral,
    sourceInterval_norm_sq_eq_integral, ← integral_add hA hB, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall (fun x => norm_nonneg _))
    ((hA.add hB).const_mul _) ?_
  filter_upwards [h₁, h₂] with x hx1 hx2
  set a := (g true).value x
  set b := (g false).value x
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have e1 : ‖star a * (P true x * b)‖ ≤ M₁ * (‖a‖ * ‖b‖) := by
    rw [norm_mul, norm_mul, norm_star]
    calc ‖a‖ * (‖P true x‖ * ‖b‖) = ‖P true x‖ * (‖a‖ * ‖b‖) := by ring
      _ ≤ M₁ * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_right hx1 (by positivity)
  have e2 : ‖star b * (P false x * a)‖ ≤ M₂ * (‖a‖ * ‖b‖) := by
    rw [norm_mul, norm_mul, norm_star]
    calc ‖b‖ * (‖P false x‖ * ‖a‖) = ‖P false x‖ * (‖a‖ * ‖b‖) := by ring
      _ ≤ M₂ * (‖a‖ * ‖b‖) := mul_le_mul_of_nonneg_right hx2 (by positivity)
  have e3 : ‖a‖ * ‖b‖ ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  have e4 : (M₁ + M₂) * (‖a‖ * ‖b‖) ≤ (M₁ + M₂) * ((‖a‖ ^ 2 + ‖b‖ ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left e3 (by linarith)
  calc ‖star a * (P true x * b) + star b * (P false x * a)‖
      ≤ ‖star a * (P true x * b)‖ + ‖star b * (P false x * a)‖ := norm_add_le _ _
    _ ≤ (M₁ + M₂) * (‖a‖ * ‖b‖) := by linarith
    _ ≤ (M₁ + M₂) / 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by linarith

end NlsGge.ThirdConsultation.M

end
