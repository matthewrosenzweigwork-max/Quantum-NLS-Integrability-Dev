import Mathlib

/- G6-028 SUPPORT 1 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6028Sup1Core.lean, namespace NlsGge.GKDefinitionDesign.G6028Aux. Mathlib only.
   Generic real-Hilbert steps of GK Theorem 19.1 / §20.2 (canonical relations => the Jacobian is symplectic):
   (1) `clm_eq_zero_of_basis`: a continuous real functional vanishing on a Hilbert basis vanishes (expansion
       HilbertBasis.hasSum_repr, as in landed G6001Aux.injective_of_biorth);
   (2) `form_eq_of_basis`: a bounded bilinear identity <J A x, A y> = <J x, y> on basis pairs holds everywhere;
   (3) `symplectic_of_adjoint`: if J∘J = -1, C is injective and the adjoint A = C† preserves <J ., .>, then so does C
       (C J C† = J by Riesz; then C† J C = J using injectivity of C only; no inverse operator is formed);
   (4) `real_inner_map_of_norm`: an additive norm-preserving map preserves the real inner product (real polarization),
       used to move the symplectic form through the complex Fourier isometry without identifying inner-product
       instances. -/
set_option autoImplicit false

open scoped InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6028Aux
noncomputable section

theorem clm_eq_zero_of_basis {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (d : HilbertBasis ι ℝ E) (f : E →L[ℝ] ℝ)
    (hf : ∀ i, f (d i) = 0) (x : E) : f x = 0 := by
  have h := (d.hasSum_repr x).mapL f
  have h0 : (fun i => f (d.repr x i • d i)) = fun _ => (0 : ℝ) := by
    funext i
    rw [map_smul, hf i, smul_zero]
  rw [h0] at h
  exact h.unique hasSum_zero

theorem form_eq_of_basis {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (d : HilbertBasis ι ℝ E) (J A : E →L[ℝ] E)
    (h : ∀ i j, inner ℝ (J (A (d i))) (A (d j)) = inner ℝ (J (d i)) (d j)) (x y : E) :
    inner ℝ (J (A x)) (A y) = inner ℝ (J x) y := by
  have h1 : ∀ (i : ι) (y : E), inner ℝ (J (A (d i))) (A y) = inner ℝ (J (d i)) y := by
    intro i y
    have hz := clm_eq_zero_of_basis d
      ((innerSL ℝ (J (A (d i)))).comp A - innerSL ℝ (J (d i)))
      (fun j => by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
          innerSL_apply_apply, h i j, sub_self]) y
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      innerSL_apply_apply, sub_eq_zero] at hz
    exact hz
  have hz := clm_eq_zero_of_basis d
    ((innerSL ℝ (A y)).comp (J.comp A) - (innerSL ℝ y).comp J)
    (fun i => by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
        innerSL_apply_apply, sub_eq_zero]
      linarith [h1 i y, real_inner_comm (J (A (d i))) (A y), real_inner_comm (J (d i)) y]) x
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    innerSL_apply_apply, sub_eq_zero] at hz
  linarith [hz, real_inner_comm (J (A x)) (A y), real_inner_comm (J x) y]

theorem symplectic_of_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (J C : E →L[ℝ] E)
    (hJJ : ∀ x, J (J x) = -x) (hinj : Function.Injective C)
    (hA : ∀ x y, inner ℝ (J (C.adjoint x)) (C.adjoint y) = inner ℝ (J x) y) (h k : E) :
    inner ℝ (J (C h)) (C k) = inner ℝ (J h) k := by
  have hstar : ∀ x, C (J (C.adjoint x)) = J x := by
    intro x
    apply ext_inner_right ℝ
    intro y
    rw [← ContinuousLinearMap.adjoint_inner_right C (J (C.adjoint x)) y, hA]
  have hw : J (C.adjoint (J (C h))) = -h := by
    apply hinj
    rw [hstar, hJJ, map_neg]
  have hw2 : C.adjoint (J (C h)) = J h := by
    have h2 := congrArg J hw
    rw [hJJ, map_neg] at h2
    exact neg_injective h2
  rw [← ContinuousLinearMap.adjoint_inner_left C k (J (C h)), hw2]

theorem real_inner_map_of_norm {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (T : F →+ G) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (x y : F) : inner ℝ (T x) (T y) = inner ℝ x y := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, hT, hT, hT]

end
end G6028Aux
end NlsGge.GKDefinitionDesign
