import Mathlib
import NlsGge.ThirdConsultation.G2.Reparam032B

                                                                                              
                                                                                              
                                                                                                  
                                                                                                  
                                                                                             
set_option autoImplicit false

open MeasureTheory Metric Filter Topology
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Lift
noncomputable section

theorem liftRate_pos (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (θ : ℝ) :
    0 < liftRate w R θ := by
  unfold liftRate
  refine div_pos (mul_pos hR ?_) (normSq_liftF_pos w R hR hw θ)
  have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) w‖ = ‖w‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]
  have h2 := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) w)
  rw [h1] at h2
  have h3 := neg_abs_le (Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) w).re
  linarith

theorem liftAngle_continuous (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) :
    Continuous (liftAngle w R) :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_liftAngle w R hR hw θ).continuousAt

theorem liftAngle_int (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) (n : ℤ) :
    liftAngle w R (2 * π * (n : ℝ)) = liftAngle w R 0 + 2 * π * (n : ℝ) := by
  refine Int.induction_on n ?_ ?_ ?_
  · simp
  · intro i ih
    have h := liftAngle_periodic w R hR hw (2 * π * (((i : ℤ)) : ℝ))
    have e : 2 * π * (((i : ℤ) + 1 : ℤ) : ℝ) = 2 * π * (((i : ℤ)) : ℝ) + 2 * π := by
      push_cast; ring
    rw [e, h, ih]; push_cast; ring
  · intro i ih
    have h := liftAngle_periodic w R hR hw (2 * π * (((-(i : ℤ)) - 1 : ℤ) : ℝ))
    have e : 2 * π * (((-(i : ℤ)) - 1 : ℤ) : ℝ) + 2 * π = 2 * π * (((-(i : ℤ)) : ℤ) : ℝ) := by
      push_cast; ring
    rw [e, ih] at h
    push_cast at h ⊢
    linarith

theorem liftAngle_surj (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) :
    Function.Surjective (liftAngle w R) := by
  intro x
  have hpos : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℤ, 2 * π * (n : ℝ) ≤ x - liftAngle w R 0 ∧
      x - liftAngle w R 0 < 2 * π * ((n : ℝ) + 1) := by
    refine ⟨⌊(x - liftAngle w R 0) / (2 * π)⌋, ?_, ?_⟩
    · have h1 := Int.floor_le ((x - liftAngle w R 0) / (2 * π))
      rw [le_div_iff₀ hpos] at h1
      linarith
    · have h2 := Int.lt_floor_add_one ((x - liftAngle w R 0) / (2 * π))
      rw [div_lt_iff₀ hpos] at h2
      linarith
  have hA := liftAngle_int w R hR hw n
  have hB := liftAngle_periodic w R hR hw (2 * π * (n : ℝ))
  have hab : 2 * π * (n : ℝ) ≤ 2 * π * (n : ℝ) + 2 * π := by linarith
  have hIVT := intermediate_value_Icc hab (liftAngle_continuous w R hR hw).continuousOn
  have hx : x ∈ Set.Icc (liftAngle w R (2 * π * (n : ℝ)))
      (liftAngle w R (2 * π * (n : ℝ) + 2 * π)) := by
    rw [hB, hA, Set.mem_Icc]
    constructor <;> linarith
  obtain ⟨θ, -, hθ⟩ := hIVT hx
  exact ⟨θ, hθ⟩

/-- INV032: inverse β of the lifted angle; C¹ with β' = 1/liftRate(β), 2π-equivariant. -/
theorem lift_inverse (w : ℂ) (R : ℝ) (hR : 0 < R) (hw : ‖w‖ < R) :
    ∃ β : ℝ → ℝ, (∀ x, liftAngle w R (β x) = x) ∧ (∀ θ, β (liftAngle w R θ) = θ) ∧
      StrictMono β ∧ (∀ x, HasDerivAt β (1 / liftRate w R (β x)) x) ∧
      (∀ x, β (x + 2 * π) = β x + 2 * π) ∧ Continuous β := by
  have hmono : StrictMono (liftAngle w R) :=
    strictMono_of_deriv_pos fun x => by
      rw [(hasDerivAt_liftAngle w R hR hw x).deriv]
      exact liftRate_pos w R hR hw x
  choose β hβ using liftAngle_surj w R hR hw
  have hleft : ∀ θ, β (liftAngle w R θ) = θ := fun θ => hmono.injective (hβ _)
  have hβmono : StrictMono β := by
    intro x y h
    rw [← hmono.lt_iff_lt, hβ, hβ]
    exact h
  have hsurjβ : Function.Surjective β := fun θ => ⟨liftAngle w R θ, hleft θ⟩
  have hβcont : Continuous β := hβmono.monotone.continuous_of_surjective hsurjβ
  refine ⟨β, hβ, hleft, hβmono, ?_, ?_, hβcont⟩
  · intro x
    have hd := HasDerivAt.of_local_left_inverse (f := liftAngle w R) (g := β)
      (f' := liftRate w R (β x)) (a := x) hβcont.continuousAt
      (hasDerivAt_liftAngle w R hR hw (β x)) (liftRate_pos w R hR hw (β x)).ne'
      (Eventually.of_forall fun y => hβ y)
    rw [one_div]
    exact hd
  · intro x
    apply hmono.injective
    rw [hβ (x + 2 * π), liftAngle_periodic w R hR hw (β x), hβ x]

/-- Selftest: the hypotheses are satisfiable (w = 0, R = 1), so the conclusion is not vacuous. -/
example : ∃ β : ℝ → ℝ, Continuous β := by
  obtain ⟨β, -, -, -, -, -, h⟩ := lift_inverse 0 1 one_pos (by simp)
  exact ⟨β, h⟩

end

end G2032Lift
end NlsGge.GKDefinitionDesign

