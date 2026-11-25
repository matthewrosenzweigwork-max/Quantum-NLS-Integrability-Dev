import Mathlib
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.G5.G5017Host

                                                                                                                  
                                                                                               
                                                                                                                               
                                                                                                                                 
                                                                                        
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem norm_pairGradientProjection_le (v : PotPair) :
  ‖pairGradientProjection v‖ ≤ Real.sqrt 2 * pairGradientNorm v := by
  unfold pairGradientProjection pairGradientNorm
  have h1 : ‖star v.1 + v.2‖ ≤ ‖v.1‖ + ‖v.2‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [show ‖star v.1‖ = ‖v.1‖ from starLp.norm_map v.1]
  refine h1.trans ?_
  rw [← Real.sqrt_mul (by norm_num)]
  calc ‖v.1‖ + ‖v.2‖ = Real.sqrt ((‖v.1‖ + ‖v.2‖) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (2 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2)) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (‖v.1‖ - ‖v.2‖)])

theorem inner_star_star_g5012 (x y : PhysicalL2) :
    inner ℂ (star x) (star y) = starRingEnd ℂ (inner ℂ x y) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star x, MeasureTheory.Lp.coeFn_star y] with t hx hy
  simp [hx, hy]

theorem real_inner_eq_re_inner_g5012 (x y : PhysicalL2) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h := integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) x y)
  refine Eq.trans ?_ h
  congr 1

theorem gradient_realSlice_re (f : PotPair → ℂ) (u : PhysicalL2)
    (hf : DifferentiableAt ℂ f (realSlice u)) :
  gradient (fun v : PhysicalL2 => (f (realSlice v)).re) u =
    pairGradientProjection (pairGradient f (realSlice u)) := by
  set L : PotPair →L[ℂ] ℂ := fderiv ℂ f (realSlice u) with hL
  set w : PhysicalL2 := pairGradientProjection (pairGradient f (realSlice u)) with hw
  have h1 : HasFDerivAt (fun v : PhysicalL2 => f (realSlice v))
      ((L.restrictScalars ℝ).comp (realSlice : PhysicalL2 →L[ℝ] PotPair)) u :=
    HasFDerivAt.comp (g := f) u (hf.hasFDerivAt.restrictScalars ℝ) realSlice.hasFDerivAt
  have h2 := Complex.reCLM.hasFDerivAt.comp u h1
  have hA : ∀ x : PhysicalL2, L (x, 0) = inner ℂ (star (pairGradientCLM L).1) x := by
    intro x
    have e : star (pairGradientCLM L).1 = (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (L.comp (ContinuousLinearMap.inl ℂ PhysicalL2 PhysicalL2)) := star_star _
    rw [e, InnerProductSpace.toDual_symm_apply]
    rfl
  have hB : ∀ y : PhysicalL2, L (0, y) = inner ℂ (star (pairGradientCLM L).2) y := by
    intro y
    have e : star (pairGradientCLM L).2 = (InnerProductSpace.toDual ℂ PhysicalL2).symm
        (L.comp (ContinuousLinearMap.inr ℂ PhysicalL2 PhysicalL2)) := star_star _
    rw [e, InnerProductSpace.toDual_symm_apply]
    rfl
  have key : Complex.reCLM.comp ((L.restrictScalars ℝ).comp (realSlice : PhysicalL2 →L[ℝ] PotPair)) =
      InnerProductSpace.toDual ℝ PhysicalL2 w := by
    refine ContinuousLinearMap.ext fun h => ?_
    rw [InnerProductSpace.toDual_apply_apply, real_inner_eq_re_inner_g5012]
    have hs : ((h, star h) : PotPair) = ((h, 0) : PotPair) + ((0, star h) : PotPair) := by
      ext <;> simp
    have hlhs : (Complex.reCLM.comp ((L.restrictScalars ℝ).comp (realSlice : PhysicalL2 →L[ℝ] PotPair))) h =
        (L ((h, star h) : PotPair)).re := rfl
    rw [hlhs, hs, map_add, hA, hB, Complex.add_re, hw]
    unfold pairGradientProjection pairGradient
    rw [inner_add_left, Complex.add_re, inner_star_star_g5012, Complex.conj_re]
  have hg : HasGradientAt (fun v : PhysicalL2 => (f (realSlice v)).re) w u := by
    rw [hasGradientAt_iff_hasFDerivAt, ← key]
    exact h2
  exact hg.gradient

end
end NlsGge.GKDefinitionDesign
