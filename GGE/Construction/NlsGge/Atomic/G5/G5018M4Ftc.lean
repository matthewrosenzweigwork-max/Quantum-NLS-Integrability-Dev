import Mathlib
import NlsGge.ThirdConsultation.G3.G3015Support
import NlsGge.ThirdConsultation.G3.G3005C6Core

                                                                                                                    
                                                                                                                               
                                                                                                                                     
                                                                                                                               
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018m4_ftc1d (Q : ℂ → ℂ) (c : ℂ) (R : ℝ) (hQ : AnalyticOnNhd ℂ Q (ball c R))
    (a0 μ0 b0 ω0 dμ : ℂ) (r : ℝ → ℂ)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a0 + (t : ℂ) * (μ0 - a0) ∈ ball c R)
    (hω : ω0 ≠ 0) (hωsq : ω0 ^ 2 = μ0 - a0)
    (hrc : ContinuousOn r (Icc (0 : ℝ) 1)) (hr0 : ∀ t ∈ Icc (0 : ℝ) 1, r t ≠ 0)
    (hrsq : ∀ t ∈ Icc (0 : ℝ) 1, r t ^ 2 = a0 + (t : ℂ) * (μ0 - a0) - b0) :
    IntervalIntegrable (fun t : ℝ => dμ * (ω0 * (t : ℂ) * deriv Q (a0 + (t : ℂ) * (μ0 - a0)) / r t
        + Q (a0 + (t : ℂ) * (μ0 - a0)) / (2 * ω0 * r t)
        - Q (a0 + (t : ℂ) * (μ0 - a0)) * ω0 * (t : ℂ) / (2 * r t ^ 3)) / (Real.sqrt t : ℂ))
      volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, dμ * (ω0 * (t : ℂ) * deriv Q (a0 + (t : ℂ) * (μ0 - a0)) / r t
        + Q (a0 + (t : ℂ) * (μ0 - a0)) / (2 * ω0 * r t)
        - Q (a0 + (t : ℂ) * (μ0 - a0)) * ω0 * (t : ℂ) / (2 * r t ^ 3)) / (Real.sqrt t : ℂ)) =
      dμ * Q μ0 / (ω0 * r 1) := by
  obtain ⟨z, hzdef⟩ : ∃ z : ℝ → ℂ, z = fun t : ℝ => a0 + (t : ℂ) * (μ0 - a0) := ⟨_, rfl⟩
  have hzc : Continuous z := by rw [hzdef]; fun_prop
  have hzb : ∀ t ∈ Icc (0 : ℝ) 1, z t ∈ ball c R := fun t ht => by rw [hzdef]; exact hseg t ht
  have hQc : ContinuousOn (fun t : ℝ => Q (z t)) (Icc (0 : ℝ) 1) :=
    hQ.continuousOn.comp hzc.continuousOn hzb
  have hQ'c : ContinuousOn (fun t : ℝ => deriv Q (z t)) (Icc (0 : ℝ) 1) :=
    (hQ.deriv).continuousOn.comp hzc.continuousOn hzb
  have hcast : ContinuousOn (fun t : ℝ => (t : ℂ)) (Icc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.continuousOn
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℂ, H = fun t : ℝ => dμ * (ω0 * (t : ℂ) * deriv Q (z t) / r t
        + Q (z t) / (2 * ω0 * r t) - Q (z t) * ω0 * (t : ℂ) / (2 * r t ^ 3)) := ⟨_, rfl⟩
  have hHc : ContinuousOn H (Icc (0 : ℝ) 1) := by
    rw [hHdef]
    refine continuousOn_const.mul ((((continuousOn_const.mul hcast).mul hQ'c).div hrc hr0).add
      (hQc.div (continuousOn_const.mul hrc) (fun t ht => mul_ne_zero (mul_ne_zero two_ne_zero hω) (hr0 t ht)))
      |>.sub ((hQc.mul continuousOn_const |>.mul hcast).div
        (continuousOn_const.mul (hrc.pow 3)) (fun t ht =>
          mul_ne_zero two_ne_zero (pow_ne_zero 3 (hr0 t ht)))))
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hHc
  have hint : IntervalIntegrable (fun t : ℝ => H t / (Real.sqrt t : ℂ)) volume 0 1 :=
    G3015Aux.integrable_of_bound H (max C 0) hHc (fun t ht => (hC t ht).trans (le_max_left _ _))
  have hD : (fun t : ℝ => H t / (Real.sqrt t : ℂ)) = fun t : ℝ => dμ * (ω0 * (t : ℂ) *
      deriv Q (a0 + (t : ℂ) * (μ0 - a0)) / r t
        + Q (a0 + (t : ℂ) * (μ0 - a0)) / (2 * ω0 * r t)
        - Q (a0 + (t : ℂ) * (μ0 - a0)) * ω0 * (t : ℂ) / (2 * r t ^ 3)) / (Real.sqrt t : ℂ) := by
    funext t; rw [hHdef, hzdef]
  rw [← hD]
  refine ⟨hint, ?_⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ → ℂ, T = fun t : ℝ =>
      dμ / ω0 * (Q (z t) * (Real.sqrt t : ℂ) / r t) := ⟨_, rfl⟩
  have hTc : ContinuousOn T (Icc (0 : ℝ) 1) := by
    rw [hTdef]
    exact continuousOn_const.mul ((hQc.mul (Complex.continuous_ofReal.comp_continuousOn
      Real.continuous_sqrt.continuousOn)).div hrc hr0)
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt T (H t / (Real.sqrt t : ℂ)) t := by
    intro t ht
    have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hz : HasDerivAt z (μ0 - a0) t := by
      rw [hzdef]
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (μ0 - a0)).const_add a0
    have hQd : DifferentiableAt ℂ Q (z t) := (hQ _ (hzb t htc)).differentiableAt
    have hQz : HasDerivAt (fun u : ℝ => Q (z u)) (deriv Q (z t) * (μ0 - a0)) t :=
      hQd.hasDerivAt.comp t hz
    have hs : HasDerivAt (fun u : ℝ => (Real.sqrt u : ℂ)) ((1 / (2 * Real.sqrt t) : ℝ) : ℂ) t :=
      (Real.hasDerivAt_sqrt ht.1.ne').ofReal_comp
    have hsq : HasDerivAt (fun u : ℝ => r u ^ 2) (μ0 - a0) t := by
      have h1 : HasDerivAt (fun u : ℝ => z u - b0) (μ0 - a0) t := hz.sub_const b0
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [htn] with u hu
      rw [hrsq u hu, hzdef]
    have hrd : HasDerivAt r ((μ0 - a0) / (2 * r t)) t :=
      G3005C6.root_hasDerivAt (hrc.continuousAt htn) (hr0 t htc) hsq
    have hT := ((hQz.mul hs).div hrd (hr0 t htc)).const_mul (dμ / ω0)
    rw [hTdef]
    refine hT.congr_deriv ?_
    have hsne : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
    have hs2 : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt ht.1.le]
    have hrn := hr0 t htc
    rw [hHdef, hzdef]
    simp only [Pi.mul_apply]
    push_cast
    rw [← hωsq]
    generalize (Real.sqrt t : ℂ) = s at hsne hs2 ⊢
    rw [← hs2]
    field_simp
  have hfin := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hTc hder hint
  rw [hfin, hTdef]
  simp only [hzdef, Real.sqrt_zero, Complex.ofReal_zero, mul_zero, zero_div, Real.sqrt_one,
    Complex.ofReal_one, mul_one, sub_zero, zero_mul, one_mul, add_sub_cancel]
  ring_nf

end
end NlsGge.GKDefinitionDesign
