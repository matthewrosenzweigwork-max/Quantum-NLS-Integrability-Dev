import Mathlib
import NlsGge.Atomic.Support.ContourChain
import NlsGge.Atomic.Support.ContourCycleIndex
import NlsGge.Atomic.Support.ContourCycleCauchy
import NlsGge.Atomic.G1.G1103Circ

/- G2-045 SUPPORT A1 (proof development, AUTHOR; not reviewed; semantic fidelity gate open).
   Abstract multi-hole deformation: for a closed set `K` inside `ball 0 R` and a finite family of circles whose
   open discs each contain exactly one "part" of `K` (every point of `K` lies strictly inside exactly one circle of
   the family and strictly outside all the others), and `f` holomorphic on `Kᶜ`, the large-circle integral equals
   the sum of the small-circle integrals.  Route: Dixon cycle Cauchy theorem (landed ContourCycleCauchy) for the cycle
   `circle 0 R - sum circle (c n) (r n)`, exactly as in landed M009Support4.closedChain_omega_zero.
   No NLS input; no added hypothesis beyond the displayed geometry. -/
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators unitInterval
open NlsGge.GK38.Lib.SlitContours
open NlsGge.Atomic.ContourChain
open NlsGge.Atomic.G1103Circ

namespace NlsGge.G2045SupA1
noncomputable section

theorem circleCycle_integral_eq (f : ℂ → ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (sphere c r)) :
    (circleCycle c r).integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) =
      circleIntegral f c r := by
  have hfun : (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = complexForm f := by
    funext w; exact toSpanSingleton_eq_complexForm f w
  rw [circleCycle_integral, hfun]
  exact curveIntegral_circleLoop f c r hr hf

theorem circle_eq_sum_circles (K : Set ℂ) (hK : IsClosed K) (R : ℝ) (hR : 0 < R)
    (hKR : K ⊆ ball (0 : ℂ) R) (S : Finset ℤ) (c : ℤ → ℂ) (r : ℤ → ℝ)
    (hr : ∀ n ∈ S, 0 < r n) (hsph : ∀ n ∈ S, sphere (c n) (r n) ⊆ Kᶜ)
    (hidx : ∀ w ∈ K, ∃ n ∈ S, ‖w - c n‖ < r n ∧ ∀ m ∈ S, m ≠ n → r m < ‖w - c m‖)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f Kᶜ) :
    circleIntegral f 0 R = ∑ n ∈ S, circleIntegral f (c n) (r n) := by
  classical
  have hUo : IsOpen Kᶜ := hK.isOpen_compl
  have hbig : sphere (0 : ℂ) R ⊆ Kᶜ := by
    intro z hz hzK
    have := hKR hzK
    rw [mem_ball, dist_eq_norm, sub_zero] at this
    rw [mem_sphere_iff_norm, sub_zero] at hz
    linarith
  have hcirc : ∀ j ∈ S, (circleCycle (c j) (r j)).range ⊆ Kᶜ := fun j hj =>
    (circleCycle_range_subset (c j) (hr j hj).le).trans (hsph j hj)
  obtain ⟨Θ, hΘr, hΘi, hΘint⟩ := exists_weighted_cycle (F := ℂ) S
    (fun j => circleCycle (c j) (r j)) (fun _ => 1)
  have hΘU : Θ.range ⊆ Kᶜ := by
    intro z hz
    obtain ⟨j, hj, hzj⟩ := hΘr z hz
    exact hcirc j hj hzj
  have hfcont : ContinuousOn f Kᶜ := hf.continuousOn
  have hcI : ∀ j ∈ S, (circleCycle (c j) (r j)).Integrable
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) := fun j hj =>
    Cycle.integrable_of_continuousOn
      ((ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp_continuousOn hfcont)
      (hcirc j hj)
  obtain ⟨hΘI, hΘI2⟩ := hΘint (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) hcI
  have hΓ0 : (circleCycle (0 : ℂ) R).Integrable
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) :=
    Cycle.integrable_of_continuousOn
      ((ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp_continuousOn hfcont)
      ((circleCycle_range_subset 0 hR.le).trans hbig)
  have hΓ'U : ((circleCycle (0 : ℂ) R).append Θ.reverse).range ⊆ Kᶜ := by
    rw [Cycle.range_append, Cycle.range_reverse]
    exact union_subset ((circleCycle_range_subset 0 hR.le).trans hbig) hΘU
  have hind : ∀ w : ℂ, w ∉ Kᶜ → ((circleCycle (0 : ℂ) R).append Θ.reverse).index w = 0 := by
    intro w hw
    have hwK : w ∈ K := not_not.1 hw
    have hwΘ : w ∉ Θ.range := fun h => hw (hΘU h)
    obtain ⟨n, hn, hin, hout⟩ := hidx w hwK
    rw [Cycle.index_append, Cycle.index_reverse Θ hwΘ,
      hΘi w (fun j hj hwj => hw (hcirc j hj hwj))]
    have h1 : (circleCycle (0 : ℂ) R).index w = 1 := by
      apply circleCycle_index_inside 0 hR
      have := hKR hwK
      rw [mem_ball, dist_eq_norm, sub_zero] at this
      simpa using this
    have h2 : ∑ j ∈ S, ((fun _ : ℤ => (1 : ℤ)) j : ℂ) * (circleCycle (c j) (r j)).index w = 1 := by
      have : ∀ j ∈ S, ((fun _ : ℤ => (1 : ℤ)) j : ℂ) * (circleCycle (c j) (r j)).index w =
          if j = n then 1 else 0 := by
        intro j hj
        by_cases hjn : j = n
        · subst hjn
          rw [if_pos rfl, circleCycle_index_inside (c j) (hr j hj) hin]; simp
        · rw [if_neg hjn, circleCycle_index_outside (c j) (hr j hj) (hout j hj hjn)]; simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' S n (fun _ => (1 : ℂ)), if_pos hn]
    rw [h1, h2]; ring
  have h0 := Cycle.integral_eq_zero ((circleCycle (0 : ℂ) R).append Θ.reverse) hUo hΓ'U hind hf
  rw [Cycle.integral_append, Cycle.integral_reverse hΘI, hΘI2] at h0
  have e1 := circleCycle_integral_eq f 0 hR (hfcont.mono hbig)
  have e2 : ∀ j ∈ S, (1 : ℤ) • (circleCycle (c j) (r j)).integral
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = circleIntegral f (c j) (r j) := by
    intro j hj
    rw [circleCycle_integral_eq f (c j) (hr j hj) (hfcont.mono (hsph j hj))]; simp
  rw [e1] at h0
  have h3 : ∑ j ∈ S, ((fun _ : ℤ => (1 : ℤ)) j : ℂ) • (circleCycle (c j) (r j)).integral
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) =
      ∑ j ∈ S, circleIntegral f (c j) (r j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← e2 j hj]; simp
  rw [h3] at h0
  linear_combination h0

end
end NlsGge.G2045SupA1
