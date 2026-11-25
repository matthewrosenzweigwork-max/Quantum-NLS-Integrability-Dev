import Mathlib
import NlsGge.Atomic.G1.S4LibCauchy
import NlsGge.Atomic.G1.S4LibUniform

/- S4Lib kit (b'), proof development, AUTHOR; not reviewed. Target NlsGge/Atomic/G1/S4LibOpen.lean.
   Uniform limits of analytic maps on an arbitrary open set (no a priori common bound) are
   analytic; and the exact product-space form UniformLimitAnalyticProp consumed by S4Picard. -/
set_option autoImplicit false
open Metric Set Filter Topology

namespace NlsGge.S4Lib

section
variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem analyticOnNhd_of_tendstoUniformlyOn_isOpen {f : ℕ → X → F} {g : X → F} {U : Set X}
    (hU : IsOpen U) (hf : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hlim : TendstoUniformlyOn f g atTop U) : AnalyticOnNhd ℂ g U := by
  have hgc : ContinuousOn g U :=
    hlim.continuousOn (Eventually.of_forall fun n => (hf n).continuousOn).frequently
  intro x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  have hca : ContinuousAt g x := hgc.continuousAt (hU.mem_nhds hx)
  obtain ⟨r', hr', hr'g⟩ := Metric.eventually_nhds_iff_ball.1
    (hca.eventually (Metric.ball_mem_nhds (g x) one_pos))
  set s := min r r' with hs
  have hspos : 0 < s := lt_min hr hr'
  have hsU : ball x s ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hrU
  have hsg : ∀ z ∈ ball x s, ‖g z‖ ≤ ‖g x‖ + 1 := by
    intro z hz
    have h1 : g z ∈ ball (g x) 1 := hr'g z (ball_subset_ball (min_le_right _ _) hz)
    rw [mem_ball, dist_eq_norm] at h1
    calc ‖g z‖ = ‖(g z - g x) + g x‖ := by congr 1; abel
      _ ≤ ‖g z - g x‖ + ‖g x‖ := norm_add_le _ _
      _ ≤ ‖g x‖ + 1 := by linarith
  have hlim' := Metric.tendstoUniformlyOn_iff.1 hlim 1 one_pos
  obtain ⟨N, hN⟩ := eventually_atTop.1 hlim'
  have hshift : TendstoUniformlyOn (fun k => f (k + N)) g atTop (ball x s) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_add_atTop_nat N).eventually
      (((Metric.tendstoUniformlyOn_iff.1 (hlim.mono hsU)) ε hε))] with k hk using hk
  have hbd : ∀ k, ∀ z ∈ ball x s, ‖f (k + N) z‖ ≤ ‖g x‖ + 2 := by
    intro k z hz
    have h1 := hN (k + N) (by omega) z (hsU hz)
    rw [dist_eq_norm] at h1
    have h2 := hsg z hz
    calc ‖f (k + N) z‖ = ‖g z - (g z - f (k + N) z)‖ := by congr 1; abel
      _ ≤ ‖g z‖ + ‖g z - f (k + N) z‖ := norm_sub_le _ _
      _ ≤ ‖g x‖ + 2 := by linarith
  have hana := analyticOnNhd_of_tendstoUniformlyOn_ball hspos
    (fun k => (hf (k + N)).mono hsU) hbd hshift
  exact hana x (mem_ball_self hspos)

end

/-- The product-space form `UniformLimitAnalyticProp E` of S4Picard, for every complex Banach
space `E`: uniform limits of analytic maps on an open subset of `ℂ × E` are analytic. -/
theorem uniformLimitAnalytic_prod (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] :
    ∀ {U : Set (ℂ × E)} {f : ℕ → ℂ × E → E} {g : ℂ × E → E}, IsOpen U →
      (∀ n, AnalyticOnNhd ℂ (f n) U) → TendstoUniformlyOn f g atTop U →
        AnalyticOnNhd ℂ g U :=
  fun hU hf hlim => analyticOnNhd_of_tendstoUniformlyOn_isOpen hU hf hlim

end NlsGge.S4Lib
