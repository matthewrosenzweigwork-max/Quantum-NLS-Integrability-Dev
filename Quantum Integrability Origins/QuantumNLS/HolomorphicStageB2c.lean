import Mathlib
import QuantumNLS.HolomorphicStageB2b
import QuantumNLS.HolomorphicCauchyC1

/-!
# C2 stage B2c: the key lemma `DifferentiableOn ℂ f U ⇒ DifferentiableOn ℂ (fderiv ℂ f) U`

Local data at each `y0 ∈ U` from stage A (`fderiv_lipschitz_near`, `exists_uniform_fderiv_bound`), then the local
derivative from stage B2b (`hasFDerivAt_fderiv_local`). Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set

namespace QuantumNLS.HolomorphicStageB2c

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem differentiableOn_fderiv {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun p => fderiv ℂ f p) U := by
  intro y0 hy0
  obtain ⟨δ, hδ, hball, K, hK0, hK⟩ := QuantumNLS.HolomorphicCauchyC1.exists_uniform_fderiv_bound hU hf hy0
  obtain ⟨D, hD, L, hL0, hLip⟩ := QuantumNLS.HolomorphicCauchyC1.fderiv_lipschitz_near hU hf hy0
  set ρ : ℝ := min δ (D / 4) with hρdef
  have hρ : 0 < ρ := lt_min hδ (by linarith)
  have hballU : ball y0 ρ ⊆ U := (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  have hballL : ∀ p ∈ ball y0 ρ, ∀ q ∈ ball y0 ρ, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ L * ‖p - q‖ := by
    intro p hp q hq
    have hp' : p ∈ ball y0 (D / 4) := Metric.ball_subset_ball (min_le_right _ _) hp
    have hq' : q ∈ ball y0 (D / 4) := Metric.ball_subset_ball (min_le_right _ _) hq
    exact hLip p hp' q hq'
  have hballK : ∀ p ∈ ball y0 ρ, ∀ w : E, ‖fderiv ℂ f p w‖ ≤ K * ‖w‖ := by
    intro p hp w
    exact hK p (Metric.ball_subset_ball (min_le_left _ _) hp) w
  obtain ⟨Lcl, hL⟩ := QuantumNLS.HolomorphicStageB2b.hasFDerivAt_fderiv_local hU hf hρ hballU hL0 hballL hK0 hballK
  exact (hL.differentiableAt).differentiableWithinAt

end QuantumNLS.HolomorphicStageB2c

#print axioms QuantumNLS.HolomorphicStageB2c.differentiableOn_fderiv
