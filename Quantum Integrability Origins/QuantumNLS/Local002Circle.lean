import Mathlib

/-! LOCAL-002 stage E (helper): generic circle-integral facts used for the idempotence of Riesz projections:
bounded operators commute with circle integrals, and Fubini for two circle integrals. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ComplexConjugate
namespace QuantumNLS.Local002Circle

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

lemma clm_circleIntegral [CompleteSpace E] [CompleteSpace F] (Λ : E →L[ℂ] F) {c : ℂ} {r : ℝ} {f : ℂ → E} (hf : CircleIntegrable f c r) :
    Λ (∮ z in C(c, r), f z) = ∮ z in C(c, r), Λ (f z) := by
  unfold circleIntegral
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm Λ hf.out]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp

lemma continuous_dcircle (c : ℂ) (r : ℝ) :
    Continuous fun θ : ℝ => deriv (circleMap c r) θ := by
  have : (fun θ : ℝ => deriv (circleMap c r) θ) = fun θ => circleMap 0 r θ * Complex.I := by
    funext θ; exact deriv_circleMap c r θ
  rw [this]
  exact (continuous_circleMap 0 r).mul continuous_const

/-- Fubini for two circle integrals of a function continuous on the product of the circles. -/
lemma circle_swap [CompleteSpace E] {c : ℂ} {r1 r2 : ℝ} (h1 : 0 ≤ r1) (h2 : 0 ≤ r2)
    (G : ℂ → ℂ → E)
    (hG : ContinuousOn (fun p : ℂ × ℂ => G p.1 p.2) (sphere c r2 ×ˢ sphere c r1)) :
    (∮ w in C(c, r1), ∮ z in C(c, r2), G z w) = ∮ z in C(c, r2), ∮ w in C(c, r1), G z w := by
  have hGc : Continuous fun p : ℝ × ℝ => G (circleMap c r2 p.1) (circleMap c r1 p.2) := by
    have hmap : Continuous fun p : ℝ × ℝ => (circleMap c r2 p.1, circleMap c r1 p.2) := by
      fun_prop
    exact hG.comp_continuous hmap (fun p => ⟨circleMap_mem_sphere c h2 _, circleMap_mem_sphere c h1 _⟩)
  have hK : Continuous fun p : ℝ × ℝ => deriv (circleMap c r1) p.2 •
      (deriv (circleMap c r2) p.1 • G (circleMap c r2 p.1) (circleMap c r1 p.2)) :=
    ((continuous_dcircle c r1).comp continuous_snd).smul
      (((continuous_dcircle c r2).comp continuous_fst).smul hGc)
  unfold circleIntegral
  have e1 : ∀ β : ℝ, deriv (circleMap c r1) β • ∫ α in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap c r2) α • G (circleMap c r2 α) (circleMap c r1 β) =
      ∫ α in (0 : ℝ)..2 * Real.pi, deriv (circleMap c r1) β •
        (deriv (circleMap c r2) α • G (circleMap c r2 α) (circleMap c r1 β)) := fun β => by
    rw [intervalIntegral.integral_smul]
  have e2 : ∀ α : ℝ, deriv (circleMap c r2) α • ∫ β in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap c r1) β • G (circleMap c r2 α) (circleMap c r1 β) =
      ∫ β in (0 : ℝ)..2 * Real.pi, deriv (circleMap c r1) β •
        (deriv (circleMap c r2) α • G (circleMap c r2 α) (circleMap c r1 β)) := fun α => by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr (fun β _ => ?_)
    simp only [smul_comm (deriv (circleMap c r2) α) (deriv (circleMap c r1) β)]
  simp_rw [e1, e2]
  refine MeasureTheory.intervalIntegral_intervalIntegral_swap (F := fun β α =>
    deriv (circleMap c r1) β • (deriv (circleMap c r2) α • G (circleMap c r2 α) (circleMap c r1 β))) ?_
  have hc : Continuous (Function.uncurry fun β α : ℝ =>
      deriv (circleMap c r1) β • (deriv (circleMap c r2) α • G (circleMap c r2 α) (circleMap c r1 β))) :=
    hK.comp continuous_swap
  exact (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

end QuantumNLS.Local002Circle
#print axioms QuantumNLS.Local002Circle.circle_swap
#print axioms QuantumNLS.Local002Circle.clm_circleIntegral
