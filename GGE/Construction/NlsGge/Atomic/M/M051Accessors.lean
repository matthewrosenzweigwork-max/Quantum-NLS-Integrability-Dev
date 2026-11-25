import Mathlib
import NlsGge.Atomic.M.M051Host

                                                                                                
                                                                                                                          
                                                                                                         
                                                                            
                                                                                                                                   
                                                                                                                                
                                                                                              
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section
attribute [local instance] Classical.propDecidable

theorem infinityFilter_neBot : (infinityFilter).NeBot := by
  unfold infinityFilter
  refine Filter.comap_neBot (fun t ht => ?_)
  obtain ⟨z, hz⟩ := (Filter.NeBot.nonempty_of_mem (inferInstance : (𝓝[≠] (0 : ℂ)).NeBot) ht)
  exact ⟨z⁻¹, by simpa using hz⟩

theorem value_at_infinity_unique
    (f : ℂ → ℂ) (a b : ℂ)
    (ha : HasValueAtInfinity f a) (hb : HasValueAtInfinity f b) :
  a = b := by
  have := infinityFilter_neBot
  exact tendsto_nhds_unique ha hb

theorem exterior_circleIntegrable
    (f : ℂ → ℂ) {R0 : ℝ} (hR0 : 0 < R0) (hf : AnalyticOnNhd ℂ f {z : ℂ | R0 < ‖z‖})
    (k : ℤ) {R : ℝ} (hR : R0 < R) :
    CircleIntegrable (fun z : ℂ => f z * z ^ (-k - 1)) 0 R := by
  apply ContinuousOn.circleIntegrable (hR0.trans hR).le
  intro z hz
  have hzn : ‖z‖ = R := by simpa using hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn; linarith [hR0.trans hR]
  have hzm : z ∈ {z : ℂ | R0 < ‖z‖} := by
    show R0 < ‖z‖
    rw [hzn]; exact hR
  exact ((hf z hzm).continuousAt.mul
    ((continuousAt_id.zpow₀ _ (Or.inl hz0)))).continuousWithinAt

theorem exterior_coeff_const
    (f : ℂ → ℂ) {R0 : ℝ} (hR0 : 0 < R0) (hf : AnalyticOnNhd ℂ f {z : ℂ | R0 < ‖z‖})
    (k : ℤ) {R1 R2 : ℝ} (h1 : R0 < R1) (h12 : R1 ≤ R2) :
    circleIntegral (fun z : ℂ => f z * z ^ (-k - 1)) 0 R2 =
      circleIntegral (fun z : ℂ => f z * z ^ (-k - 1)) 0 R1 := by
  have hR1 : 0 < R1 := hR0.trans h1
  have hda : ∀ z : ℂ, R1 ≤ ‖z‖ →
      DifferentiableAt ℂ (fun z : ℂ => f z * z ^ (-k - 1)) z := by
    intro z hz1'
    have hzm : z ∈ {z : ℂ | R0 < ‖z‖} := lt_of_lt_of_le h1 hz1'
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz1'; linarith
    exact (hf z hzm).differentiableAt.mul ((differentiableAt_id.zpow (Or.inl hz0)))
  have hcont : ContinuousOn (fun z : ℂ => f z * z ^ (-k - 1))
      (Metric.closedBall (0 : ℂ) R2 \ Metric.ball (0 : ℂ) R1) := fun z hz =>
    (hda z (by simpa using hz.2)).continuousAt.continuousWithinAt
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hR1 h12
    Set.countable_empty hcont (fun z hz => hda z (by
      have := hz.1.2
      exact (by simpa using this : R1 < ‖z‖).le))

theorem exterior_laurent_coefficient_exists_unique
    (f : ℂ → ℂ) (hf : ExteriorHolomorphic f) (k : ℤ) :
  ∃! a : ℂ, HasLaurentCoefficient f k a := by
  obtain ⟨R0, hR0, hfa⟩ := hf
  have hint : ∃ R0' : ℝ, 0 < R0' ∧ ∀ R : ℝ, R0' < R →
      CircleIntegrable (fun z : ℂ => f z * z ^ (-k - 1)) 0 R :=
    ⟨R0, hR0, fun R hR => exterior_circleIntegrable f hR0 hfa k hR⟩
  set a : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun z : ℂ => f z * z ^ (-k - 1)) 0 (R0 + 1) with ha
  have hlim : Tendsto
      (fun R : ℝ => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun z : ℂ => f z * z ^ (-k - 1)) 0 R) atTop (𝓝 a) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (R0 + 1)] with R hR
    rw [ha, exterior_coeff_const f hR0 hfa k (by linarith) hR]
  refine ⟨a, ⟨hint, hlim⟩, ?_⟩
  rintro b ⟨-, hb⟩
  exact tendsto_nhds_unique hb hlim

def laurentCoefficient (f : ℂ → ℂ) (hf : ExteriorHolomorphic f)
    (k : ℤ) : ℂ :=
  Classical.choose (exterior_laurent_coefficient_exists_unique f hf k).exists

def valueAtInfinity (f : ℂ → ℂ)
    (hf : ∃! a : ℂ, HasValueAtInfinity f a) : ℂ :=
  Classical.choose hf.exists

theorem laurent_coefficient_characterization
    (f : ℂ → ℂ) (hf : ExteriorHolomorphic f) (k : ℤ) :
  HasLaurentCoefficient f k (laurentCoefficient f hf k) ∧
  ∀ a : ℂ, HasLaurentCoefficient f k a →
    a = laurentCoefficient f hf k := by
  have h := exterior_laurent_coefficient_exists_unique f hf k
  refine ⟨Classical.choose_spec h.exists, fun a ha => ?_⟩
  exact h.unique ha (Classical.choose_spec h.exists)

theorem value_at_infinity_characterization
    (f : ℂ → ℂ) (hf : ∃! a : ℂ, HasValueAtInfinity f a) :
  HasValueAtInfinity f (valueAtInfinity f hf) ∧
  ∀ a : ℂ, HasValueAtInfinity f a → a = valueAtInfinity f hf := by
  refine ⟨Classical.choose_spec hf.exists, fun a ha => ?_⟩
  exact hf.unique ha (Classical.choose_spec hf.exists)

end
end NlsGge.ThirdConsultation.MPrimitive

namespace NlsGge.ThirdConsultation.M

noncomputable def LaurentCoefficient (f : ℂ → ℂ)
    (hf : MPrimitive.ExteriorHolomorphic f) (k : ℤ) : ℂ :=
  MPrimitive.laurentCoefficient f hf k

noncomputable def valueAtInfinity (f : ℂ → ℂ)
    (hf : ∃! a : ℂ, MPrimitive.HasValueAtInfinity f a) : ℂ :=
  MPrimitive.valueAtInfinity f hf

end NlsGge.ThirdConsultation.M
