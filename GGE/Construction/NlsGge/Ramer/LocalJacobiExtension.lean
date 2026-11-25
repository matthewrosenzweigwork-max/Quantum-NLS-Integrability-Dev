import Mathlib
import NlsGge.Ramer.RamerStep1Locality

/-!
# LOC-EXT: extending the local Jacobi identity from uniformly continuous to measurable test functions

Generic setting: `X` metric, second countable, Borel; `μ` finite; `T : X ≃ₜ X`; `J` measurable;
`V` open.  If `(*)` holds for all bounded uniformly continuous `F ≥ 0` with
`tsupport F ⊆ T '' V` (exactly the shape consumed by `map_symm_eq_withDensity_of_local`), then
`∫⁻ y in T '' V, G y ∂μ = ∫⁻ x in V, G (T x) * J x ∂μ` for every measurable `G : X → ℝ≥0∞`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Ramer

open MeasureTheory Set Metric
open scoped ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- The local hypothesis in the shape of `map_symm_eq_withDensity_of_local`. -/
def LocalJacobiUC (μ : Measure X) (T : X ≃ₜ X) (J : X → ℝ≥0∞) (V : Set X) : Prop :=
  ∀ F : X → ℝ, UniformContinuous F → (∃ C, ∀ y, |F y| ≤ C) → (∀ y, 0 ≤ F y) →
    tsupport F ⊆ T '' V →
    ∫⁻ y in T '' V, ENNReal.ofReal (F y) ∂μ =
      ∫⁻ x in V, ENNReal.ofReal (F (T x)) * J x ∂μ

/-- Equality of the two measures on `X` (before integrating). -/
theorem restrict_image_eq_map_withDensity (μ : Measure X) [IsFiniteMeasure μ] (T : X ≃ₜ X)
    (J : X → ℝ≥0∞) (hJ : Measurable J) (V : Set X) (hV : IsOpen V)
    (hloc : LocalJacobiUC μ T J V) :
    μ.restrict (T '' V) = Measure.map T ((μ.restrict V).withDensity J) := by
  set W : Set X := T '' V with hWdef
  have hW : IsOpen W := T.isOpenMap V hV
  set ν : Measure X := Measure.map T ((μ.restrict V).withDensity J) with hν
  have hTm : Measurable T := T.continuous.measurable
  have hνapp : ∀ A : Set X, MeasurableSet A → ν A = ∫⁻ x in T ⁻¹' A ∩ V, J x ∂μ := by
    intro A hA
    rw [hν, Measure.map_apply hTm hA, withDensity_apply _ (hTm hA), Measure.restrict_restrict (hTm hA)]
  -- good open sets
  have hgood : ∀ U : Set X, IsOpen U → closure U ⊆ W → μ.restrict W U = ν U := by
    intro U hU hcl
    have hUW : U ⊆ W := subset_closure.trans hcl
    set O : Set X := T ⁻¹' U with hO
    have hOo : IsOpen O := hU.preimage T.continuous
    have hclO : closure O ⊆ V := by
      have : closure O = T ⁻¹' closure U := by
        rw [hO, ← T.preimage_closure]
      rw [this]
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hcl hx
      rwa [← T.injective hyx]
    have hOV : O ⊆ V := subset_closure.trans hclO
    have himg : T '' O = U := by
      rw [hO]; exact T.image_preimage U ▸ (by simp [Set.image_preimage_eq _ T.surjective])
    have := measure_image_eq_of_local μ T J hJ V O hOo hclO hloc
    rw [himg] at this
    rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.2 hUW, this,
      hνapp U hU.measurableSet, inter_eq_left.2 hOV]
  -- local equality on good sets
  have hlocal : ∀ O : Set X, IsOpen O → closure O ⊆ W →
      (μ.restrict W).restrict O = ν.restrict O := by
    intro O hO hclO
    have : IsFiniteMeasure ((μ.restrict W).restrict O) := inferInstance
    refine ext_of_generate_finite {s : Set X | IsOpen s} ?_ isPiSystem_isOpen ?_ ?_
    · exact (BorelSpace.measurable_eq (α := X))
    · intro U hU
      rw [Measure.restrict_apply hU.measurableSet, Measure.restrict_apply hU.measurableSet]
      have h := hgood (U ∩ O) (hU.inter hO)
        ((closure_inter_subset_inter_closure _ _).trans (inter_subset_right.trans hclO))
      exact h
    · have h := hgood O hO hclO
      simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter]
      exact h
  -- countable cover of W by good open sets
  let S0 : Set (Set X) := {U | IsOpen U ∧ closure U ⊆ W}
  obtain ⟨S, hSc, hSS, hSU⟩ := TopologicalSpace.isOpen_sUnion_countable S0 (fun U hU => hU.1)
  have hcover : ⋃₀ S = W := by
    rw [hSU]
    refine subset_antisymm (sUnion_subset fun U hU => subset_closure.trans hU.2) fun x hx => ?_
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hW x hx
    refine ⟨Metric.ball x (r / 2), ⟨Metric.isOpen_ball, ?_⟩, Metric.mem_ball_self (half_pos hr)⟩
    refine (closure_ball_subset_closedBall).trans fun y hy => hball ?_
    exact Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (half_lt_self hr))
  have hSW : (μ.restrict W).restrict (⋃₀ S) = ν.restrict (⋃₀ S) := by
    rw [Measure.restrict_sUnion_congr hSc]
    intro U hU
    exact hlocal U (hSS hU).1 (hSS hU).2
  rw [hcover] at hSW
  have hν0 : ν Wᶜ = 0 := by
    rw [hνapp _ hW.measurableSet.compl]
    have : T ⁻¹' Wᶜ ∩ V = ∅ := by
      ext x; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, hWdef, mem_empty_iff_false,
        iff_false, not_and]
      intro h hx; exact h (mem_image_of_mem T hx)
    rw [this]; simp
  have hae : ∀ᵐ x ∂ν, x ∈ W := by
    rw [ae_iff]; exact hν0
  have hae1 : ∀ᵐ x ∂(μ.restrict W), x ∈ W := ae_restrict_mem hW.measurableSet
  rw [← Measure.restrict_eq_self_of_ae_mem hae1, ← Measure.restrict_eq_self_of_ae_mem hae, hSW]

/-- **LOC-EXT**: the local Jacobi identity for every measurable extended-real `G`. -/
theorem lintegral_image_eq_of_local_ext (μ : Measure X) [IsFiniteMeasure μ] (T : X ≃ₜ X)
    (J : X → ℝ≥0∞) (hJ : Measurable J) (V : Set X) (hV : IsOpen V)
    (hloc : LocalJacobiUC μ T J V) (G : X → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y in T '' V, G y ∂μ = ∫⁻ x in V, G (T x) * J x ∂μ := by
  have hTm : Measurable T := T.continuous.measurable
  rw [restrict_image_eq_map_withDensity μ T J hJ V hV hloc,
    lintegral_map hG hTm]
  refine (lintegral_withDensity_eq_lintegral_mul₀ (f := J) (g := G ∘ T) hJ.aemeasurable
      (hG.comp hTm).aemeasurable).trans ?_
  refine lintegral_congr fun x => ?_
  simp [mul_comm]

/-- Real-valued form: measurable `F ≥ 0` (no boundedness or continuity). -/
theorem lintegral_ofReal_image_eq_of_local_ext (μ : Measure X) [IsFiniteMeasure μ] (T : X ≃ₜ X)
    (J : X → ℝ≥0∞) (hJ : Measurable J) (V : Set X) (hV : IsOpen V)
    (hloc : LocalJacobiUC μ T J V) (F : X → ℝ) (hF : Measurable F) :
    ∫⁻ y in T '' V, ENNReal.ofReal (F y) ∂μ =
      ∫⁻ x in V, ENNReal.ofReal (F (T x)) * J x ∂μ :=
  lintegral_image_eq_of_local_ext μ T J hJ V hV hloc _ (ENNReal.measurable_ofReal.comp hF)

/-- Version for `F` vanishing off `T '' V`: no restriction on the left. -/
theorem lintegral_eq_of_local_ext_of_zero_off (μ : Measure X) [IsFiniteMeasure μ] (T : X ≃ₜ X)
    (J : X → ℝ≥0∞) (hJ : Measurable J) (V : Set X) (hV : IsOpen V)
    (hloc : LocalJacobiUC μ T J V) (G : X → ℝ≥0∞) (hG : Measurable G)
    (hz : ∀ y, y ∉ T '' V → G y = 0) :
    ∫⁻ y, G y ∂μ = ∫⁻ x in V, G (T x) * J x ∂μ := by
  rw [← lintegral_image_eq_of_local_ext μ T J hJ V hV hloc G hG]
  refine (setLIntegral_eq_of_support_subset ?_).symm
  intro y hy
  by_contra h
  exact hy (hz y h)

/-- Borel sets: `μ (T '' A) = ∫⁻_A J` for `A ⊆ V` measurable. -/
theorem measure_image_eq_of_local_ext (μ : Measure X) [IsFiniteMeasure μ] (T : X ≃ₜ X)
    (J : X → ℝ≥0∞) (hJ : Measurable J) (V : Set X) (hV : IsOpen V)
    (hloc : LocalJacobiUC μ T J V) (A : Set X) (hA : MeasurableSet A) (hAV : A ⊆ V) :
    μ (T '' A) = ∫⁻ x in A, J x ∂μ := by
  have hTA : MeasurableSet (T '' A) := (T.toMeasurableEquiv.measurableSet_image).2 hA
  have h := lintegral_image_eq_of_local_ext μ T J hJ V hV hloc ((T '' A).indicator 1)
    (measurable_one.indicator hTA)
  have hsub : T '' A ⊆ T '' V := image_mono hAV
  rw [lintegral_indicator_one hTA, Measure.restrict_apply hTA, inter_eq_left.2 hsub] at h
  rw [h]
  have : ∀ x, (T '' A).indicator (1 : X → ℝ≥0∞) (T x) * J x = A.indicator J x := by
    intro x
    by_cases hx : x ∈ A
    · simp [indicator_of_mem hx, indicator_of_mem (mem_image_of_mem T hx)]
    · have : T x ∉ T '' A := fun h => hx (T.injective.mem_set_image.1 h)
      simp [indicator_of_notMem hx, indicator_of_notMem this]
  simp_rw [this]
  rw [lintegral_indicator hA, Measure.restrict_restrict hA, inter_eq_left.2 hAV]

end NlsGge.Ramer
