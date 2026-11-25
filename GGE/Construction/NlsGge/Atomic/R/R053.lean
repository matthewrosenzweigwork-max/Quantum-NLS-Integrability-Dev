import Mathlib
import NlsGge.Ramer.RamerStep10
import NlsGge.Ramer.LocalJacobiExtension

                                                                                                                                        
                                                                                                                   
                                                                                                                                              
                                                                                                                           
                                                                                                                                               
                                                                                                                                               
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section

def RamerLocalLowerBound
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : Measure X) (T : X ≃ₜ X) (U : Set X)
    (J : X → ℝ≥0∞) : Prop :=
  ∀ B : Set X, B ⊆ T '' U →
    (∫⁻ x in T ⁻¹' B, J x ∂γ) ≤ γ B

def LocalJacobiUC
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : Measure X) (T : X ≃ₜ X)
    (J : X → ℝ≥0∞) (U : Set X) : Prop :=
  ∀ F : X → ℝ,
    UniformContinuous F →
    (∃ C : ℝ, ∀ y : X, |F y| ≤ C) →
    (∀ y : X, 0 ≤ F y) →
    tsupport F ⊆ T '' U →
    (∫⁻ y in T '' U, ENNReal.ofReal (F y) ∂γ) =
      ∫⁻ x in U, ENNReal.ofReal (F (T x)) * J x ∂γ


theorem twoSided_inverse_bound
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : Measure X) (T : X ≃ₜ X) (U : Set X) (J2 : X → ℝ≥0∞)
    (h2 : RamerLocalLowerBound γ T.symm (T '' U) J2) :
    ∀ A : Set X, A ⊆ U → ∫⁻ y in T '' A, J2 y ∂γ ≤ γ A := by
  intro A hA
  have h := h2 A (by
    intro x hx
    exact ⟨T x, ⟨x, hA hx, rfl⟩, T.symm_apply_apply x⟩)
  rw [Homeomorph.preimage_symm] at h
  exact h

theorem localJacobiUC_of_two_sided
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : Measure X) (T : X ≃ₜ X) (U : Set X) (hU : IsOpen U)
    (J1 J2 : X → ℝ≥0∞)
    (hJ1 : Measurable J1) (hJ2 : Measurable J2)
    (h1 : RamerLocalLowerBound γ T U J1)
    (h2 : RamerLocalLowerBound γ T.symm (T '' U) J2)
    (hp : ∀ᵐ y ∂γ,
      y ∈ T '' U → J1 (T.symm y) * J2 y = 1) :
    LocalJacobiUC γ T J1 U :=
  NlsGge.Ramer.localJacobiUC_of_two_sided γ T U hU J1 J2 hJ1 hJ2 h1
    (twoSided_inverse_bound γ T U J2 h2) hp

theorem restrict_image_eq_map_withDensity_of_two_sided
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (γ : Measure X) (T : X ≃ₜ X) (U : Set X) (hU : IsOpen U)
    (J1 J2 : X → ℝ≥0∞)
    (hJ1 : Measurable J1) (hJ2 : Measurable J2)
    (h1 : RamerLocalLowerBound γ T U J1)
    (h2 : RamerLocalLowerBound γ T.symm (T '' U) J2)
    (hp : ∀ᵐ y ∂γ,
      y ∈ T '' U → J1 (T.symm y) * J2 y = 1) :
    γ.restrict (T '' U) =
      Measure.map T ((γ.restrict U).withDensity J1) := by
  have h2' := twoSided_inverse_bound γ T U J2 h2
  have hSV : MeasurableSet (T '' U) := (T.isOpenMap U hU).measurableSet
  have hSinj : Function.Injective T := T.injective
  have hTm : Measurable T := T.continuous.measurable
  have hTsm : Measurable T.symm := T.symm.continuous.measurable
  have himg : ∀ B : Set X, T.symm ⁻¹' B = T '' B := by
    intro B; ext x; constructor
    · intro h; exact ⟨T.symm x, h, T.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  set ρ1 : Measure X := (γ.restrict (T '' U)).withDensity J2 with hρ1
  have hle : Measure.map T.symm ρ1 ≤ γ.restrict U := by
    rw [Measure.le_iff]
    intro A' hA'
    have hpre : MeasurableSet (T.symm ⁻¹' A') := hTsm hA'
    rw [Measure.map_apply hTsm hA', hρ1, withDensity_apply _ hpre,
      Measure.restrict_restrict hpre, Measure.restrict_apply hA', himg, ← image_inter hSinj]
    exact h2' (A' ∩ U) inter_subset_right
  have h4 : ∀ B : Set X, MeasurableSet B → B ⊆ T '' U →
      γ B ≤ ∫⁻ x in T ⁻¹' B, J1 x ∂γ := by
    intro B hB hBV
    have hC : MeasurableSet (T ⁻¹' B) := hTm hB
    have hCV : T ⁻¹' B ⊆ U := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hBV hx
      rwa [← hSinj hyx]
    have hmeasg : Measurable fun y => (T ⁻¹' B).indicator J1 (T.symm y) :=
      (hJ1.indicator hC).comp hTsm
    calc γ B = ∫⁻ y in T '' U, B.indicator (fun _ => (1 : ℝ≥0∞)) y ∂γ := by
          rw [lintegral_indicator hB, setLIntegral_const, one_mul, Measure.restrict_apply hB,
            inter_eq_left.2 hBV]
      _ = ∫⁻ y in T '' U, (T ⁻¹' B).indicator J1 (T.symm y) * J2 y ∂γ := by
          refine lintegral_congr_ae ((ae_restrict_iff' hSV).2 ?_)
          filter_upwards [hp] with y hy hyV
          by_cases hyB : y ∈ B
          · have : T.symm y ∈ T ⁻¹' B := by simpa using hyB
            rw [indicator_of_mem hyB, indicator_of_mem this, hy hyV]
          · have : T.symm y ∉ T ⁻¹' B := by simpa using hyB
            rw [indicator_of_notMem hyB, indicator_of_notMem this, zero_mul]
      _ = ∫⁻ y, (T ⁻¹' B).indicator J1 (T.symm y) ∂ρ1 := by
          rw [hρ1, lintegral_withDensity_eq_lintegral_mul _ hJ2 hmeasg]
          exact lintegral_congr fun y => mul_comm _ _
      _ = ∫⁻ x, (T ⁻¹' B).indicator J1 x ∂(Measure.map T.symm ρ1) :=
          (lintegral_map (hJ1.indicator hC) hTsm).symm
      _ ≤ ∫⁻ x, (T ⁻¹' B).indicator J1 x ∂(γ.restrict U) := lintegral_mono' hle le_rfl
      _ = ∫⁻ x in T ⁻¹' B, J1 x ∂γ := by
          rw [lintegral_indicator hC, Measure.restrict_restrict hC, inter_eq_left.2 hCV]
  have hEq : ∀ B : Set X, MeasurableSet B → B ⊆ T '' U →
      γ B = ∫⁻ x in T ⁻¹' B, J1 x ∂γ := fun B hB hBV =>
    le_antisymm (h4 B hB hBV) (h1 B hBV)
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply hTm hB,
    withDensity_apply _ (hTm hB), Measure.restrict_restrict (hTm hB)]
  have : T ⁻¹' B ∩ U = T ⁻¹' (B ∩ T '' U) := by
    ext x; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨x, h2, rfl⟩⟩
    · rintro ⟨h1, y, hy, hyx⟩; exact ⟨h1, by rwa [← hSinj hyx]⟩
  rw [this, ← hEq _ (hB.inter hSV) inter_subset_right]

end
end NlsGge.ThirdConsultation.R
