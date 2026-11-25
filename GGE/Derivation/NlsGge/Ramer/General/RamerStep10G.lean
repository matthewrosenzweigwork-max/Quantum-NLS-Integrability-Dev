import Mathlib
import NlsGge.Ramer.General.ProjFieldNullPreservingG
import NlsGge.Ramer.General.RamerLocalLowerBoundG
import NlsGge.Ramer.General.LinearSmallJacobiLocalG
import NlsGge.Ramer.General.RamerDensityG
import NlsGge.Ramer.General.HypothesisBridgeG
import NlsGge.Ramer.LocalJacobiExtension
import NlsGge.Ramer.RamerStep1Locality

/-!
# GE10: Ramer's Step 10 over a `RamerSetting` (two-sided argument for `T = I + iK`)

Generalization of `NlsGge/Ramer/RamerStep10.lean`.  For a homeomorphism `T = I + iK` of `S.E`
with `T⁻¹ = I + iK'` (`K`, `K'` of class `C²`) we prove the local Jacobi identity `LocalJacobiUC`
at every point, with density a measurable representative of `ofReal ∘ S.ramerJac K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

open NlsGge.Ramer

section Abstract

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The abstract two-sided argument of Ramer's Step 10: two lower bounds (for `T` on `T '' U`,
and for `T⁻¹` on `U`) together with `J2 * J1∘T⁻¹ = 1` a.e. on `T '' U` give the local Jacobi
identity for `T` on `U`. -/
theorem localJacobiUC_of_two_sided (γ : Measure X) (T : X ≃ₜ X) (U : Set X) (hU : IsOpen U)
    (J1 J2 : X → ℝ≥0∞) (hJ1 : Measurable J1) (hJ2 : Measurable J2)
    (h1 : ∀ B : Set X, B ⊆ T '' U → ∫⁻ x in T ⁻¹' B, J1 x ∂γ ≤ γ B)
    (h2 : ∀ A : Set X, A ⊆ U → ∫⁻ y in T '' A, J2 y ∂γ ≤ γ A)
    (hprod : ∀ᵐ y ∂γ, y ∈ T '' U → J1 (T.symm y) * J2 y = 1) :
    LocalJacobiUC γ T J1 U := by
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
    exact h2 (A' ∩ U) inter_subset_right
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
          filter_upwards [hprod] with y hy hyV
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
    le_antisymm (h4 B hB hBV) (by
      have := h1 B hBV
      exact this)
  have hmeq : γ.restrict (T '' U) = Measure.map T ((γ.restrict U).withDensity J1) := by
    ext B hB
    rw [Measure.restrict_apply hB, Measure.map_apply hTm hB,
      withDensity_apply _ (hTm hB), Measure.restrict_restrict (hTm hB)]
    have : T ⁻¹' B ∩ U = T ⁻¹' (B ∩ T '' U) := by
      ext x; constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, ⟨x, h2, rfl⟩⟩
      · rintro ⟨h1, y, hy, hyx⟩; exact ⟨h1, by rwa [← hSinj hyx]⟩
    rw [this, ← hEq _ (hB.inter hSV) inter_subset_right]
  intro F hF _ _ _
  have hFm : Measurable fun y => ENNReal.ofReal (F y) :=
    ENNReal.measurable_ofReal.comp hF.continuous.measurable
  have hFS : Measurable fun x => ENNReal.ofReal (F (T x)) := hFm.comp hTm
  rw [hmeq, lintegral_map hFm hTm, lintegral_withDensity_eq_lintegral_mul _ hJ1 hFS]
  exact lintegral_congr fun x => mul_comm _ _


end Abstract

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- From `T = I + iK`, `T⁻¹ = I + iK'`: `K' (T x) = -K x`. (Old: `step10_GT`.) -/
theorem step10_GT (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y)) (x : S.E) :
    K' (T x) = -K x := by
  have h := hTs (T x)
  rw [T.symm_apply_apply] at h
  have h2 : S.incl (K' (T x)) = S.incl (-K x) := by
    rw [map_neg]
    have h3 : x = x + S.incl (K x) + S.incl (K' (T x)) := by
      rw [← hT x]; exact h
    have h4 : S.incl (K x) + S.incl (K' (T x)) = 0 := by
      calc _ = (x + S.incl (K x) + S.incl (K' (T x))) - x := by abel
        _ = 0 := by rw [← h3]; simp
    exact eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h4)
  exact S.incl_injective h2

/-- Invertibility of `I + D_H K(x)` and `I + D_H K'(T x)` is DERIVED from the hypotheses.
(Old: `step10_isUnit`.) -/
theorem step10_isUnit
    (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K') (x : S.E) :
    IsUnit (1 + (S.hsDerivH K x).toCLM) ∧
      IsUnit (1 + (S.hsDerivH K' (T x)).toCLM) := by
  obtain ⟨L, hL, hLs⟩ := exists_inverse_id_add_HDeriv S.incl
    S.incl_injective T K K' hT hTs
    (hK.differentiable (by norm_num)) (hK'.differentiable (by norm_num)) x
  have hA : (S.hsDerivH K x).toCLM = (fderiv ℝ K x).comp S.incl :=
    S.hsDerivH_toCLM K x
  have hA' : (S.hsDerivH K' (T x)).toCLM = (fderiv ℝ K' (T x)).comp S.incl :=
    S.hsDerivH_toCLM K' (T x)
  have e1 : 1 + (S.hsDerivH K x).toCLM = L.toContinuousLinearMap := by
    rw [hL, hA]; rfl
  have e2 : 1 + (S.hsDerivH K' (T x)).toCLM =
      L.symm.toContinuousLinearMap := by
    rw [hLs, hA']; rfl
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact ⟨⟨L, L.symm, by ext; simp, by ext; simp⟩, rfl⟩
  · rw [e2]
    exact ⟨⟨L.symm, L, by ext; simp, by ext; simp⟩, rfl⟩

/-- **Ramer Step 10, local form.**  (Old: `ramer_step10_local`.) -/
theorem ramer_step10_local
    (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K')
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y)) :
    ∃ J : S.E → ℝ≥0∞, Measurable J ∧
      (J =ᵐ[S.γE]
        fun x => ENNReal.ofReal (S.ramerJac K x)) ∧
      ∀ x₀ : S.E, ∃ V : Set S.E, IsOpen V ∧ x₀ ∈ V ∧
        LocalJacobiUC S.γE T J V := by
  set γ := S.γE with hγ
  have hmK := S.aemeasurable_ofReal_ramerJac K hK
  have hmK' := S.aemeasurable_ofReal_ramerJac K' hK'
  set J1 := hmK.mk with hJ1def
  set J2 := hmK'.mk with hJ2def
  have hJ1 : Measurable J1 := hmK.measurable_mk
  have hJ2 : Measurable J2 := hmK'.measurable_mk
  have hJ1ae : J1 =ᵐ[γ] fun x => ENNReal.ofReal (S.ramerJac K x) := hmK.ae_eq_mk.symm
  have hJ2ae : J2 =ᵐ[γ] fun x => ENNReal.ofReal (S.ramerJac K' x) := hmK'.ae_eq_mk.symm
  have hTM : S.TM K = ⇑T := funext fun x => (hT x).symm
  have hTM' : S.TM K' = ⇑T.symm := funext fun x => (hTs x).symm
  have hTl : (fun y => y + S.incl (K y)) = ⇑T := hTM
  have hTl' : (fun y => y + S.incl (K' y)) = ⇑T.symm := hTM'
  refine ⟨J1, hJ1, hJ1ae, fun x₀ => ?_⟩
  obtain ⟨hU1, hU2⟩ := S.step10_isUnit T K K' hT hTs (hK.of_le (by norm_num))
    (hK'.of_le (by norm_num)) x₀
  obtain ⟨V₁, hV₁o, hx₁, -, hge1, hnull1⟩ := S.ramer_local_lower_bound K hK x₀ hU1
  obtain ⟨V₂, hV₂o, hx₂, -, hge2, hnull2⟩ := S.ramer_local_lower_bound K' hK' (T x₀) hU2
  obtain ⟨r, hr, hTk0⟩ := S.projField_nullPres_eventually K hK x₀ hU1
  set U : Set S.E := V₁ ∩ T ⁻¹' V₂ ∩ ball x₀ r with hUdef
  have hUo : IsOpen U := (hV₁o.inter (hV₂o.preimage T.continuous)).inter isOpen_ball
  have hx₀U : x₀ ∈ U := ⟨⟨hx₁, hx₂⟩, mem_ball_self hr⟩
  have hUV₁ : U ⊆ V₁ := fun x hx => hx.1.1
  have hUV₂ : ∀ x ∈ U, T x ∈ V₂ := fun x hx => hx.1.2
  refine ⟨U, hUo, hx₀U, ?_⟩
  have hTn : ∀ N : Set S.E, γ N = 0 → γ (U ∩ S.TM K ⁻¹' N) = 0 :=
    fun N hN => measure_mono_null (inter_subset_inter_left _ hUV₁) (hnull1 N hN)
  have hTk : ∀ᶠ k in atTop, ∀ N : Set S.E,
      γ N = 0 → γ (U ∩ S.TM (S.projField k K) ⁻¹' N) = 0 :=
    hTk0.mono fun k hk N hN =>
      measure_mono_null (inter_subset_inter_left _ (fun x hx => hx.2)) (hk N hN)
  have hd := S.ramerJac_comp_mul_eq_one_eventually U hUo K K' hK hK' hTn hTk
    (fun x _ => by rw [hTM]; exact S.step10_GT T K K' hT hTs x)
  rw [hTM] at hd
  -- null-set preservation of `T` on `U`, from `K'`
  let e : S.E ≃ᵐ S.E := T.toMeasurableEquiv
  have hes : ∀ x, e.symm x = T.symm x := fun x => rfl
  have hQ : ∀ N : Set S.E, γ N = 0 → γ (e '' (U ∩ N)) = 0 := by
    intro N hN
    refine measure_mono_null ?_ (hnull2 N hN)
    rintro _ ⟨x, ⟨hxU, hxN⟩, rfl⟩
    refine ⟨hUV₂ x hxU, ?_⟩
    have h5 : T x + S.incl (K' (T x)) = x := by
      rw [← hTs (T x), T.symm_apply_apply]
    show T x + S.incl (K' (T x)) ∈ N
    rw [h5]; exact hxN
  have hT1 := ae_transfer γ e U hQ _ hd
  have hT2 := ae_transfer γ e U hQ _ hJ1ae
  have hprod : ∀ᵐ y ∂γ, y ∈ T '' U → J1 (T.symm y) * J2 y = 1 := by
    filter_upwards [hT1, hT2, hJ2ae] with y a b c' hy
    have hyV : y ∈ e '' U := hy
    have a' := a hyV
    have b' := b hyV
    rw [hes] at a' b'
    obtain ⟨x, hxV, rfl⟩ := hy
    rw [T.symm_apply_apply] at a' b' ⊢
    rw [b', c', ← ENNReal.ofReal_mul (S.ramerJac_nonneg K x), mul_comm]
    rw [hTM'] at *
    rw [show S.ramerJac K' (T x) * S.ramerJac K x = 1 from by
      have := a' hxV; simpa using this]
    simp
  have himg : ∀ B : Set S.E, T.symm ⁻¹' B = T '' B := by
    intro B; ext x; constructor
    · intro h; exact ⟨T.symm x, h, T.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  refine localJacobiUC_of_two_sided γ T U hUo J1 J2 hJ1 hJ2 ?_ ?_ hprod
  · intro B hB
    have hsub : T ⁻¹' B ⊆ U := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hB hx
      rwa [← T.injective hyx]
    have := hge1 B
    rw [hTl, inter_eq_right.2 (hsub.trans hUV₁)] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr_ae (ae_restrict_of_ae hJ1ae)
  · intro A' hA'
    have := hge2 A'
    rw [hTl', himg, inter_eq_right.2 (image_subset_iff.2 (fun x hx => hUV₂ x (hA' hx)) |>.trans
      (by exact fun y hy => by simpa using hy) : T '' A' ⊆ V₂)] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr_ae (ae_restrict_of_ae hJ2ae)

/-- The same, with density `ofReal ∘ S.ramerJac K` itself. (Old: `ramer_step10_local_ofReal`.) -/
theorem ramer_step10_local_ofReal
    (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K')
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y)) (x₀ : S.E) :
    ∃ V : Set S.E, IsOpen V ∧ x₀ ∈ V ∧
      LocalJacobiUC S.γE T
        (fun x => ENNReal.ofReal (S.ramerJac K x)) V := by
  obtain ⟨J, -, hJae, hloc⟩ := S.ramer_step10_local T K K' hK hK' hT hTs
  obtain ⟨V, hVo, hxV, hV⟩ := hloc x₀
  refine ⟨V, hVo, hxV, fun F hF hb hnn hts => ?_⟩
  rw [hV F hF hb hnn hts]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hJae] with x hx
  rw [hx]

/-- Global consequence via R1 (`map_symm_eq_withDensity_of_local`).
(Old: `ramer_step10_global`.) -/
theorem ramer_step10_global
    (T : S.E ≃ₜ S.E)
    (K K' : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K')
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y)) :
    ∃ J : S.E → ℝ≥0∞, Measurable J ∧
      (J =ᵐ[S.γE]
        fun x => ENNReal.ofReal (S.ramerJac K x)) ∧
      S.γE.map T.symm = S.γE.withDensity J := by
  obtain ⟨J, hJm, hJae, hloc⟩ := S.ramer_step10_local T K K' hK hK' hT hTs
  exact ⟨J, hJm, hJae, map_symm_eq_withDensity_of_local _ T J hJm fun x₀ => by
    obtain ⟨V, hVo, hxV, hV⟩ := hloc x₀
    exact ⟨V, hVo, hxV, hV⟩⟩

end NlsGge.Ramer.General.RamerSetting
