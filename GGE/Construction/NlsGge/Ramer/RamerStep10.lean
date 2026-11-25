import NlsGge.Ramer.ProjFieldNullPreserving
import NlsGge.Ramer.RamerLocalLowerBound
import NlsGge.Ramer.LocalJacobiExtension
import NlsGge.Ramer.LinearSmallJacobiLocal
import NlsGge.Ramer.HypothesisBridge
import NlsGge.Ramer.RamerStep1Locality

/-!
# R10-P6: Ramer's Step 10 (two-sided argument for the nonlinear map `T = I + iK`)

For a homeomorphism `T = I + iK` with `T⁻¹ = I + iK'` (`K`, `K'` of class `C²`) we prove the local
Jacobi identity `LocalJacobiUC` at every point, with density a measurable representative of
`ofReal ∘ ramerJac K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

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

section Concrete

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- From `T = I + iK`, `T⁻¹ = I + iK'`: `K' (T x) = -K x`. -/
theorem step10_GT (hs : (1 : ℝ) / 2 < s) (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y)) (x : FullWeightedHilbert c s) :
    K' (T x) = -K x := by
  have hs0 : 0 ≤ s := zero_le_of_half_lt hs
  have h := hTs (T x)
  rw [T.symm_apply_apply] at h
  have h2 : inclE c s hs (K' (T x)) = inclE c s hs (-K x) := by
    rw [map_neg]
    have h3 : x = x + inclE c s hs (K x) + inclE c s hs (K' (T x)) := by
      rw [← hT x]; exact h
    have h4 : inclE c s hs (K x) + inclE c s hs (K' (T x)) = 0 := by
      have := h3
      calc _ = (x + inclE c s hs (K x) + inclE c s hs (K' (T x))) - x := by abel
        _ = 0 := by rw [← h3]; simp
    exact eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h4)
  exact cmToFullWeightedHilbert_injective c s hs0 h2

/-- Invertibility of `I + D_H K(x)` and `I + D_H K'(T x)` is DERIVED from the hypotheses. -/
theorem step10_isUnit (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K') (x : FullWeightedHilbert c s) :
    IsUnit (1 + (hsDerivH c s hs K x).toCLM) ∧
      IsUnit (1 + (hsDerivH c s hs K' (T x)).toCLM) := by
  have hs0 : 0 ≤ s := zero_le_of_half_lt hs
  obtain ⟨L, hL, hLs⟩ := exists_inverse_id_add_HDeriv (inclE c s hs)
    (cmToFullWeightedHilbert_injective c s hs0) T K K' hT hTs
    (hK.differentiable (by norm_num)) (hK'.differentiable (by norm_num)) x
  have hA : (hsDerivH c s hs K x).toCLM = (fderiv ℝ K x).comp (inclE c s hs) :=
    hsDerivH_toCLM c s hs K x
  have hA' : (hsDerivH c s hs K' (T x)).toCLM = (fderiv ℝ K' (T x)).comp (inclE c s hs) :=
    hsDerivH_toCLM c s hs K' (T x)
  have e1 : 1 + (hsDerivH c s hs K x).toCLM = L.toContinuousLinearMap := by
    rw [hL, hA]; rfl
  have e2 : 1 + (hsDerivH c s hs K' (T x)).toCLM =
      L.symm.toContinuousLinearMap := by
    rw [hLs, hA']; rfl
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact ⟨⟨L, L.symm, by ext; simp, by ext; simp⟩, rfl⟩
  · rw [e2]
    exact ⟨⟨L.symm, L, by ext; simp, by ext; simp⟩, rfl⟩

/-- **Ramer Step 10, local form.**  Let `T` be a homeomorphism of `E` with `T = I + iK` and
`T⁻¹ = I + iK'`, `K`, `K'` of class `C²`.  There is a measurable `J` with
`J =ᵐ ofReal ∘ ramerJac K` such that every point has an open neighbourhood `V` with
`LocalJacobiUC γ_E T J V`. -/
theorem ramer_step10_local (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K')
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y)) :
    ∃ J : FullWeightedHilbert c s → ℝ≥0∞, Measurable J ∧
      (J =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
        fun x => ENNReal.ofReal (ramerJac c s hs K x)) ∧
      ∀ x₀ : FullWeightedHilbert c s, ∃ V : Set (FullWeightedHilbert c s), IsOpen V ∧ x₀ ∈ V ∧
        LocalJacobiUC (NlsGge.Measure.fullWeightedSequenceGaussian c s) T J V := by
  set γ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hγ
  have hmK := aemeasurable_ofReal_ramerJac c s hs K hK
  have hmK' := aemeasurable_ofReal_ramerJac c s hs K' hK'
  set J1 := hmK.mk with hJ1def
  set J2 := hmK'.mk with hJ2def
  have hJ1 : Measurable J1 := hmK.measurable_mk
  have hJ2 : Measurable J2 := hmK'.measurable_mk
  have hJ1ae : J1 =ᵐ[γ] fun x => ENNReal.ofReal (ramerJac c s hs K x) := hmK.ae_eq_mk.symm
  have hJ2ae : J2 =ᵐ[γ] fun x => ENNReal.ofReal (ramerJac c s hs K' x) := hmK'.ae_eq_mk.symm
  have hTM : TM c s hs K = ⇑T := funext fun x => (hT x).symm
  have hTM' : TM c s hs K' = ⇑T.symm := funext fun x => (hTs x).symm
  have hTl : (fun y => y + inclE c s hs (K y)) = ⇑T := hTM
  have hTl' : (fun y => y + inclE c s hs (K' y)) = ⇑T.symm := hTM'
  refine ⟨J1, hJ1, hJ1ae, fun x₀ => ?_⟩
  obtain ⟨hU1, hU2⟩ := step10_isUnit c s hs T K K' hT hTs (hK.of_le (by norm_num))
    (hK'.of_le (by norm_num)) x₀
  obtain ⟨V₁, hV₁o, hx₁, -, hge1, hnull1⟩ := ramer_local_lower_bound c s hs K hK x₀ hU1
  obtain ⟨V₂, hV₂o, hx₂, -, hge2, hnull2⟩ := ramer_local_lower_bound c s hs K' hK' (T x₀) hU2
  obtain ⟨r, hr, hTk0⟩ := projField_nullPres_eventually c s hs K hK x₀ hU1
  set U : Set (FullWeightedHilbert c s) := V₁ ∩ T ⁻¹' V₂ ∩ ball x₀ r with hUdef
  have hUo : IsOpen U := (hV₁o.inter (hV₂o.preimage T.continuous)).inter isOpen_ball
  have hx₀U : x₀ ∈ U := ⟨⟨hx₁, hx₂⟩, mem_ball_self hr⟩
  have hUV₁ : U ⊆ V₁ := fun x hx => hx.1.1
  have hUV₂ : ∀ x ∈ U, T x ∈ V₂ := fun x hx => hx.1.2
  refine ⟨U, hUo, hx₀U, ?_⟩
  have hTn : ∀ N : Set (FullWeightedHilbert c s), γ N = 0 → γ (U ∩ TM c s hs K ⁻¹' N) = 0 :=
    fun N hN => measure_mono_null (inter_subset_inter_left _ hUV₁) (hnull1 N hN)
  have hTk : ∀ᶠ k in atTop, ∀ N : Set (FullWeightedHilbert c s), γ N = 0 →
      γ (U ∩ TM c s hs (projField k K) ⁻¹' N) = 0 :=
    hTk0.mono fun k hk N hN =>
      measure_mono_null (inter_subset_inter_left _ (fun x hx => hx.2)) (hk N hN)
  have hd := ramerJac_comp_mul_eq_one_eventually c s hs U hUo K K' hK hK' hTn hTk
    (fun x _ => by rw [hTM]; exact step10_GT c s hs T K K' hT hTs x)
  rw [hTM] at hd
  -- null-set preservation of `T` on `U`, from `K'`
  let e : FullWeightedHilbert c s ≃ᵐ FullWeightedHilbert c s := T.toMeasurableEquiv
  have hes : ∀ x, e.symm x = T.symm x := fun x => rfl
  have hQ : ∀ N : Set (FullWeightedHilbert c s), γ N = 0 → γ (e '' (U ∩ N)) = 0 := by
    intro N hN
    refine measure_mono_null ?_ (hnull2 N hN)
    rintro _ ⟨x, ⟨hxU, hxN⟩, rfl⟩
    refine ⟨hUV₂ x hxU, ?_⟩
    have h5 : T x + inclE c s hs (K' (T x)) = x := by
      rw [← hTs (T x), T.symm_apply_apply]
    show T x + inclE c s hs (K' (T x)) ∈ N
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
    rw [b', c', ← ENNReal.ofReal_mul (ramerJac_nonneg c s hs K x), mul_comm]
    rw [hTM'] at *
    rw [show ramerJac c s hs K' (T x) * ramerJac c s hs K x = 1 from by
      have := a' hxV; simpa using this]
    simp
  have himg : ∀ B : Set (FullWeightedHilbert c s), T.symm ⁻¹' B = T '' B := by
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

/-- The same, with density `ofReal ∘ ramerJac K` itself (no measurability needed in the
definition of `LocalJacobiUC`). -/
theorem ramer_step10_local_ofReal (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K')
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y)) (x₀ : FullWeightedHilbert c s) :
    ∃ V : Set (FullWeightedHilbert c s), IsOpen V ∧ x₀ ∈ V ∧
      LocalJacobiUC (NlsGge.Measure.fullWeightedSequenceGaussian c s) T
        (fun x => ENNReal.ofReal (ramerJac c s hs K x)) V := by
  obtain ⟨J, -, hJae, hloc⟩ := ramer_step10_local c s hs T K K' hK hK' hT hTs
  obtain ⟨V, hVo, hxV, hV⟩ := hloc x₀
  refine ⟨V, hVo, hxV, fun F hF hb hnn hts => ?_⟩
  rw [hV F hF hb hnn hts]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hJae] with x hx
  rw [hx]

/-- Global consequence via R1 (`map_symm_eq_withDensity_of_local`). -/
theorem ramer_step10_global (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K')
    (hT : ∀ x, T x = x + inclE c s hs (K x))
    (hTs : ∀ y, T.symm y = y + inclE c s hs (K' y)) :
    ∃ J : FullWeightedHilbert c s → ℝ≥0∞, Measurable J ∧
      (J =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
        fun x => ENNReal.ofReal (ramerJac c s hs K x)) ∧
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).map T.symm =
        (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity J := by
  obtain ⟨J, hJm, hJae, hloc⟩ := ramer_step10_local c s hs T K K' hK hK' hT hTs
  exact ⟨J, hJm, hJae, map_symm_eq_withDensity_of_local _ T J hJm fun x₀ => by
    obtain ⟨V, hVo, hxV, hV⟩ := hloc x₀
    exact ⟨V, hVo, hxV, hV⟩⟩

#print axioms ramer_step10_global
#check @ramer_step10_global
#print axioms step10_GT
#print axioms step10_isUnit
#print axioms localJacobiUC_of_two_sided
#print axioms ramer_step10_local
#print axioms ramer_step10_local_ofReal
#check @ramer_step10_local_ofReal
#check @step10_GT
#check @step10_isUnit
#check @localJacobiUC_of_two_sided
#check @ramer_step10_local

end Concrete

end NlsGge.Ramer
