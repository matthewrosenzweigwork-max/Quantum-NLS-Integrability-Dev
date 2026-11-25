import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14ActionRaw
import NlsGge.Atomic.PDE.PDE059
import NlsGge.ThirdConsultation.PDE.PDE060Cone
import NlsGge.ThirdConsultation.PDE.PDE060Borel
import NlsGge.ThirdConsultation.PDE.LP1Separable

/- PDE061CORE PRODUCTION01 (proof development, AUTHOR; not reviewed). Proposed target NlsGge/ThirdConsultation/PDE/PDE061Core.lean,
   namespace NlsGge.ThirdConsultation.PDE. Core for PDE-061 (no packet increment), for ANY choice ch of local analytic
   action extensions (instantiated in PDE061 with chosenActionExtension):
   freq_continuous: J ↦ w_n · fderiv (ch J) J.val e_n is norm-continuous on the cone (near J₀, PDE-059 replaces ch J by the
     fixed analytic ch J₀, whose fderiv is analytic hence continuous: AnalyticOnNhd.fderiv);
   measurable_omega_of: the zero-extended raw-action function is product-measurable (norm Borel = coordinate comap,
     PDE-060 (ii) with LP1Separable; actionCoe ∘ rawActionToPositive = id; cone measurable, PDE-060 (i)). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GKDefinitionDesign
namespace NlsGge.ThirdConsultation.PDE

theorem freq_continuous (ch : PositiveActionSpace → WeightedActionSpace → ℝ)
    (hch : ∀ I, LocalActionExtension (ch I) I) (n : ℤ) :
    Continuous (fun J : PositiveActionSpace =>
      actionWeight n * fderiv ℝ (ch J) J.val (lp.single 1 n (1 : ℝ))) := by
  rw [continuous_iff_continuousAt]
  intro J0
  obtain ⟨U0, hU0, hJ0, ha0, hag0⟩ := hch J0
  have hnb : (fun J : PositiveActionSpace => J.val) ⁻¹' U0 ∈ 𝓝 J0 :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hU0.mem_nhds hJ0)
  have hev : (fun J : PositiveActionSpace =>
        actionWeight n * fderiv ℝ (ch J0) J.val (lp.single 1 n (1 : ℝ))) =ᶠ[𝓝 J0]
      (fun J : PositiveActionSpace =>
        actionWeight n * fderiv ℝ (ch J) J.val (lp.single 1 n (1 : ℝ))) := by
    filter_upwards [hnb] with J hJ
    rw [action_frequency_extension_independent (ch J) (ch J0) J n (hch J) ⟨U0, hU0, hJ, ha0, hag0⟩]
  have h1 : ContinuousAt (fderiv ℝ (ch J0)) J0.val := (ha0.fderiv J0.val hJ0).continuousAt
  have hc : ContinuousAt (fun J : PositiveActionSpace =>
      actionWeight n * fderiv ℝ (ch J0) J.val (lp.single 1 n (1 : ℝ))) J0 :=
    continuousAt_const.mul
      ((h1.comp continuous_subtype_val.continuousAt).clm_apply continuousAt_const)
  exact hc.congr hev

theorem actionCoe_rawActionToPositive (I : ℤ → ℝ) (hI : I ∈ positiveActionCone) :
    actionCoe (rawActionToPositive I hI) = I := by
  funext n
  show (actionWeight n * I n) / actionWeight n = I n
  have h : actionWeight n ≠ 0 := (sobolevModeWeight_pos 1 n).ne'
  field_simp

open scoped Classical in
theorem measurable_omega_of (ch : PositiveActionSpace → WeightedActionSpace → ℝ)
    (hch : ∀ I, LocalActionExtension (ch I) I) (n : ℤ) :
    Measurable (fun I : ℤ → ℝ =>
      if hI : I ∈ positiveActionCone then
        actionWeight n * fderiv ℝ (ch (rawActionToPositive I hI)) (rawActionToPositive I hI).val
          (lp.single 1 n (1 : ℝ))
      else 0) := by
  intro B hB
  set Ω := fun J : PositiveActionSpace =>
    actionWeight n * fderiv ℝ (ch J) J.val (lp.single 1 n (1 : ℝ)) with hΩ
  have hΩm : MeasurableSet[actionNormBorel] (Ω ⁻¹' B) := by
    letI : MeasurableSpace PositiveActionSpace := actionNormBorel
    haveI : BorelSpace PositiveActionSpace := ⟨rfl⟩
    exact (freq_continuous ch hch n).measurable hB
  rw [actionNormBorel_eq_comap lp_one_int_real_separableSpace] at hΩm
  obtain ⟨T, hT, hTeq⟩ := hΩm
  have hprod : actionProductBorel = (inferInstance : MeasurableSpace (ℤ → ℝ)) :=
    (BorelSpace.measurable_eq (α := ℤ → ℝ)).symm
  rw [hprod] at hT
  have hset : (fun I : ℤ → ℝ =>
      if hI : I ∈ positiveActionCone then
        actionWeight n * fderiv ℝ (ch (rawActionToPositive I hI)) (rawActionToPositive I hI).val
          (lp.single 1 n (1 : ℝ))
      else 0) ⁻¹' B =
      (positiveActionCone ∩ T) ∪ (positiveActionConeᶜ ∩ {_I | (0 : ℝ) ∈ B}) := by
    ext I
    by_cases hI : I ∈ positiveActionCone
    · rw [Set.mem_preimage, dif_pos hI]
      have h := congrArg (fun s => rawActionToPositive I hI ∈ s) hTeq
      simp only [Set.mem_preimage, actionCoe_rawActionToPositive] at h
      have key : (Ω (rawActionToPositive I hI) ∈ B) ↔ I ∈ T := (Eq.to_iff h).symm
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, hI,
        not_true_eq_false, false_and, or_false, true_and]
      exact key
    · rw [Set.mem_preimage, dif_neg hI]
      simp [hI]
  rw [hset]
  exact (positiveActionCone_measurableSet.inter hT).union
    (positiveActionCone_measurableSet.compl.inter (MeasurableSet.const _))

end NlsGge.ThirdConsultation.PDE
