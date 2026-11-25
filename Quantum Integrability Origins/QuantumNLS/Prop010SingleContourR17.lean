import QuantumNLS.Prop010RectangleDifferentialR17

/-! PROP-010 on a single declared rectangle and a single constructed smooth
extension pair. The full-mass period transport, leading symbol and full
real differential use exactly the contour in the condensate norm bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped ContDiff
namespace QuantumNLS.Prop010SingleContourR17
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut)
open RootScalarPeriodR10 (symbol lambda exponent exponential)
open PeriodReconstructionCore PeriodReconstruction PeriodTwoTerm
open Prop010ContourBindingR11
open Prop010RectangleTransportR17
open LabelExactPeriod (rectIntegral)
variable {L κ : ℝ} [Fact (0<L)]

lemma rect_congr {a b h : ℝ} (hab : a≤b) (hh : 0≤h) {f g : ℂ → ℂ}
    (he : EqOn f g (Gam a b h)) : rectIntegral f a b h=rectIntegral g a b h :=
  LabelExactPeriod.rectIntegral_congr (fun _ hx => he (bot_mem hab hx))
    (fun _ hx => he (top_mem hab hx)) (fun _ hx => he (right_mem hh hx))
    (fun _ hx => he (left_mem hh hx))

lemma log_eq_lambda (hκ : 0<κ) (u : L2T L) (z w : ℂ) :
    localLog L κ (fun z => G hκ z u) z w=lambda hκ u z w := by
  simp only [localLog,localRoot,lambda,ScalarLogBranchR10.localLog,ScalarLogBranchR10.root,
    ScalarLogBranchR10.difference,ScalarLogBranchR10.transfer,sf,Df,Af,exponent,
    Prop010CutoffExistenceR11.ef_exp]

lemma background_eq_symbol (hκ : 0<κ) (u : L2T L) (z : ℂ)
    (hz : RootCauchyJointR9.Regular κ (u,z)) :
    sf L κ (fun z => G hκ z u) z=symbol κ u z := by
  rw [RootScalarPeriodR10.transfer_identity hκ u z hz]
  simp only [sf,Af,ScalarLogBranchR10.transfer,exponent,Prop010CutoffExistenceR11.ef_exp]

/-- Uniform branch agreement, transported to the fixed rectangle. -/
theorem eventually_lambda_rectangle (hκ : 0<κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h) :
    ∀ᶠ v : L2T L in 𝓝 u,∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,
      lambda hκ u z (symbol κ v z)=exponent hκ v z := by
  apply (isCompact_Gam _ _ _).eventually_forall_of_forall_eventually
  intro z hz
  have hr := Prop010CutoffExistenceR11.rectangle_regular L hκ u n hh hz
  have hc := (RootCauchyJointR9.continuousAt_joint_regular hκ (u,z) hr).const_mul (I*(κ:ℂ))
  have hc0 : ContinuousAt (fun p : L2T L × ℂ => exponent hκ u p.2) (u,z) := by
    have hj : ContinuousAt (fun p : L2T L × ℂ => (u,p.2)) (u,z) :=
      (continuous_const.prodMk continuous_snd).continuousAt
    exact ((RootCauchyJointR9.continuousAt_joint_regular hκ (u,z) hr).comp
      (f := fun p : L2T L × ℂ => (u,p.2)) hj).const_mul (I*(κ:ℂ))
  have he : ContinuousAt (fun p : L2T L × ℂ => exponential L p.2) (u,z) := by
    unfold exponential; fun_prop
  have hl := ScalarLogBranchR10.eventually_localLog he hc0 hc rfl
    (RootScalarPeriodR10.difference_ne hκ u z hr)
  filter_upwards [hl,(RootCauchyJointR9.isOpen_regular κ).mem_nhds hr] with p hp hpr
  change ScalarLogBranchR10.localLog _ _ _ = _
  rw [RootScalarPeriodR10.transfer_identity hκ p.1 p.2 hpr]
  exact hp

/-- Source eq:B4-classical-action-functional for the actual chosen F. -/
def leadingSymbol (hκ : 0<κ) (u : L2T L) (n : ℤ) (h : ℝ)
    (F : ℂ × ℂ → ℂ) (v : L2T L) : ℝ :=
  -(2*Real.pi*κ)⁻¹*(rectIntegral (fun z => F (z,symbol κ v z))
    (cut hκ u (n-1)) (cut hκ u n) h).re

/-- Every constructed extension pair has the actual full-neighborhood
symbol, with no period or differentiated identity added as a premise. -/
theorem leading_identification (hκ : 0<κ) (u : L2T L) (n : ℤ) {h r : ℝ}
    (hh : 0<h) (hr : 0<r) (F : ℂ × ℂ → ℂ)
    (hf : ∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,∀ w,
      ‖w-sf L κ (fun z => G hκ z u) z‖<r → F (z,w)=localLog L κ (fun z => G hκ z u) z w) :
    ∃ U : Set (L2T L),IsOpen U ∧ u ∈ U ∧
      (∀ v ∈ U,leadingSymbol hκ u n h F v=mass hκ n v) ∧
      (∀ v ∈ U,AnalyticAt ℝ (leadingSymbol hκ u n h F) v) ∧
      (∀ v ∈ U,fderiv ℝ (leadingSymbol hκ u n h F) v=fderiv ℝ (mass hκ n) v) := by
  have hc : Continuous (fun p : L2T L × ℂ => symbol κ p.1 p.2) := by
    simp_rw [Prop010ClassicalR10.symbol_eq_trace hκ]
    have hd : Continuous (fun p : L2T L × ℂ => L2SpatialTransfer.discriminant κ p.1 p.2) :=
      continuous_iff_continuousAt.mpr fun p =>
        (DEF014DiscriminantAnalytic.analyticAt_discriminant_joint κ p).continuousAt
    exact (by fun_prop : Continuous (fun p : L2T L × ℂ => exp (I*p.2*L/2))).mul hd
  have hc0 := hc.comp (show Continuous (fun p : L2T L × ℂ => (u,p.2)) from
    continuous_const.prodMk continuous_snd)
  have hev : ∀ᶠ v : L2T L in 𝓝 u,∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,
      ‖symbol κ v z-symbol κ u z‖<r := by
    apply (isCompact_Gam _ _ _).eventually_forall_of_forall_eventually
    intro z _
    exact (hc.sub hc0).norm.continuousAt.eventually (gt_mem_nhds (by simpa using hr))
  have heq : ∀ᶠ v : L2T L in 𝓝 u,leadingSymbol hκ u n h F v=mass hκ n v := by
    filter_upwards [hev,eventually_lambda_rectangle hκ u n hh,eventually_rectangle_period hκ u n hh] with v hv hl hp
    have hab : cut hκ u (n-1)≤cut hκ u n :=
      ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)).le
    have he : rectIntegral (fun z => F (z,symbol κ v z)) (cut hκ u (n-1)) (cut hκ u n) h =
        (I*(κ:ℂ))*rectIntegral (fun z => G hκ z v) (cut hκ u (n-1)) (cut hκ u n) h := by
      rw [← rectIntegral_const_mul]
      apply rect_congr hab hh.le
      intro z hz
      change F (z,symbol κ v z)=(I*(κ:ℂ))*G hκ z v
      rw [hf z hz _ (by rw [background_eq_symbol hκ u z
        (Prop010CutoffExistenceR11.rectangle_regular L hκ u n hh hz)]; exact hv z hz),log_eq_lambda,hl z hz]
      rfl
    rw [leadingSymbol,he,hp]
    simp only [mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im]
    norm_num
    field_simp
  obtain ⟨U,hsub,hU,hu⟩ := mem_nhds_iff.mp heq
  refine ⟨U,hU,hu,hsub,?_,?_⟩
  · intro v hv
    apply (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n v).congr
    filter_upwards [hU.mem_nhds hv] with w hw
    exact (hsub hw).symm
  · intro v hv
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds hv] with w hw
    exact hsub hw

/-- PROP-010, lem:B4-condensate-reconstruction: one rectangle and the SAME
constructed F,H in its operator definition and classical leading symbol.
The full-mass identity is proved by contour transport, so no additional
period premise is needed. All real Hilbert variations are included. -/
theorem condensate_reconstruction (hκ : 0<κ) (u : L2T L) (hu : ‖u‖=1) (n : ℤ)
    {h : ℝ} (hh : 0<h) :
    ∃ F : ℂ × ℂ → ℂ,∃ H : ℂ × (ℂ × ℂ) → ℂ,
    ∃ hF : ContDiff ℝ ∞ F,∃ hFc : HasCompactSupport F,
    ∃ hH : ContDiff ℝ ∞ H,∃ hHc : HasCompactSupport H,∃ r>0,
      (∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,∀ w,
        ‖w-sf L κ (fun z => G hκ z u) z‖<r → F (z,w)=localLog L κ (fun z => G hκ z u) z w) ∧
      (∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h,∀ w v,
        ‖w-sf L κ (fun z => G hκ z u) z‖<r → ‖v‖≤MixedQuadratures.Rbd L κ (h+1) →
        H (z,(w,v))=localCorrection L κ (fun z => G hκ z u) z w v) ∧
      (let f := Extension.ofSmooth F hF hFc
       let g := Extension.ofSmooth H hH hHc
       ∃ D≥0,∃ N₀ : ℕ,∀ (N : ℕ) (hN : 0<N),N₀≤N →
         IsSelfAdjoint (C L hκ hN f g (cut hκ u (n-1)) (cut hκ u n) h) ∧
         ‖C L hκ hN f g (cut hκ u (n-1)) (cut hκ u n) h‖≤K κ (cut hκ u (n-1)) (cut hκ u n) h f g ∧
         ‖(B L hκ hN n-C L hκ hN f g (cut hκ u (n-1)) (cut hκ u n) h)
           (HighMomentsOps.wvec N u)‖≤D*((N:ℝ)⁻¹)^2) ∧
      (∃ U : Set (L2T L),IsOpen U ∧ u ∈ U ∧
        (∀ v ∈ U,leadingSymbol hκ u n h F v=mass hκ n v) ∧
        (∀ v ∈ U,AnalyticAt ℝ (leadingSymbol hκ u n h F) v) ∧
        (∀ v ∈ U,fderiv ℝ (leadingSymbol hκ u n h F) v=fderiv ℝ (mass hκ n) v)) ∧
      (∀ v : L2T L,fderiv ℝ (mass hκ n) u v= -(2*Real.pi*κ)⁻¹*
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => symbol κ w z) u v /
          Df L κ (fun z => G hκ z u) z) (cut hκ u (n-1)) (cut hκ u n) h).re) := by
  obtain ⟨F,H,hF,hFc,hH,hHc,r,hr,hf,hg,hN⟩ :=
    Prop010CutoffExistenceR11.condensate_reconstruction L hκ u hu n hh
  exact ⟨F,H,hF,hFc,hH,hHc,r,hr,hf,hg,hN,
    leading_identification hκ u n hh hr F hf,
    fun v => Prop010RectangleDifferentialR17.action_differential_rectangle hκ u v n hh⟩

end QuantumNLS.Prop010SingleContourR17
