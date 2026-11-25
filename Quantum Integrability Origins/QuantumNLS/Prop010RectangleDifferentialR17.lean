import QuantumNLS.Prop010RectangleTransportR17

/-! Uniform-norm differentiation of the transported full-mass period.
No directional-interchange or differentiated-period hypothesis is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped BigOperators
namespace QuantumNLS.Prop010RectangleDifferentialR17
open Prop010RectangleTransportR17 PeriodReconstruction
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut)
open LabelExactPeriod (rectIntegral)

abbrev Boundary (a b h : ℝ) := ↥(Gam a b h)
instance boundaryCompact (a b h : ℝ) : CompactSpace (Boundary a b h) :=
  isCompact_iff_compactSpace.mp (isCompact_Gam a b h)

abbrev UI := DEF014AnalyticIntegration.UnitInterval

def sidePath {a b h : ℝ} (hab : a≤b) (hh : 0≤h) (i : Fin 4) : C(UI,Boundary a b h) :=
  ⟨fun s => ⟨side a b h i ((hi b h i-lo a h i)*s.1+lo a h i),by
    apply side_mem hab hh i
    have hl : lo a h i≤hi b h i := by fin_cases i <;> simp [lo,hi] <;> linarith
    constructor <;> nlinarith [s.2.1,s.2.2]⟩,by
    apply Continuous.subtype_mk
    fin_cases i <;> simp [side,lo,hi] <;> fun_prop⟩

def boundaryIntegral {a b h : ℝ} (hab : a≤b) (hh : 0≤h) : C(Boundary a b h,ℂ) →L[ℝ] ℂ :=
  ∑ i : Fin 4, (coeff i*((hi b h i-lo a h i:ℝ):ℂ)) •
    (DEF014AnalyticIntegration.integrateCLM.comp (ContinuousMap.compCLM (M := ℂ) (R := ℝ) (sidePath hab hh i)))

lemma boundaryIntegral_eq {a b h : ℝ} (hab : a≤b) (hh : 0≤h)
    (F : C(Boundary a b h,ℂ)) (f : ℂ → ℂ)
    (he : ∀ z : Boundary a b h,F z=f z.1) :
    boundaryIntegral hab hh F=rectIntegral f a b h := by
  rw [rect_sum]
  simp only [boundaryIntegral,sum_apply,smul_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have ht : DEF014AnalyticIntegration.integrateCLM ((ContinuousMap.compCLM (M := ℂ) (R := ℝ) (sidePath hab hh i)) F) =
      ∫ t in (0:ℝ)..1,f (side a b h i ((hi b h i-lo a h i)*t+lo a h i)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at ht
    change F (sidePath hab hh i (projIcc 0 1 (by norm_num) t)) = _
    rw [projIcc_of_mem (by norm_num) ht,he]
    rfl
  rw [ht,mul_assoc]
  congr 1
  have hx := intervalIntegral.smul_integral_comp_mul_add (a := (0:ℝ)) (b := 1)
    (fun t => f (side a b h i t)) (hi b h i-lo a h i) (lo a h i)
  rw [RCLike.real_smul_eq_coe_mul] at hx
  convert! hx using 1
  simp only [mul_zero,zero_add,mul_one,sub_add_cancel]

variable {L κ : ℝ} [Fact (0<L)]

/-- The actual full Cauchy field has one analytic germ in the uniform norm
of the very same rectangle as the norm reconstruction. -/
theorem rectangle_analytic_path (hκ : 0<κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h) :
    ∃ H : L2T L → C(Boundary (cut hκ u (n-1)) (cut hκ u n) h,ℂ),
      AnalyticAt ℝ H u ∧ ∀ᶠ v : L2T L in 𝓝 u,∀ z,H v z=G hκ z.1 v := by
  let a := cut hκ u (n-1)
  let b := cut hκ u n
  let Z : C(Boundary a b h,ℂ) := ⟨Subtype.val,continuous_subtype_val⟩
  have hZ : LipschitzWith 1 Z := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [NNReal.coe_one,one_mul]
    exact le_rfl
  obtain ⟨δ,hδ,hg⟩ := endpoint_gaps hκ u n
  have hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ q : ℝ ∂(PhysicalQuantumMeasure.measure hκ v),∀ z : Boundary a b h,min δ h≤‖Z z-(q:ℂ)‖ := by
    filter_upwards [hg] with v hv
    filter_upwards [hv] with q hq z
    exact Gam_dist hh hq.1 hq.2 z.2
  have hm : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal≤(‖u‖+1)^2 := by
    have hn : ∀ᶠ v : L2T L in 𝓝 u,‖v‖<‖u‖+1 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hn] with v hv
    rw [PhysicalQuantumMeasure.measure_univ,ENNReal.toReal_ofReal (sq_nonneg _)]
    nlinarith [norm_nonneg v,norm_nonneg u]
  have hr : ∀ᶠ v : L2T L in 𝓝 u,∀ z : Boundary a b h,Regular κ (v,Z z) := by
    have he : ∀ᶠ v : L2T L in 𝓝 u,∀ z ∈ Gam a b h,Regular κ (v,z) := by
      apply (isCompact_Gam a b h).eventually_forall_of_forall_eventually
      intro z hz
      exact (RootCauchyJointR9.isOpen_regular κ).mem_nhds
        (Prop010CutoffExistenceR11.rectangle_regular L hκ u n hh hz)
    filter_upwards [he] with v hv z
    exact hv z.1 z.2
  exact RootScalarDifferentialR10.exists_analytic_regular_path hκ Z hZ u
    (lt_min hδ hh) (sq_nonneg _) hgap hm hr

/-- Differentiation of the transported period, through a bounded real
linear boundary integral. This includes every radial variation. -/
theorem mass_differential_rectangle (hκ : 0<κ) (u v : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h) :
    (fderiv ℝ (mass hκ n) u v:ℂ)=(2*(Real.pi:ℂ)*I)⁻¹*
      rectIntegral (fun z => fderiv ℝ (G hκ z) u v) (cut hκ u (n-1)) (cut hκ u n) h := by
  obtain ⟨H,hH,hHe⟩ := rectangle_analytic_path hκ u n hh
  have hab : cut hκ u (n-1)≤cut hκ u n :=
    ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)).le
  let T := boundaryIntegral hab hh.le
  let J : L2T L → ℂ := fun w => T (H w)
  have hJ := T.hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt
  change HasFDerivAt J _ u at hJ
  have hDH : ∀ z : Boundary (cut hκ u (n-1)) (cut hκ u n) h,
      (fderiv ℝ H u v) z=fderiv ℝ (G hκ z.1) u v := by
    intro z
    have hd := (ContinuousMap.evalCLM ℝ z).hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt
    have heq : (fun w => H w z) =ᶠ[𝓝 u] G hκ z.1 := hHe.mono fun w hw => hw z
    have hhd := (hd.congr_of_eventuallyEq heq.symm).fderiv
    simpa using (congrArg (fun A : L2T L →L[ℝ] ℂ => A v) hhd).symm
  have heq : J =ᶠ[𝓝 u] fun w => rectIntegral (fun z => G hκ z w)
      (cut hκ u (n-1)) (cut hκ u n) h := by
    filter_upwards [hHe] with w hw
    exact boundaryIntegral_eq hab hh.le _ _ hw
  have hmass : (fun w => (mass hκ n w:ℂ)) =ᶠ[𝓝 u]
      fun w => (2*(Real.pi:ℂ)*I)⁻¹*J w := by
    filter_upwards [heq,eventually_rectangle_period hκ u n hh] with w hw hp
    rw [hw,hp]
    field_simp
  have hdM := Complex.ofRealCLM.hasFDerivAt.comp u
    (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u).differentiableAt.hasFDerivAt
  have hhM := (hdM.congr_of_eventuallyEq hmass.symm).fderiv
  have he := congrArg (fun A : L2T L →L[ℝ] ℂ => A v)
    (hhM.symm.trans (hJ.const_mul (2*(Real.pi:ℂ)*I)⁻¹).fderiv)
  change (fderiv ℝ (mass hκ n) u v:ℂ)=(2*(Real.pi:ℂ)*I)⁻¹*(T (fderiv ℝ H u v)) at he
  rw [boundaryIntegral_eq hab hh.le _ (fun z => fderiv ℝ (G hκ z) u v) hDH] at he
  exact he

/-- Source eq:B4-action-differential on the norm theorem's rectangle. -/
theorem action_differential_rectangle (hκ : 0<κ) (u v : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h) :
    fderiv ℝ (mass hκ n) u v= -(2*Real.pi*κ)⁻¹*
      (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u v /
        PeriodReconstructionCore.Df L κ (fun z => G hκ z u) z)
        (cut hκ u (n-1)) (cut hκ u n) h).re := by
  let J := rectIntegral (fun z => fderiv ℝ (G hκ z) u v) (cut hκ u (n-1)) (cut hκ u n) h
  have hm := mass_differential_rectangle hκ u v n hh
  have hj : J=(2*(Real.pi:ℂ)*I)*(fderiv ℝ (mass hκ n) u v:ℂ) := by
    change (fderiv ℝ (mass hκ n) u v:ℂ)=(2*(Real.pi:ℂ)*I)⁻¹*J at hm
    rw [hm]; field_simp
  have hp (z : ℂ) (hz : z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h) :
      fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u v /
        PeriodReconstructionCore.Df L κ (fun z => G hκ z u) z =
        (I*(κ:ℂ))*fderiv ℝ (G hκ z) u v := by
    have he := Prop010ClassicalR10.exponent_differential hκ u v z
      (Prop010CutoffExistenceR11.rectangle_regular L hκ u n hh hz)
    simpa only [PeriodReconstructionCore.Df,PeriodReconstructionCore.Af,
      ScalarLogBranchR10.difference,RootScalarPeriodR10.exponent,← Prop010CutoffExistenceR11.ef_exp] using he.symm
  have hab : cut hκ u (n-1)≤cut hκ u n :=
    ((DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)).le
  have he : rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u v /
      PeriodReconstructionCore.Df L κ (fun z => G hκ z u) z) (cut hκ u (n-1)) (cut hκ u n) h =
      rectIntegral (fun z => (I*(κ:ℂ))*fderiv ℝ (G hκ z) u v) (cut hκ u (n-1)) (cut hκ u n) h := by
    apply LabelExactPeriod.rectIntegral_congr
    · exact fun x hx => hp _ (PeriodTwoTerm.bot_mem hab hx)
    · exact fun x hx => hp _ (PeriodTwoTerm.top_mem hab hx)
    · exact fun y hy => hp _ (PeriodTwoTerm.right_mem hh.le hy)
    · exact fun y hy => hp _ (PeriodTwoTerm.left_mem hh.le hy)
  rw [he,PeriodTwoTerm.rectIntegral_const_mul]
  change _ = -(2*Real.pi*κ)⁻¹*((I*(κ:ℂ))*J).re
  rw [hj]
  simp only [mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im]
  norm_num
  field_simp

end QuantumNLS.Prop010RectangleDifferentialR17
