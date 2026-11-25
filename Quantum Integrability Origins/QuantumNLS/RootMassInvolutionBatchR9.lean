import QuantumNLS.HolomorphicStageD3
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.Conformal
import QuantumNLS.RootMassInvolutionR8
import QuantumNLS.PhysicalPhaseHolomorphic

/-! sol_multi round 9: serial, single-queue batch of the complete spectral
covector, continuation, fixed-contour differential and mass-pair proof.
Author verification only; independent reviewer terra_review. -/

-- Source component: RootSpectralCovectorR9

/-! Bounded-covector holomorphy from joint real analyticity and actual
spectral holomorphy. This is an application lemma, not an assumed physical
regularity or bracket-vanishing statement. -/
attribute [local instance] InnerProductSpace.complexToReal
set_option autoImplicit false
set_option maxErrors 200
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Topology
namespace QuantumNLS.RootSpectralCovectorR9
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fieldCovector differential in the real field, in its operator norm. -/
def fieldCovector (F : E × ℂ → ℂ) (p : E × ℂ) : E →L[ℝ] ℂ :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℂ)

lemma fieldCovector_eq (F : E × ℂ → ℂ) (p : E × ℂ)
    (hf : DifferentiableAt ℝ F p) :
    fieldCovector F p = fderiv ℝ (fun v => F (v,p.2)) p.1 := by
  exact ((hf.hasFDerivAt.comp p.1
    ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const (c := p.2) p.1))).fderiv).symm

/-- CR for the mixed second derivative, obtained by differentiating the
spectral CR identity in a real field direction and using Hessian symmetry. -/
lemma mixed_CR {F : E × ℂ → ℂ} {u : E} {z : ℂ}
    (hf : AnalyticAt ℝ F (u,z))
    (hh : ∀ᶠ p : E × ℂ in 𝓝 (u,z), DifferentiableAt ℂ (fun w => F (p.1,w)) p.2)
    (v : E) :
    fderiv ℝ (fderiv ℝ F) (u,z) (0,Complex.I) (v,0) =
      Complex.I * fderiv ℝ (fderiv ℝ F) (u,z) (0,1) (v,0) := by
  have hA := hf.fderiv.differentiableAt
  have he : (fun p => fderiv ℝ F p (0,Complex.I)) =ᶠ[𝓝 (u,z)]
      (fun p => Complex.I * fderiv ℝ F p (0,1)) := by
    filter_upwards [hh,hf.eventually_analyticAt] with p hp hfp
    have hj : HasFDerivAt (fun w : ℂ => (p.1,w)) (ContinuousLinearMap.inr ℝ E ℂ) p.2 := by
      simpa using ((ContinuousLinearMap.inr ℝ E ℂ).hasFDerivAt.add_const (p.1,0))
    have hslice := hfp.differentiableAt.hasFDerivAt.comp p.2 hj
    dsimp only [Function.comp_def] at hslice
    have hcr := (differentiableAt_complex_iff_differentiableAt_real.mp hp).2
    rw [hslice.fderiv] at hcr
    simpa using hcr
  have hleft := hA.hasFDerivAt.clm_apply (hasFDerivAt_const (c := ((0,Complex.I) : E × ℂ)) (u,z))
  have hright := (hA.hasFDerivAt.clm_apply
    (hasFDerivAt_const (c := ((0,(1 : ℂ)) : E × ℂ)) (u,z))).const_mul Complex.I
  have hd := hleft.unique (hright.congr_of_eventuallyEq he)
  have hdv := DFunLike.congr_fun hd (v,0)
  have hcd : ContDiffAt ℝ 2 F (u,z) := hf.contDiffAt
  have hs := hcd.isSymmSndFDerivAt (by norm_num)
  have hdv' : fderiv ℝ (fderiv ℝ F) (u,z) (v,0) (0,Complex.I) =
      Complex.I * fderiv ℝ (fderiv ℝ F) (u,z) (v,0) (0,1) := by
    simpa using hdv
  rwa [hs (v,0) (0,Complex.I),hs (v,0) (0,1)] at hdv'

lemma differentiableAt_fieldCovector {F : E × ℂ → ℂ} {u : E} {z : ℂ}
    (hf : AnalyticAt ℝ F (u,z))
    (hh : ∀ᶠ p : E × ℂ in 𝓝 (u,z), DifferentiableAt ℂ (fun w => F (p.1,w)) p.2) :
    DifferentiableAt ℂ (fun w => fieldCovector F (u,w)) z := by
  have hA := hf.fderiv.differentiableAt.hasFDerivAt
  have hd := (hA.comp z ((hasFDerivAt_const (𝕜 := ℝ) u z).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) z))).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.inl ℝ E ℂ) z)
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨hd.differentiableAt,?_⟩
  dsimp only [Function.comp_def] at hd
  unfold fieldCovector
  rw [hd.fderiv]
  ext v
  simpa using mixed_CR hf hh v

/-- Holomorphic dependence in operator norm, rather than only after each
scalar evaluation. The accepted GP-05 bridge supplies a covector-valued series. -/
theorem analyticAt_fieldCovector {F : E × ℂ → ℂ} {u : E} {z : ℂ}
    (hf : AnalyticAt ℝ F (u,z))
    (hh : ∀ᶠ p : E × ℂ in 𝓝 (u,z), DifferentiableAt ℂ (fun w => F (p.1,w)) p.2) :
    AnalyticAt ℂ (fun w => fieldCovector F (u,w)) z := by
  have hall : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (fun t => fieldCovector F (u,t)) w := by
    have hj : Continuous (fun w : ℂ => (u,w)) := continuous_const.prodMk continuous_id
    filter_upwards [hj.continuousAt.eventually hf.eventually_analyticAt,
      hj.continuousAt.eventually (eventually_eventually_nhds.mpr hh)] with w hfw hhw
    exact differentiableAt_fieldCovector hfw hhw
  obtain ⟨U,hU,hopen,hzU⟩ := mem_nhds_iff.mp hall
  exact HolomorphicStageD3.analyticAt_of_differentiableOn hopen
    (fun w hw => (hU hw).differentiableWithinAt) hzU
end QuantumNLS.RootSpectralCovectorR9

-- Source component: RootCauchyJointR9

/-! Joint full-field/spectral regularity of the literal positive-measure
Cauchy transform. The domain includes both half-planes and open real bands.
No bracket-vanishing, zero-mass, or contour-exchange premise is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Topology MeasureTheory ComplexConjugate
namespace QuantumNLS.RootCauchyJointR9
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
variable {L κ : ℝ} [Fact (0 < L)]

/-- A fixed spectral point is uniformly separated from the nearby measures. -/
def Away (hκ : 0 < κ) (u : L2T L) (z : ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ v : L2T L in 𝓝 u,
    ∀ᵐ t : ℝ ∂(PhysicalQuantumMeasure.measure hκ v), δ ≤ ‖z-(t : ℂ)‖

/-- Both half-planes and the real open bands of the actual discriminant. -/
def Regular (κ : ℝ) (p : L2T L × ℂ) : Prop :=
  p.2.im ≠ 0 ∨ |(L2SpatialTransfer.discriminant κ p.1 p.2).re| < 2

lemma isOpen_regular (κ : ℝ) : IsOpen {p : L2T L × ℂ | Regular κ p} := by
  have hc : Continuous (fun p : L2T L × ℂ => L2SpatialTransfer.discriminant κ p.1 p.2) :=
    continuous_iff_continuousAt.mpr fun p =>
      (DEF014DiscriminantAnalytic.analyticAt_discriminant_joint κ p).continuousAt
  exact (isOpen_ne.preimage (Complex.continuous_im.comp continuous_snd)).union
    (isOpen_lt (Complex.continuous_re.comp hc).abs continuous_const)

lemma away_nonreal (hκ : 0 < κ) (u : L2T L) {z : ℂ} (hz : z.im ≠ 0) : Away hκ u z := by
  refine ⟨|z.im|,abs_pos.mpr hz,Filter.Eventually.of_forall fun v => ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  simpa using Complex.abs_im_le_norm (z-(t : ℂ))

lemma away_band (hκ : 0 < κ) (u : L2T L) (x : ℝ)
    (hx : |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2) : Away hκ u (x : ℂ) := by
  obtain ⟨δ,hδ,hb⟩ := DEF014Phase.common_band ((⟨κ,hκ⟩,u) : DEF014Phase.Param L) hx
  have hj : Continuous (fun v : L2T L => ((⟨κ,hκ⟩,v) : DEF014Phase.Param L)) :=
    continuous_const.prodMk continuous_id
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hj.continuousAt.eventually hb] with v hv
  have hz : PhysicalQuantumMeasure.measure hκ v (Metric.ball x δ) = 0 := by
    apply DEF014Phase.measure_band_zero ((⟨κ,hκ⟩,v) : DEF014Phase.Param L) Metric.isOpen_ball.measurableSet
    intro t ht
    exact (hv t (by simpa [Metric.mem_ball,Real.dist_eq] using ht)).le
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with t ht
  simpa [Metric.mem_ball,Real.dist_eq,not_lt,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] using ht

lemma away_regular (hκ : 0 < κ) (p : L2T L × ℂ) (hp : Regular κ p) : Away hκ p.1 p.2 := by
  rcases hp with hp | hp
  · exact away_nonreal hκ p.1 hp
  · by_cases hi : p.2.im = 0
    · have he : p.2 = (p.2.re : ℂ) := by apply Complex.ext <;> simp [hi]
      rw [he] at hp ⊢
      exact away_band hκ p.1 p.2.re hp
    · exact away_nonreal hκ p.1 hi

/-- Local spectral Lipschitz bounds and field continuity imply joint
continuity, with an explicit finite-mass majorant. -/
lemma continuousAt_joint_of_away (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (ha : Away hκ u z) (hc : ContinuousAt (G hκ z) u) :
    ContinuousAt (fun p : L2T L × ℂ => G hκ p.2 p.1) (u,z) := by
  obtain ⟨δ,hδ,hgap⟩ := ha
  have hsep : ∀ᶠ p : L2T L × ℂ in 𝓝 (u,z), ‖p.2-z‖ < δ/2 := by
    exact ((continuous_snd.sub continuous_const).norm.continuousAt.eventually
      (gt_mem_nhds (by simpa using (half_pos hδ))))
  have hgp := (continuous_fst.continuousAt (x := (u,z))).eventually hgap
  have hm : ∀ᶠ p : L2T L × ℂ in 𝓝 (u,z), ‖p.1‖^2 < ‖u‖^2+1 := by
    exact (continuous_fst.norm.pow 2).continuousAt.eventually
      (gt_mem_nhds (by linarith : ‖u‖^2 < ‖u‖^2+1))
  have hb : ∀ᶠ p : L2T L × ℂ in 𝓝 (u,z),
      ‖G hκ p.2 p.1-G hκ z p.1‖ ≤ (‖u‖^2+1) * (δ/2)⁻¹^2 * ‖p.2-z‖ := by
    filter_upwards [hsep,hgp,hm] with p hp hpt hpm
    have h1 : ∀ᵐ t : ℝ ∂(PhysicalQuantumMeasure.measure hκ p.1), δ/2 ≤ ‖p.2-(t : ℂ)‖ := by
      filter_upwards [hpt] with t ht
      have hh := norm_add_le (z-p.2) (p.2-(t : ℂ))
      rw [sub_add_sub_cancel, norm_sub_rev z p.2] at hh
      linarith
    have h2 : ∀ᵐ t : ℝ ∂(PhysicalQuantumMeasure.measure hκ p.1), δ/2 ≤ ‖z-(t : ℂ)‖ :=
      hpt.mono fun t ht => (by linarith)
    have hh := DEF014Contour.norm_cauchy_sub_le (PhysicalQuantumMeasure.measure hκ p.1)
      (half_pos hδ) h1 h2
    refine hh.trans ?_
    rw [PhysicalQuantumMeasure.full_mass]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpm.le (sq_nonneg _)) (norm_nonneg _)
  have ht : Tendsto (fun p : L2T L × ℂ => G hκ p.2 p.1-G hκ z p.1) (𝓝 (u,z)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall fun p => norm_nonneg _) hb
    have hh : Continuous (fun p : L2T L × ℂ => (‖u‖^2+1) * (δ/2)⁻¹^2 * ‖p.2-z‖) := by fun_prop
    simpa using hh.tendsto (u,z)
  have hh := ht.add (hc.tendsto.comp continuous_fst.continuousAt.tendsto)
  change Tendsto (fun p : L2T L × ℂ => G hκ p.2 p.1) (𝓝 (u,z)) (𝓝 (G hκ z u))
  simpa using hh

lemma G_conj (hκ : 0 < κ) (z : ℂ) :
    G (L := L) hκ (conj z) = fun v => conj (G hκ z v) := by
  funext v
  exact DEF014ContourReflection.cauchy_conj _ z

lemma analyticAt_lower (hκ : 0 < κ) (u : L2T L) {z : ℂ} (hz : z.im < 0) :
    AnalyticAt ℝ (G hκ z) u := by
  have ha := DEF014PhaseAnalytic.analyticAt_cauchy_upper hκ u
    (z := conj z) (by simpa using neg_pos.mpr hz)
  have hc := (Complex.conjCLE.toContinuousLinearMap.analyticAt (G hκ (conj z) u)).comp ha
  convert hc using 1
  funext v
  change G hκ z v = conj (G hκ (conj z) v)
  simpa only [G,starRingEnd_self_apply] using
    DEF014ContourReflection.cauchy_conj (PhysicalQuantumMeasure.measure hκ v) (conj z)

lemma continuousAt_joint_regular (hκ : 0 < κ) (p : L2T L × ℂ) (hp : Regular κ p) :
    ContinuousAt (fun q : L2T L × ℂ => G hκ q.2 q.1) p := by
  apply continuousAt_joint_of_away hκ p.1 p.2 (away_regular hκ p hp)
  rcases lt_trichotomy p.2.im 0 with hz | hz | hz
  · exact (analyticAt_lower hκ p.1 hz).continuousAt
  · have he : p.2 = (p.2.re : ℂ) := by apply Complex.ext <;> simp [hz]
    have hb : |(L2SpatialTransfer.discriminant κ p.1 (p.2.re : ℂ)).re| < 2 := by
      rcases hp with hp | hp
      · exact (hp hz).elim
      · rw [← he]; exact hp
    rw [he]
    exact DEF014UpperAnalytic.continuousAt_cauchy_band hκ p.1 hb
  · exact (DEF014PhaseAnalytic.analyticAt_cauchy_upper hκ p.1 hz).continuousAt


lemma selected_conj (hκ : 0 < κ) (u : L2T L) (z : ℂ) :
    DEF014PhaseAnalytic.selected hκ u (conj z) =
      conj (DEF014PhaseAnalytic.selected hκ u z) := by
  simp only [DEF014PhaseAnalytic.selected,SpatialTransfer.boundaryPhase,
    DEF014ContourReflection.cauchy_conj,map_sub,map_div₀,map_mul,Complex.conj_ofReal]
  rw [map_ofNat _ 2]

/-- Schwarz reflection for the actual entire physical trace, proved from
its reality on the real axis. -/
lemma discriminant_conj (κ : ℝ) (u : L2T L) (z : ℂ) :
    L2SpatialTransfer.discriminant κ u (conj z) =
      conj (L2SpatialTransfer.discriminant κ u z) := by
  let f := L2SpatialTransfer.discriminant κ u
  have hf : AnalyticOnNhd ℂ f univ :=
    (PhysicalUpperTraceIdentity.entire_discriminant κ u).differentiableOn.analyticOnNhd isOpen_univ
  have hg : AnalyticOnNhd ℂ (fun w => conj (f (conj w))) univ := by
    have hd : Differentiable ℂ (fun w => conj (f (conj w))) := by
      intro w
      convert! (PhysicalUpperTraceIdentity.entire_discriminant κ u (conj w)).conj_conj using 1
      exact (starRingEnd_self_apply w).symm
    exact hd.differentiableOn.analyticOnNhd isOpen_univ
  have hr (x : ℝ) : f (x : ℂ) = conj (f (conj (x : ℂ))) := by
    apply Complex.ext
    · simp
    · simp [f,L2DiscriminantRegularity.discriminant_real]
  have hcl : (0 : ℂ) ∈ closure ({w : ℂ | f w = conj (f (conj w))} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨(ε/2 : ℝ),⟨hr _,?_⟩,?_⟩
    · simp only [mem_singleton_iff,Complex.ofReal_eq_zero]
      linarith
    · simp [dist_eq_norm,Complex.norm_real,abs_of_pos hε]
      linarith
  have he := hf.eqOn_of_preconnected_of_mem_closure hg isPreconnected_univ
    (mem_univ (0 : ℂ)) hcl (mem_univ z)
  have hh := congrArg conj he
  simpa [f] using hh.symm

lemma cosine_regular (hκ : 0 < κ) (p : L2T L × ℂ) (hp : Regular κ p) :
    2 * Complex.cos (DEF014PhaseAnalytic.selected hκ p.1 p.2) =
      L2SpatialTransfer.discriminant κ p.1 p.2 := by
  rcases lt_trichotomy p.2.im 0 with hz | hz | hz
  · have hu : 2 * Complex.cos (DEF014PhaseAnalytic.selected hκ p.1 (conj p.2)) =
        L2SpatialTransfer.discriminant κ p.1 (conj p.2) :=
      PhysicalUnconditionalTrace.upper_cosine hκ p.1 (by simpa using neg_pos.mpr hz)
    have he := congrArg conj hu
    have htwo : conj (2 : ℂ) = 2 := map_ofNat _ 2
    simpa only [map_mul,htwo,← Complex.cos_conj,← selected_conj,
      starRingEnd_self_apply,discriminant_conj] using he
  · have he : p.2 = (p.2.re : ℂ) := by apply Complex.ext <;> simp [hz]
    have hb : |(L2SpatialTransfer.discriminant κ p.1 (p.2.re : ℂ)).re| < 2 := by
      have hh := hp.resolve_left (fun hn => hn hz)
      rw [← he]
      exact hh
    rw [he]
    rw [DEF014UpperAnalytic.selected_real_eq hκ p.1 hb]
    have hcos := PhysicalContinuousBoundary.boundary_cosine hκ p.1 p.2.re
    have hbnd : PhysicalContinuousBoundary.boundary hκ p.1 p.2.re =
        (DEF014Phase.phase (⟨κ,hκ⟩,p.1) p.2.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simp only [Complex.ofReal_im]
        rw [PhysicalContinuousBoundary.boundary_im]
        simp [RootDensity.hfun,not_lt.mpr hb.le]
    rwa [hbnd] at hcos
  · exact PhysicalUnconditionalTrace.upper_cosine hκ p.1 hz

lemma sine_regular (hκ : 0 < κ) (p : L2T L × ℂ) (hp : Regular κ p) :
    Complex.sin (DEF014PhaseAnalytic.selected hκ p.1 p.2) ≠ 0 := by
  intro hs
  rcases lt_trichotomy p.2.im 0 with hz | hz | hz
  · have hp' := PhysicalQuantumMeasure.im_phase_pos hκ p.1
      (z := conj p.2) (by simpa using neg_pos.mpr hz)
    have hh : Complex.sin (DEF014PhaseAnalytic.selected hκ p.1 (conj p.2)) = 0 := by
      rw [selected_conj,Complex.sin_conj,hs,map_zero]
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hh
    have hi := congrArg Complex.im hk
    simp at hi
    change 0 < (DEF014PhaseAnalytic.selected hκ p.1 (conj p.2)).im at hp'
    linarith
  · have he := cosine_regular hκ p hp
    have hb : |(L2SpatialTransfer.discriminant κ p.1 p.2).re| < 2 := hp.resolve_left (by simp [hz])
    rcases Complex.sin_eq_zero_iff_cos_eq.mp hs with hc | hc
    all_goals
      rw [hc] at he
      have hr := congrArg Complex.re he
      norm_num at hr
      rw [← hr] at hb
      norm_num at hb
  · have hp' := PhysicalQuantumMeasure.im_phase_pos hκ p.1 hz
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hs
    have hi := congrArg Complex.im hk
    simp at hi
    change 0 < (DEF014PhaseAnalytic.selected hκ p.1 p.2).im at hp'
    linarith

/-- Joint analyticity across real band crossings on the full real Hilbert
space times the spectral plane. This is the literal selected Cauchy branch. -/
theorem analyticAt_joint_regular (hκ : 0 < κ) (p : L2T L × ℂ) (hp : Regular κ p) :
    AnalyticAt ℝ (fun q : L2T L × ℂ => G hκ q.2 q.1) p := by
  have hg : ContinuousAt (fun q : L2T L × ℂ => DEF014PhaseAnalytic.selected hκ q.1 q.2) p :=
    by
      change ContinuousAt (fun q : L2T L × ℂ =>
        (L : ℂ)*q.2/2-(κ : ℂ)*G hκ q.2 q.1) p
      exact ((continuous_const.mul continuous_snd).div_const 2).continuousAt.sub
        ((continuousAt_joint_regular hκ p hp).const_mul (κ : ℂ))
  have he : ∀ᶠ q : L2T L × ℂ in 𝓝 p,
      2 * Complex.cos (DEF014PhaseAnalytic.selected hκ q.1 q.2) =
        L2SpatialTransfer.discriminant κ q.1 q.2 :=
    Filter.Eventually.mono ((isOpen_regular κ).mem_nhds hp) (fun q hq => cosine_regular hκ q hq)
  have ha := DEF014PhaseAnalytic.analytic_selected_cosine
    (DEF014DiscriminantAnalytic.analyticAt_discriminant_joint κ p) hg he (sine_regular hκ p hp)
  have hh := (((analyticAt_const (v := (L : ℂ))).mul analyticAt_snd).div
    (analyticAt_const (v := (2 : ℂ))) (by norm_num)).sub ha
  have hc := hh.div (analyticAt_const (v := (κ : ℂ))) (Complex.ofReal_ne_zero.mpr hκ.ne')
  convert hc using 1
  funext q
  dsimp [DEF014PhaseAnalytic.selected,SpatialTransfer.boundaryPhase,G]
  field_simp [Complex.ofReal_ne_zero.mpr hκ.ne']
  ring


/-- Complex differentiability of a finite Cauchy integral with a positive
almost-everywhere support distance. The dominated derivative has an explicit
constant majorant; no product integral or Fubini exchange is used. -/
theorem hasDerivAt_cauchy_away (M : Measure ℝ) [IsFiniteMeasure M]
    {z₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) (ha : ∀ᵐ (t : ℝ) ∂M, δ ≤ ‖z₀ - (t : ℂ)‖) :
    HasDerivAt (EmpiricalRapidity.cauchyTransform M)
      (∫ t : ℝ, -((z₀ - (t : ℂ))⁻¹ ^ 2) ∂M) z₀ := by
  let S : Set ℂ := Metric.ball z₀ (δ / 2)
  let F : ℂ → ℝ → ℂ := fun z t => (z - (t : ℂ))⁻¹
  let D : ℂ → ℝ → ℂ := fun z t => -((z - (t : ℂ))⁻¹ ^ 2)
  have hs : S ∈ 𝓝 z₀ := Metric.ball_mem_nhds _ (by positivity)
  have hb : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, δ / 2 ≤ ‖z - (t : ℂ)‖ := by
    filter_upwards [ha] with t ht z hz
    have hnorm : δ ≤ ‖z₀ - (t : ℂ)‖ := by
      exact ht
    have hz' : ‖z₀ - z‖ < δ / 2 := by
      simpa [S, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
    have ht := norm_add_le (z₀ - z) (z - (t : ℂ))
    rw [sub_add_sub_cancel] at ht
    linarith
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) M := by
    exact ((measurable_const.sub Complex.measurable_ofReal).inv).aestronglyMeasurable
  have hnorm : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, ‖F z t‖ ≤ (δ / 2)⁻¹ := by
    filter_upwards [hb] with t ht z hz
    exact (norm_inv _).trans_le (inv_anti₀ (by positivity) (ht z hz))
  have hxS : z₀ ∈ S := Metric.mem_ball_self (by positivity)
  have hi : Integrable (F z₀) M :=
    (integrable_const ((δ / 2)⁻¹)).mono' (hmeas _) (hnorm.mono (fun t ht => ht _ hxS))
  have hmD : AEStronglyMeasurable (D z₀) M := (hmeas _).pow 2 |>.neg
  have hbd : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, ‖D z t‖ ≤ (δ / 2)⁻¹ ^ 2 := by
    filter_upwards [hnorm] with t ht z hz
    simpa [D, F] using pow_le_pow_left₀ (norm_nonneg (F z t)) (ht z hz) 2
  have hd : ∀ᵐ (t : ℝ) ∂M, ∀ z ∈ S, HasDerivAt (fun w => F w t) (D z t) z := by
    filter_upwards [hb] with t ht z hz
    have hn : z - (t : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (ht z hz))
    exact (((hasDerivAt_id z).sub_const (t : ℂ)).inv hn).congr_deriv
      (by simp [D, div_eq_mul_inv, inv_pow])
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall hmeas) hi hmD hbd (integrable_const _) hd).2


lemma differentiableAt_spectral_regular (hκ : 0 < κ) (p : L2T L × ℂ) (hp : Regular κ p) :
    DifferentiableAt ℂ (fun w => G hκ w p.1) p.2 := by
  obtain ⟨δ,hδ,hg⟩ := away_regular hκ p hp
  exact (hasDerivAt_cauchy_away (PhysicalQuantumMeasure.measure hκ p.1) (z₀ := p.2) hδ
    (Filter.Eventually.self_of_nhds (x := p.1) hg)).differentiableAt

/-- Full bounded field differentials depend holomorphically on the spectral
parameter through both half-planes AND every real open-band crossing. -/
theorem analyticAt_field_differential (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hp : Regular κ (u,z)) :
    AnalyticAt ℂ (fun w => fderiv ℝ (G hκ w) u) z := by
  let F : L2T L × ℂ → ℂ := fun p => G hκ p.2 p.1
  have ha := analyticAt_joint_regular hκ (u,z) hp
  have he : ∀ᶠ p : L2T L × ℂ in 𝓝 (u,z),
      DifferentiableAt ℂ (fun w => F (p.1,w)) p.2 :=
    Filter.Eventually.mono ((isOpen_regular κ).mem_nhds hp) fun p hq => differentiableAt_spectral_regular hκ p hq
  have hc := RootSpectralCovectorR9.analyticAt_fieldCovector ha he
  apply hc.congr
  have hj : Continuous (fun w : ℂ => (u,w)) := continuous_const.prodMk continuous_id
  filter_upwards [hj.continuousAt.eventually ((isOpen_regular κ).mem_nhds hp)] with w hw
  exact RootSpectralCovectorR9.fieldCovector_eq F (u,w)
    (analyticAt_joint_regular hκ (u,w) hw).differentiableAt

end QuantumNLS.RootCauchyJointR9

-- Source component: RootBracketCovectorR9

/-! The actual Poisson bracket as a bounded complex-linear evaluation of
the first field covector, with its second functional fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Topology ComplexConjugate
namespace QuantumNLS.RootBracketCovectorR9
open SymplecticBracket
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Evaluation is complex linear on complex-valued real covectors. -/
def eval (h : H) : (H →L[ℝ] ℂ) →L[ℂ] ℂ :=
  ({ toFun := fun α => α h
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : (H →L[ℝ] ℂ) →ₗ[ℂ] ℂ).mkContinuous ‖h‖
    (fun α => by simpa [mul_comm] using α.le_opNorm h)

/-- The second functional supplies fixed full Hamiltonian directions.
No gradient projection or restriction to a mass sphere occurs. -/
def bracketEval (K : H → ℂ) (u : H) : (H →L[ℝ] ℂ) →L[ℂ] ℂ :=
  eval (hamField (fun v => (K v).re) u) +
    Complex.I • eval (hamField (fun v => (K v).im) u)

theorem bracketEval_fderiv (F K : H → ℂ) (u : H) (hF : DifferentiableAt ℝ F u) :
    bracketEval K u (fderiv ℝ F u) = pbC F K u := by
  have hre : fderiv ℝ (fun v => (F v).re) u = Complex.reCLM.comp (fderiv ℝ F u) :=
    (Complex.reCLM.hasFDerivAt.comp u hF.hasFDerivAt).fderiv
  have him : fderiv ℝ (fun v => (F v).im) u = Complex.imCLM.comp (fderiv ℝ F u) :=
    (Complex.imCLM.hasFDerivAt.comp u hF.hasFDerivAt).fderiv
  unfold bracketEval eval pbC pbR
  apply Complex.ext <;> simp [hre,him,Complex.mul_re,Complex.mul_im,sub_eq_add_neg]

/-- Operator-norm covector analyticity suffices for each separate
spectral bracket, without identifying derivatives only pointwise. -/
theorem analyticAt_bracket {F : ℂ → H → ℂ} {K : H → ℂ} {u : H} {z : ℂ}
    (ha : AnalyticAt ℂ (fun w => fderiv ℝ (F w) u) z)
    (hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (F w) u) :
    AnalyticAt ℂ (fun w => pbC (F w) K u) z := by
  apply ((bracketEval K u).analyticAt _ |>.comp ha).congr
  exact hd.mono fun w hw => bracketEval_fderiv (F w) K u hw

end QuantumNLS.RootBracketCovectorR9

namespace QuantumNLS.RootBracketCovectorR9
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 SymplecticBracket
variable {L κ : ℝ} [Fact (0 < L)]

/-- Spectral holomorphy of the first bracket parameter, including across
real band crossings. The second functional is arbitrary and fixed. -/
theorem analyticAt_bracket_G (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hp : Regular κ (u,z)) (K : L2T L → ℂ) :
    AnalyticAt ℂ (fun w => pbC (G hκ w) K u) z := by
  apply analyticAt_bracket (analyticAt_field_differential hκ u z hp)
  have hj : Continuous (fun w : ℂ => (u,w)) := continuous_const.prodMk continuous_id
  filter_upwards [hj.continuousAt.eventually ((isOpen_regular κ).mem_nhds hp)] with w hw
  have ha := analyticAt_joint_regular hκ (u,w) hw
  exact (ha.comp (f := fun v : L2T L => (v,w))
    (analyticAt_id.prod analyticAt_const)).differentiableAt

/-- Separate holomorphy in the second parameter follows from the actual
skew symmetry of the full complex bracket. -/
theorem analyticAt_bracket_G_right (hκ : 0 < κ) (u : L2T L) (z w : ℂ)
    (hp : Regular κ (u,w)) :
    AnalyticAt ℂ (fun t => pbC (G hκ z) (G hκ t) u) w := by
  have ha := (analyticAt_bracket_G hκ u w hp (G hκ z)).neg
  convert ha using 1
  funext t
  exact RootGBracket.pbC_swap _ _ _
end QuantumNLS.RootBracketCovectorR9

-- Source component: RootBracketContinuationR9

/-! Identity-theorem continuation of the proved high-parameter full-space
Cauchy brackets. No zero bracket is assumed as a physical hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Topology ComplexConjugate
namespace QuantumNLS.RootBracketContinuationR9
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 RootCauchyJointR9
open RootBracketCovectorR9 SymplecticBracket

/-- Identity continuation on either half-plane from the indicated high
open region. This is a scalar analysis lemma. -/
lemma continue_half {f : ℂ → ℂ} {L a b s : ℝ} (hL : 0 < L)
    (hs : s = 1 ∨ s = -1)
    (hf : AnalyticOnNhd ℂ f {z | 0 < s*z.im})
    (hzero : ∀ z : ℂ, a ≤ s*z.im → b ≤ L*(s*z.im) → f z = 0) :
    ∀ z : ℂ, 0 < s*z.im → f z = 0 := by
  have hs2 : s*s = 1 := by rcases hs with rfl | rfl <;> norm_num
  let y : ℝ := max (max a (b/L)) 0 + 1
  let z₀ : ℂ := ⟨0,s*y⟩
  have he : s*z₀.im = y := by change s*(s*y)=y; rw [← mul_assoc,hs2,one_mul]
  have hy : 0 < y := by dsimp [y]; linarith [le_max_right (max a (b/L)) 0]
  have hya : a < y := by
    dsimp [y]; linarith [le_max_left a (b/L),le_max_left (max a (b/L)) 0]
  have hyb : b < L*y := by
    have hh : b/L < y := by
      dsimp [y]; linarith [le_max_right a (b/L),le_max_left (max a (b/L)) 0]
    have hh' := (div_lt_iff₀ hL).mp hh
    nlinarith
  have hconn : IsPreconnected {z : ℂ | 0 < s*z.im} :=
    ((convex_Ioi (0 : ℝ)).linear_preimage (s • Complex.imLm)).isPreconnected
  have hnh : f =ᶠ[𝓝 z₀] (fun _ => (0 : ℂ)) := by
    have h1 : ∀ᶠ w : ℂ in 𝓝 z₀, a < s*w.im :=
      (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).mem_nhds (by change a < s*z₀.im; rwa [he])
    have h2 : ∀ᶠ w : ℂ in 𝓝 z₀, b < L*(s*w.im) :=
      (isOpen_lt continuous_const (continuous_const.mul (continuous_const.mul Complex.continuous_im))).mem_nhds
        (by change b < L*(s*z₀.im); rwa [he])
    filter_upwards [h1,h2] with w hw1 hw2
    exact hzero w hw1.le hw2.le
  exact hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn
    (by change 0 < s*z₀.im; rwa [he]) hnh

variable {L κ : ℝ} [Fact (0 < L)]

lemma pbC_conj_conj (F K : L2T L → ℂ) (u : L2T L) :
    pbC (fun v => conj (F v)) (fun v => conj (K v)) u = conj (pbC F K u) := by
  unfold pbC
  simp only [Complex.conj_re,Complex.conj_im]
  rw [pbR_neg_left,pbR_neg_right,pbR_neg_right,pbR_neg_left]
  apply Complex.ext
  · simp
  · simp
    ring

/-- The high upper seed in the first parameter is continued in the second
parameter to either half-plane. -/
lemma high_upper_nonreal (hκ : 0 < κ) (u : L2T L) (z w : ℂ)
    (hz4 : 4*(κ*‖u‖^2) ≤ z.im) (hzL : Real.log 16 ≤ L*z.im)
    (hw : w.im ≠ 0) : pbC (G hκ z) (G hκ w) u = 0 := by
  have hL : 0 < L := Fact.out
  by_cases hwpos : 0 < w.im
  · apply continue_half hL (s := 1) (Or.inl rfl)
      (a := 4*(κ*‖u‖^2)) (b := Real.log 16)
      (f := fun t => pbC (G hκ z) (G hκ t) u) ?_ ?_ w (by simpa using hwpos)
    · intro t ht
      apply analyticAt_bracket_G_right hκ u z t
      exact Or.inl (ne_of_gt (by simpa only [mem_ofPred_eq,one_mul] using ht))
    · intro t ht4 htL
      exact (G_full_high_bracket_zero hκ z t u hz4 hzL
        (by simpa using ht4) (by simpa using htL)).1
  · have hwneg : w.im < 0 := lt_of_le_of_ne (le_of_not_gt hwpos) hw
    apply continue_half hL (s := -1) (Or.inr rfl)
      (a := 4*(κ*‖u‖^2)) (b := Real.log 16)
      (f := fun t => pbC (G hκ z) (G hκ t) u) ?_ ?_ w (by simpa using hwneg)
    · intro t ht
      apply analyticAt_bracket_G_right hκ u z t
      left
      change t.im ≠ 0
      intro he
      have ht' : 0 < (-1 : ℝ)*t.im := ht
      rw [he] at ht'
      norm_num at ht' 
    · intro t ht4 htL
      have he : G (L := L) hκ t = fun v => conj (G hκ (conj t) v) := by
        simpa only [starRingEnd_self_apply] using G_conj hκ (conj t)
      rw [he]
      exact (G_full_high_bracket_zero hκ z (conj t) u hz4 hzL
        (by simpa using ht4) (by simpa using htL)).2

/-- Full upper/upper and upper/lower continuation, with no high spectral
inequality remaining in the statement. -/
theorem upper_nonreal_bracket (hκ : 0 < κ) (u : L2T L) (z w : ℂ)
    (hz : 0 < z.im) (hw : w.im ≠ 0) : pbC (G hκ z) (G hκ w) u = 0 := by
  apply continue_half (Fact.out : 0 < L) (s := 1) (Or.inl rfl)
    (a := 4*(κ*‖u‖^2)) (b := Real.log 16)
    (f := fun t => pbC (G hκ t) (G hκ w) u) ?_ ?_ z (by simpa using hz)
  · intro t ht
    exact analyticAt_bracket_G hκ u t (Or.inl (ne_of_gt (by simpa only [mem_ofPred_eq,one_mul] using ht))) (G hκ w)
  · intro t ht4 htL
    exact high_upper_nonreal hκ u t w (by simpa using ht4) (by simpa using htL) hw

/-- All four nonreal half-plane pairs for arbitrary physical L2 input. -/
theorem nonreal_bracket (hκ : 0 < κ) (u : L2T L) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) : pbC (G hκ z) (G hκ w) u = 0 := by
  by_cases hzpos : 0 < z.im
  · exact upper_nonreal_bracket hκ u z w hzpos hw
  · have hzneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hzpos) hz
    by_cases hwpos : 0 < w.im
    · rw [RootGBracket.pbC_swap (G hκ z) (G hκ w) u,
        upper_nonreal_bracket hκ u w z hwpos hz,neg_zero]
    · have hwneg : w.im < 0 := lt_of_le_of_ne (le_of_not_gt hwpos) hw
      have hez : G (L := L) hκ z = fun v => conj (G hκ (conj z) v) := by
        simpa only [starRingEnd_self_apply] using G_conj hκ (conj z)
      have hew : G (L := L) hκ w = fun v => conj (G hκ (conj w) v) := by
        simpa only [starRingEnd_self_apply] using G_conj hκ (conj w)
      rw [hez,hew,pbC_conj_conj,
        upper_nonreal_bracket hκ u (conj z) (conj w)
          (by simpa using neg_pos.mpr hzneg) (by simpa using hw),map_zero]


lemma continuous_zero_of_nonreal {f : ℂ → ℂ} {z : ℂ} (hc : ContinuousAt f z)
    (hz : ∀ w : ℂ, w.im ≠ 0 → f w = 0) : f z = 0 := by
  by_cases hi : z.im ≠ 0
  · exact hz z hi
  · have hi0 : z.im = 0 := not_ne_iff.mp hi
    let a : ℕ → ℂ := fun n => z + ((1 / ((n : ℝ)+1) : ℝ) : ℂ)*Complex.I
    have ha : Tendsto a atTop (𝓝 z) := by
      have ht := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0))
      simpa [a] using tendsto_const_nhds.add (ht.mul_const Complex.I)
    have he : ∀ n : ℕ, f (a n) = 0 := by
      intro n
      apply hz
      have him : (a n).im = 1/((n : ℝ)+1) := by
        change z.im + (((1/((n : ℝ)+1) : ℝ) : ℂ) * Complex.I).im = _
        rw [hi0]
        simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
          Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero,zero_add]
      rw [him]
      exact ne_of_gt (by positivity : (0 : ℝ) < 1/((n : ℝ)+1))
    have hh := hc.tendsto.comp ha
    have heq : (fun n => f (a n)) = (fun _ : ℕ => (0 : ℂ)) := funext he
    change Tendsto (fun n => f (a n)) atTop (𝓝 (f z)) at hh
    rw [heq] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds

/-- The differential extension through bands transports the zero pairing
to all regular contour points, including the literal real crossings. -/
theorem regular_bracket (hκ : 0 < κ) (u : L2T L) (z w : ℂ)
    (hz : Regular κ (u,z)) (hw : Regular κ (u,w)) :
    pbC (G hκ z) (G hκ w) u = 0 := by
  have hfirst : ∀ t : ℂ, t.im ≠ 0 → pbC (G hκ z) (G hκ t) u = 0 := by
    intro t ht
    apply continuous_zero_of_nonreal (analyticAt_bracket_G hκ u z hz (G hκ t)).continuousAt
    intro s hs
    exact nonreal_bracket hκ u s t hs ht
  apply continuous_zero_of_nonreal (analyticAt_bracket_G_right hκ u z w hw).continuousAt
  exact hfirst

lemma regular_conj (u : L2T L) (w : ℂ) (hw : Regular κ (u,w)) :
    Regular κ (u,conj w) := by
  rcases hw with hw | hw
  · left
    simpa using hw
  · right
    simpa only [discriminant_conj,Complex.conj_re] using hw

lemma regular_bracket_conj (hκ : 0 < κ) (u : L2T L) (z w : ℂ)
    (hz : Regular κ (u,z)) (hw : Regular κ (u,w)) :
    pbC (G hκ z) (fun v => conj (G hκ w v)) u = 0 := by
  have hh := regular_bracket hκ u z (conj w) hz (regular_conj u w hw)
  rwa [G_conj] at hh

/-- Every real component pairing vanishes; both complex and conjugate
brackets are used, so no real component cancellation is assumed. -/
theorem regular_component_brackets (hκ : 0 < κ) (u : L2T L) (z w : ℂ)
    (hz : Regular κ (u,z)) (hw : Regular κ (u,w)) :
    pbR (fun v => (G hκ z v).re) (fun v => (G hκ w v).re) u = 0 ∧
    pbR (fun v => (G hκ z v).re) (fun v => (G hκ w v).im) u = 0 ∧
    pbR (fun v => (G hκ z v).im) (fun v => (G hκ w v).re) u = 0 ∧
    pbR (fun v => (G hκ z v).im) (fun v => (G hκ w v).im) u = 0 := by
  have h0 := regular_bracket hκ u z w hz hw
  have hc := regular_bracket_conj hκ u z w hz hw
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  have h3 := congrArg Complex.re hc
  have h4 := congrArg Complex.im hc
  dsimp only [pbC] at h1 h2 h3 h4
  simp only [Complex.zero_re,Complex.zero_im] at h1 h2 h3 h4
  simp only [Complex.conj_re,Complex.conj_im,pbR_neg_right] at h3 h4
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩
end QuantumNLS.RootBracketContinuationR9

-- Source component: RootMassDifferentialR9

/-! Differentiating the inherited fixed mass contour using its existing
uniform Cauchy germ. No new contour/measure Fubini contract is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace QuantumNLS.RootMassDifferentialR9
open PhysicalTensor (L2T)
open DEF014MassAnalytic (UpperInterval upperPath)
open RootCauchyFullBracketR8 (G)
open RootMassInvolutionR8 (mass)
open RootCauchyJointR9
variable {L κ : ℝ} [Fact (0 < L)]

/-- A tangent vector annihilated by every regular spectral Cauchy
covector is annihilated by each indexed-mass differential. The contours
and their uniform full-field derivatives are fixed at the given input. -/
theorem mass_differential_kernel (hκ : 0 < κ) (n : ℤ) (u h : L2T L)
    (hker : ∀ z : ℂ, Regular κ (u,z) → fderiv ℝ (G hκ z) u h = 0) :
    fderiv ℝ (mass hκ n) u h = 0 := by
  let p : DEF014Phase.Param L := (⟨κ,hκ⟩,u)
  let j : L2T L → DEF014Phase.Param L := fun v => (⟨κ,hκ⟩,v)
  have hj : Continuous j := continuous_const.prodMk continuous_id
  let a := DEF014Phase.separator p (n-1)
  let b := DEF014Phase.separator p n
  let c := (a+b)/2
  let R := (b-a)/2
  have hab : a < b := (DEF014Phase.facts p).phase.separator_strictMono (by omega)
  have hR : 0 < R := by dsimp [R]; linarith
  let Z := upperPath c R
  have hZ : LipschitzWith (Real.nnabs R) Z := by
    apply LipschitzWith.of_dist_le_mul
    intro θ φ
    change dist (circleMap (c : ℂ) R θ.1) (circleMap (c : ℂ) R φ.1) ≤
      (Real.nnabs R : ℝ) * dist θ.1 φ.1
    exact (lipschitzWith_circleMap (c : ℂ) R).dist_le_mul θ.1 φ.1
  have hupper : ∀ θ, 0 ≤ (Z θ).im := by
    intro θ
    change 0 ≤ (circleMap (c : ℂ) R θ.1).im
    simpa [circleMap,Complex.exp_mul_I,Complex.mul_im,Complex.sin_ofReal_re] using
      mul_nonneg hR.le (Real.sin_nonneg_of_mem_Icc θ.2)
  have hreal : ∀ θ : UpperInterval, (Z θ).im = 0 → (Z θ).re = a ∨ (Z θ).re = b := by
    intro θ hθ
    have him : (Z θ).im = R * Real.sin θ.1 := by
      simp [Z,upperPath,circleMap,Complex.exp_mul_I,Complex.mul_im,Complex.sin_ofReal_re]
    have hs : Real.sin θ.1 = 0 := (mul_eq_zero.mp (him.symm.trans hθ)).resolve_left hR.ne'
    by_cases h0 : θ.1 = 0
    · right
      simp [Z,upperPath,h0,circleMap,c,R]; ring
    · by_cases hπ : θ.1 = Real.pi
      · left
        simp [Z,upperPath,hπ,circleMap,c,R]; ring
      · have hp := Real.sin_pos_of_pos_of_lt_pi
          (lt_of_le_of_ne θ.2.1 (Ne.symm h0)) (lt_of_le_of_ne θ.2.2 hπ)
        exact (hp.ne' hs).elim
  obtain ⟨δ,hδ,hgapP⟩ := DEF014Contour.common_contour_gap p n
  have hgap : ∀ᶠ v : L2T L in 𝓝 u,
      ∀ᵐ (t : ℝ) ∂(PhysicalQuantumMeasure.measure hκ v), ∀ θ : UpperInterval,
        δ ≤ ‖Z θ-(t : ℂ)‖ := by
    filter_upwards [hj.continuousAt.tendsto.eventually hgapP] with v hv
    filter_upwards [hv] with t ht θ
    exact DEF014ContourReflection.circle_support_distance c hR ht θ.1
  let M := (‖u‖+1)^2
  have hM : 0 ≤ M := sq_nonneg _
  have hmass : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ M := by
    have hn : ∀ᶠ v : L2T L in 𝓝 u, ‖v‖ < ‖u‖+1 :=
      continuous_norm.continuousAt.tendsto.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hn] with v hv
    rw [PhysicalQuantumMeasure.measure_univ,ENNReal.toReal_ofReal (sq_nonneg _)]
    dsimp [M]
    nlinarith [norm_nonneg v,norm_nonneg u]
  obtain ⟨δa,hδa,hba⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band (n-1))
  obtain ⟨δb,hδb,hbb⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band n)
  have hband : ∀ᶠ v : L2T L in 𝓝 u, ∀ θ : UpperInterval, (Z θ).im = 0 →
      |(L2SpatialTransfer.discriminant κ v ((Z θ).re : ℂ)).re| < 2 := by
    filter_upwards [hj.continuousAt.tendsto.eventually hba,
      hj.continuousAt.tendsto.eventually hbb] with v hva hvb θ hθ
    rcases hreal θ hθ with he | he
    · rw [he]
      exact hva a (by simpa [a,DEF014Phase.separator] using hδa)
    · rw [he]
      exact hvb b (by simpa [b,DEF014Phase.separator] using hδb)
  obtain ⟨H,hH,hHe⟩ := DEF014UpperAnalytic.exists_analytic_cauchy_path hκ Z hZ u
    hupper hδ hM hgap hmass hband
  let τ : C(DEF014AnalyticIntegration.UnitInterval,UpperInterval) :=
    ⟨fun s => ⟨Real.pi*s.1,by constructor <;> nlinarith [s.2.1,s.2.2,Real.pi_pos]⟩,
      by fun_prop⟩
  let d : C(DEF014AnalyticIntegration.UnitInterval,ℂ) :=
    ⟨fun s => deriv (circleMap (c : ℂ) R) (Real.pi*s.1),by
      simp only [deriv_circleMap]; fun_prop⟩
  let F : L2T L → C(DEF014AnalyticIntegration.UnitInterval,ℂ) :=
    fun v => d * (H v).comp τ
  have hF : AnalyticAt ℝ F u := by
    exact analyticAt_const.mul
      (((ContinuousMap.compCLM (M := ℂ) (R := ℝ) τ).analyticAt _).comp hH)
  have hreg : ∀ θ : UpperInterval, Regular κ (u,Z θ) := by
    intro θ
    by_cases hi : (Z θ).im = 0
    · right
      have hez : Z θ = ((Z θ).re : ℂ) := by apply Complex.ext <;> simp [hi]
      rw [hez]
      exact Filter.Eventually.self_of_nhds hband θ hi
    · exact Or.inl hi
  have hDH : fderiv ℝ H u h = 0 := by
    apply ContinuousMap.ext
    intro θ
    have hd := ((ContinuousMap.evalCLM ℝ θ).hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt)
    have heq : (fun v : L2T L => H v θ) =ᶠ[𝓝 u] G hκ (Z θ) :=
      hHe.mono fun v hv => hv θ
    have hdG := hd.congr_of_eventuallyEq heq.symm
    have hh := congrArg (fun A : L2T L →L[ℝ] ℂ => A h) hdG.fderiv
    have hz := hker (Z θ) (hreg θ)
    simpa using hh.symm.trans hz
  have hDF : fderiv ℝ F u h = 0 := by
    have hcomp := (ContinuousMap.compCLM (M := ℂ) (R := ℝ) τ).hasFDerivAt.comp u
      hH.differentiableAt.hasFDerivAt
    have hd := (hasFDerivAt_const d u).mul hcomp
    change HasFDerivAt F _ u at hd
    rw [hd.fderiv]
    simp [hDH]
  let J : L2T L → ℂ := fun v => (Real.pi : ℂ) * DEF014AnalyticIntegration.integrateCLM (F v)
  have hDJ : fderiv ℝ J u h = 0 := by
    have hd := (DEF014AnalyticIntegration.integrateCLM.hasFDerivAt.comp u
      hF.differentiableAt.hasFDerivAt).const_mul (Real.pi : ℂ)
    change HasFDerivAt J _ u at hd
    rw [hd.fderiv]
    simp [hDF]
  have hJeq : J =ᶠ[𝓝 u] (fun v : L2T L => ∫ θ in (0 : ℝ)..Real.pi,
      DEF014ContourReflection.arcIntegrand (PhysicalQuantumMeasure.measure hκ v) c R θ) := by
    filter_upwards [hHe] with v hv
    have he : (∫ t in (0 : ℝ)..1, DEF014AnalyticIntegration.extend (F v) t) =
        ∫ t in (0 : ℝ)..1, DEF014ContourReflection.arcIntegrand
          (PhysicalQuantumMeasure.measure hκ v) c R (Real.pi*t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      change F v (projIcc 0 1 (by norm_num) t) = _
      rw [projIcc_of_mem (by norm_num) ht]
      change deriv (circleMap (c : ℂ) R) (Real.pi*t) * H v (τ ⟨t,ht⟩) = _
      rw [hv]
      simp [τ,Z,upperPath,DEF014ContourReflection.arcIntegrand]
    change (Real.pi : ℂ) * (∫ t in (0 : ℝ)..1, DEF014AnalyticIntegration.extend (F v) t) = _
    rw [he]
    simpa only [Function.comp_def,← Complex.real_smul,mul_zero,zero_add,add_zero,mul_one] using
      intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
        (DEF014ContourReflection.arcIntegrand (PhysicalQuantumMeasure.measure hκ v) c R) Real.pi 0
  let Q : L2T L → ℝ := fun v => (J v).im / Real.pi
  have hDQ : fderiv ℝ Q u h = 0 := by
    have hJ : DifferentiableAt ℝ J u :=
      (DEF014AnalyticIntegration.integrateCLM.differentiableAt.comp u hF.differentiableAt).const_mul _
    have hd := (Complex.imCLM.hasFDerivAt.comp u hJ.hasFDerivAt).const_mul Real.pi⁻¹
    have hfun : (fun y => Real.pi⁻¹ * Complex.imCLM (J y)) = Q := by
      funext v
      simp only [Q,div_eq_mul_inv,Complex.imCLM_apply,mul_comm]
    dsimp only [Function.comp_def] at hd
    rw [hfun] at hd
    have hdQ := hd
    rw [hdQ.fderiv]
    simp [hDJ]
  have hQeq : (mass hκ n) =ᶠ[𝓝 u] Q := by
    have hcontour := hj.continuousAt.tendsto.eventually (DEF014Contour.eventually_physical_mass_contour p n)
    filter_upwards [hcontour,hj.continuousAt.tendsto.eventually hgapP,hJeq] with v hv hvg hjv
    have hr := DEF014ContourReflection.integral_eq_upper_sub_conj
      (PhysicalQuantumMeasure.measure hκ v) c hR hδ hvg
    change (mass hκ n v : ℂ) = (2*(Real.pi : ℂ)*I)⁻¹ *
      (∮ z in C((c : ℂ),R),G hκ z v) at hv
    unfold G at hv
    rw [hr,DEF014ContourReflection.normalized_sub_conj] at hv
    have hh := congrArg Complex.re hv
    change mass hκ n v = (J v).im/Real.pi
    rw [hjv]
    simpa only [Complex.ofReal_re] using hh
  rw [hQeq.fderiv_eq]
  exact hDQ
end QuantumNLS.RootMassDifferentialR9

-- Source component: RootMassInvolutionR9

/-! R-507DD869: individual mass analyticity and arbitrary indexed pair
involution on the full physical real Hilbert space, with normalization
2 Im inner. No distinctness, positive-mass, smoothness, unit norm or
supplied vanishing-bracket premise is imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Topology ComplexConjugate
namespace QuantumNLS.RootMassInvolutionR9
open PhysicalTensor (L2T)
open RootMassInvolutionR8 (mass)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9
open RootBracketContinuationR9 RootMassDifferentialR9 SymplecticBracket
variable {L κ : ℝ} [Fact (0 < L)]

lemma G_differential_ham_zero (hκ : 0 < κ) (u : L2T L) (z : ℂ)
    (hz : Regular κ (u,z)) (K : L2T L → ℝ)
    (hR : pbR (fun v => (G hκ z v).re) K u = 0)
    (hI : pbR (fun v => (G hκ z v).im) K u = 0) :
    fderiv ℝ (G hκ z) u (hamField K u) = 0 := by
  have hd : DifferentiableAt ℝ (G hκ z) u :=
    ((analyticAt_joint_regular hκ (u,z) hz).comp
      (f := fun v : L2T L => (v,z)) (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hre : fderiv ℝ (fun v => (G hκ z v).re) u = Complex.reCLM.comp (fderiv ℝ (G hκ z) u) :=
    (Complex.reCLM.hasFDerivAt.comp u hd.hasFDerivAt).fderiv
  have him : fderiv ℝ (fun v => (G hκ z v).im) u = Complex.imCLM.comp (fderiv ℝ (G hκ z) u) :=
    (Complex.imCLM.hasFDerivAt.comp u hd.hasFDerivAt).fderiv
  apply Complex.ext
  · unfold pbR at hR
    have hh := DFunLike.congr_fun hre (hamField K u)
    change fderiv ℝ (fun v => (G hκ z v).re) u (hamField K u) = _ at hh
    exact hh.symm.trans hR
  · unfold pbR at hI
    have hh := DFunLike.congr_fun him (hamField K u)
    change fderiv ℝ (fun v => (G hκ z v).im) u (hamField K u) = _ at hh
    exact hh.symm.trans hI

/-- One fixed mass contour can be differentiated against either real
Hamiltonian component of a spectral Cauchy value. -/
theorem mass_bracket_components (hκ : 0 < κ) (u : L2T L) (n : ℤ) (w : ℂ)
    (hw : Regular κ (u,w)) :
    pbR (mass hκ n) (fun v => (G hκ w v).re) u = 0 ∧
    pbR (mass hκ n) (fun v => (G hκ w v).im) u = 0 := by
  constructor
  · apply mass_differential_kernel hκ n u
    intro z hz
    have hh := regular_component_brackets hκ u z w hz hw
    exact G_differential_ham_zero hκ u z hz _ hh.1 hh.2.2.1
  · apply mass_differential_kernel hκ n u
    intro z hz
    have hh := regular_component_brackets hκ u z w hz hw
    exact G_differential_ham_zero hκ u z hz _ hh.2.1 hh.2.2.2

/-- Arbitrary indexed masses commute, including distinct positive masses.
The proof applies the fixed-contour differential kernel twice. -/
theorem indexed_pair_bracket (hκ : 0 < κ) (u : L2T L) (n m : ℤ) :
    pbR (mass hκ n) (mass hκ m) u = 0 := by
  apply mass_differential_kernel hκ n u
  intro z hz
  have hm := mass_bracket_components hκ u m z hz
  apply G_differential_ham_zero hκ u z hz
  · rw [pbR_swap,hm.1,neg_zero]
  · rw [pbR_swap,hm.2,neg_zero]

/-- R-507DD869 `thm:root-mass-involution`, with exactly the printed full
physical phase space and fixed positive period/coupling. -/
theorem root_mass_involution (hκ : 0 < κ) :
    (∀ (n : ℤ) (u : L2T L), AnalyticAt ℝ (mass hκ n) u) ∧
    (∀ (n m : ℤ) (u : L2T L), pbR (mass hκ n) (mass hκ m) u = 0) :=
  ⟨fun n u => DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u,
    fun n m u => indexed_pair_bracket hκ u n m⟩
end QuantumNLS.RootMassInvolutionR9
#print axioms QuantumNLS.RootMassInvolutionR9.root_mass_involution

#print axioms QuantumNLS.RootSpectralCovectorR9.analyticAt_fieldCovector
#print axioms QuantumNLS.RootCauchyJointR9.analyticAt_field_differential
#print axioms QuantumNLS.RootBracketContinuationR9.regular_bracket
#print axioms QuantumNLS.RootMassDifferentialR9.mass_differential_kernel
#check @QuantumNLS.RootMassInvolutionR9.root_mass_involution

set_option maxHeartbeats 24000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if (n.toString.startsWith "QuantumNLS.RootSpectralCovectorR9." ||
        n.toString.startsWith "QuantumNLS.RootCauchyJointR9." ||
        n.toString.startsWith "QuantumNLS.RootBracketCovectorR9." ||
        n.toString.startsWith "QuantumNLS.RootBracketContinuationR9." ||
        n.toString.startsWith "QuantumNLS.RootMassDifferentialR9." ||
        n.toString.startsWith "QuantumNLS.RootMassInvolutionR9.") ||
        n.toString.startsWith "_private.QuantumNLS.RootMassInvolutionBatchR9." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"RootMassInvolutionBatchR9 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
