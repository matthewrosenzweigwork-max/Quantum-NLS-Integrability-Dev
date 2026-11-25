import QuantumNLS.Prop010CutoffExistenceR11
import QuantumNLS.Q07ContourMeasureR16

/-! Cauchy contour transport to the same rectangle used by PROP-010's
frozen norm theorem. The kernel residue computation uses Cauchy-Goursat
on the pole-free domain; finite-measure Fubini then transports the whole
Cauchy period. The differentiated transport is in the uniform norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Set Filter Topology Complex MeasureTheory
open scoped BigOperators
namespace QuantumNLS.Prop010RectangleTransportR17
open PeriodReconstruction PeriodTwoTerm
open LabelExactPeriod (rectIntegral)

def side (a b h : ℝ) (i : Fin 4) (t : ℝ) : ℂ :=
  if i=0 then t+((-h:ℝ):ℂ)*I else if i=1 then t+h*I
  else if i=2 then b+t*I else a+t*I

def lo (a h : ℝ) (i : Fin 4) : ℝ := if i<2 then a else -h
def hi (b h : ℝ) (i : Fin 4) : ℝ := if i<2 then b else h
def coeff (i : Fin 4) : ℂ := if i=0 then 1 else if i=1 then -1 else if i=2 then I else -I

lemma side_mem {a b h : ℝ} (hab : a≤b) (hh : 0≤h) (i : Fin 4) {t : ℝ}
    (ht : t ∈ Icc (lo a h i) (hi b h i)) : side a b h i t ∈ Gam a b h := by
  fin_cases i
  · exact bot_mem hab (by simpa [lo,hi,uIcc_of_le hab] using ht)
  · exact top_mem hab (by simpa [lo,hi,uIcc_of_le hab] using ht)
  · exact right_mem hh (by simpa [lo,hi,uIcc_of_le (by linarith : -h≤h)] using ht)
  · exact left_mem hh (by simpa [lo,hi,uIcc_of_le (by linarith : -h≤h)] using ht)

lemma rect_sum (a b h : ℝ) (F : ℂ → ℂ) :
    rectIntegral F a b h = ∑ i : Fin 4, coeff i*(∫ t in lo a h i..hi b h i,F (side a b h i t)) := by
  simp [Fin.sum_univ_succ,coeff,lo,hi,side,rectIntegral,smul_eq_mul]
  ring

lemma kernel_rectangle {a b h q : ℝ} (hab : a<b) (hh : 0<h)
    (hqa : q≠a) (hqb : q≠b) :
    rectIntegral (fun z => (z-(q:ℂ))⁻¹) a b h =
      (2*(Real.pi:ℂ)*I)*(Ioo a b).indicator (fun _ : ℝ => (1:ℂ)) q := by
  by_cases hq : q ∈ Ioo a b
  · rw [indicator_of_mem hq]
    simpa using Prop018Period.rect_pow_inv hab.le hh.le
      (by simpa using hq.1) (by simpa using hq.2) (by simpa using hh) 0
  · rw [indicator_of_notMem hq,mul_zero]
    have hf : DifferentiableOn ℂ (fun z : ℂ => (z-(q:ℂ))⁻¹) (Icc a b ×ℂ Icc (-h) h) := by
      intro z hz
      have hzq : z≠(q:ℂ) := by
        intro he
        have hr : a≤z.re ∧ z.re≤b := hz.1
        rw [he,ofReal_re] at hr
        have hlt : a<q := lt_of_le_of_ne hr.1 hqa.symm
        have hgt : q<b := lt_of_le_of_ne hr.2 hqb
        exact hq ⟨hlt,hgt⟩
      exact ((differentiableAt_id.sub_const (q:ℂ)).inv (sub_ne_zero.mpr hzq)).differentiableWithinAt
    have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (fun z : ℂ => (z-(q:ℂ))⁻¹) ((a:ℂ)-(h:ℂ)*I) ((b:ℂ)+(h:ℂ)*I)
    have hs : (uIcc (((a:ℂ)-(h:ℂ)*I).re) (((b:ℂ)+(h:ℂ)*I).re) ×ℂ
        uIcc (((a:ℂ)-(h:ℂ)*I).im) (((b:ℂ)+(h:ℂ)*I).im)) =
        (Icc a b ×ℂ Icc (-h) h) := by
      simp [uIcc_of_le hab.le,uIcc_of_le (by linarith : -h≤h)]
    rw [hs] at hc
    simpa [rectIntegral] using hc hf

/-- Arbitrary, possibly unbounded-support finite measures; both endpoint
support gaps are explicit. No target period identity is a premise. -/
theorem rectangle_cauchy (μ : Measure ℝ) [IsFiniteMeasure μ] {a b h δ : ℝ}
    (hab : a<b) (hh : 0<h) (hδ : 0<δ)
    (hg : ∀ᵐ q : ℝ ∂μ,δ≤|q-a| ∧ δ≤|q-b|) :
    rectIntegral (EmpiricalRapidity.cauchyTransform μ) a b h =
      (2*(Real.pi:ℂ)*I)*((μ (Ioo a b)).toReal:ℂ) := by
  have hl : ∀ i : Fin 4,lo a h i≤hi b h i := by
    intro i; fin_cases i <;> simp [lo,hi] <;> linarith
  let K : Fin 4 → ℝ → ℂ := fun i q => ∫ t in lo a h i..hi b h i,(side a b h i t-(q:ℂ))⁻¹
  have hs : ∀ i : Fin 4,
      (∫ t in lo a h i..hi b h i,EmpiricalRapidity.cauchyTransform μ (side a b h i t)) =
        ∫ q,K i q ∂μ ∧ Integrable (K i) μ := by
    intro i
    have hc : Continuous (side a b h i) := by fin_cases i <;> unfold side <;> simp <;> fun_prop
    have hb : ∀ t ∈ Icc (lo a h i) (hi b h i),‖side a b h i t‖≤|a|+|b|+h := by
      intro t ht
      have hz := side_mem hab.le hh.le i ht
      have hr : |(side a b h i t).re|≤|a|+|b| := by
        rcases hz with ⟨hr,-⟩ | ⟨-,hr | hr⟩
        · rw [abs_le]; constructor <;> linarith [hr.1,hr.2,neg_abs_le a,le_abs_self b,abs_nonneg a,abs_nonneg b]
        · rw [hr]; linarith [abs_nonneg b]
        · rw [hr]; linarith [abs_nonneg a]
      exact (norm_le_abs_re_add_abs_im _).trans (add_le_add hr (Gam_abs_im hh hz))
    have hgap : ∀ᵐ q : ℝ ∂μ,∀ t ∈ Icc (lo a h i) (hi b h i),min δ h≤‖side a b h i t-(q:ℂ)‖ := by
      filter_upwards [hg] with q hq t ht
      exact Gam_dist hh hq.1 hq.2 (side_mem hab.le hh.le i ht)
    simpa only [pow_zero,one_mul,K] using
      Q07ContourMeasureR16.side_fubini μ (side a b h i) hc (hl i)
        (by positivity : 0≤|a|+|b|+h) (lt_min hδ hh) 0 hb hgap
  have hswap : rectIntegral (EmpiricalRapidity.cauchyTransform μ) a b h =
      ∫ q,rectIntegral (fun z => (z-(q:ℂ))⁻¹) a b h ∂μ := by
    rw [rect_sum]
    calc
      _ = ∑ i : Fin 4, coeff i*(∫ q,K i q ∂μ) := by
        apply Finset.sum_congr rfl; intro i _; rw [(hs i).1]
      _ = ∫ q,∑ i : Fin 4, coeff i*K i q ∂μ := by
        simp only [← integral_const_mul]
        rw [integral_finsetSum _ (fun i _ => (hs i).2.const_mul _)]
      _ = _ := by apply integral_congr_ae; filter_upwards with q; rw [rect_sum]
  rw [hswap]
  calc
    _ = ∫ q,(2*(Real.pi:ℂ)*I)*(Ioo a b).indicator (fun _ : ℝ => (1:ℂ)) q ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg] with q hq
      apply kernel_rectangle hab hh
      · intro he; subst q; simp at hq; linarith [hq.1]
      · intro he; subst q; simp at hq; linarith [hq.2]
    _ = _ := by rw [integral_const_mul,integral_indicator measurableSet_Ioo]; simp [Measure.real]

open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut center radius)
variable {L κ : ℝ} [Fact (0<L)]

/-- One full real Hilbert neighborhood has uniform endpoint support gaps. -/
theorem endpoint_gaps (hκ : 0<κ) (u : L2T L) (n : ℤ) :
    ∃ δ>0,∀ᶠ v : L2T L in 𝓝 u,∀ᵐ q : ℝ ∂(PhysicalQuantumMeasure.measure hκ v),
      δ≤|q-cut hκ u (n-1)| ∧ δ≤|q-cut hκ u n| := by
  let p : DEF014Phase.Param L := (⟨κ,hκ⟩,u)
  obtain ⟨δa,ha,hba⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band (n-1))
  obtain ⟨δb,hb,hbb⟩ := DEF014Phase.common_band p ((DEF014Phase.facts p).separator_in_band n)
  have hj : Continuous (fun v : L2T L => ((⟨κ,hκ⟩,v):DEF014Phase.Param L)) := continuous_const.prodMk continuous_id
  refine ⟨min δa δb,lt_min ha hb,?_⟩
  filter_upwards [hj.continuousAt.eventually hba,hj.continuousAt.eventually hbb] with v hva hvb
  have hz (a δ : ℝ) (hv : ∀ t : ℝ,|t-a|<δ → |(L2SpatialTransfer.discriminant κ v (t:ℂ)).re| < 2) :
      PhysicalQuantumMeasure.measure hκ v (Metric.ball a δ)=0 := by
    exact DEF014Phase.measure_band_zero ((⟨κ,hκ⟩,v):DEF014Phase.Param L)
      Metric.isOpen_ball.measurableSet (fun t ht => (hv t (by simpa [Metric.mem_ball,Real.dist_eq] using ht)).le)
  have hza := hz _ _ hva
  have hzb := hz _ _ hvb
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hza,measure_eq_zero_iff_ae_notMem.mp hzb] with q hqa hqb
  constructor
  · exact (min_le_left _ _).trans (by simpa [Metric.mem_ball,Real.dist_eq,not_lt,p,cut,DEF014Phase.separator] using hqa)
  · exact (min_le_right _ _).trans (by simpa [Metric.mem_ball,Real.dist_eq,not_lt,p,cut,DEF014Phase.separator] using hqb)

/-- The support avoids the real cuts, hence it avoids the entire radial
sweep between the circle and rectangle. This is the quantitative circular
support gap needed for the Cauchy-Goursat transport. -/
lemma radial_gap_of_endpoints {μ : Measure ℝ} {a b δ : ℝ}
    (hg : ∀ᵐ q : ℝ ∂μ,δ≤|q-a| ∧ δ≤|q-b|) :
    ∀ᵐ q : ℝ ∂μ,δ≤|‖(q:ℂ)-(((a+b)/2:ℝ):ℂ)‖-(b-a)/2| := by
  filter_upwards [hg] with q hq
  simp only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  by_cases ht : q≤(a+b)/2
  · rw [abs_of_nonpos (by linarith : q-(a+b)/2≤0)]
    have he : -(q-(a+b)/2)-(b-a)/2= -(q-a) := by ring
    rw [he,abs_neg]
    exact hq.1
  · rw [abs_of_nonneg (by linarith : 0≤q-(a+b)/2)]
    have he : q-(a+b)/2-(b-a)/2=q-b := by ring
    rw [he]
    exact hq.2

/-- Actual circle-to-rectangle contour transport for any finite measure.
Cauchy-Goursat gives identical kernel residues; the two justified Fubini
interchanges transport the full Cauchy transform in its analyticity domain.
There is no assumed mass, action, or contour equality. -/
theorem cauchy_circle_rectangle (μ : Measure ℝ) [IsFiniteMeasure μ] {a b h δ : ℝ}
    (hab : a<b) (hh : 0<h) (hδ : 0<δ)
    (hg : ∀ᵐ q : ℝ ∂μ,δ≤|q-a| ∧ δ≤|q-b|) :
    (∮ z in C((((a+b)/2:ℝ):ℂ),(b-a)/2),EmpiricalRapidity.cauchyTransform μ z) =
      rectIntegral (EmpiricalRapidity.cauchyTransform μ) a b h := by
  rw [DEF014Contour.integral_cauchy μ ((a+b)/2) (by linarith : 0<(b-a)/2)
    hδ (radial_gap_of_endpoints hg),DEF014Contour.diameter_set,
    rectangle_cauchy μ hab hh hδ hg]

/-- Transport of the full Cauchy period to the frozen norm rectangle.
The proof computes the same residues in the common pole-free analyticity
domain, justifying transport for the finite full-mass measure. -/
theorem eventually_rectangle_period (hκ : 0<κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h) :
    ∀ᶠ v : L2T L in 𝓝 u,rectIntegral (fun z => G hκ z v)
      (cut hκ u (n-1)) (cut hκ u n) h = (2*(Real.pi:ℂ)*I)*(mass hκ n v:ℂ) := by
  obtain ⟨δ,hδ,hg⟩ := endpoint_gaps hκ u n
  filter_upwards [hg,RootScalarPeriodR8.eventually_mass_eq_cauchyPeriod hκ u n] with v hv hm
  have hab : cut hκ u (n-1)<cut hκ u n :=
    (DEF014Phase.facts ((⟨κ,hκ⟩,u):DEF014Phase.Param L)).phase.separator_strictMono (by omega)
  have ht := cauchy_circle_rectangle (PhysicalQuantumMeasure.measure hκ v) hab hh hδ hv
  change (mass hκ n v:ℂ)=(2*(Real.pi:ℂ)*I)⁻¹* _ at hm
  change (∮ z in C((center hκ u n:ℂ),radius hκ u n),G hκ z v) =
    rectIntegral (fun z => G hκ z v) (cut hκ u (n-1)) (cut hκ u n) h at ht
  rw [← ht,hm]
  field_simp
  rfl

/-- Explicit circle-to-rectangle equality on a full neighborhood. -/
theorem circle_rectangle_deformation (hκ : 0<κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0<h) :
    ∀ᶠ v : L2T L in 𝓝 u,
      (∮ z in C((center hκ u n:ℂ),radius hκ u n),G hκ z v) =
        rectIntegral (fun z => G hκ z v) (cut hκ u (n-1)) (cut hκ u n) h := by
  filter_upwards [RootScalarPeriodR8.eventually_mass_eq_cauchyPeriod hκ u n,
    eventually_rectangle_period hκ u n hh] with v hc hr
  change (mass hκ n v:ℂ)=(2*(Real.pi:ℂ)*I)⁻¹* _ at hc
  rw [hr,hc]
  field_simp
  rfl

end QuantumNLS.Prop010RectangleTransportR17
