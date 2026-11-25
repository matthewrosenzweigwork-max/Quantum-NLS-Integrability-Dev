import QuantumNLS.Q07WindowDifferentiationR16
import QuantumNLS.Prop018Period

/-! Concrete polynomial Cauchy kernels and finite-measure Fubini for the
actual rectangular contour. No general owner-held Fubini contract is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory Complex
namespace QuantumNLS.Q07ContourMeasureR16
open ResolventNeighborhood (GammaN)
open Q07WindowDifferentiationR16 (side lo hi coefficient rect_sum side_mem)

 theorem rect_label (a h : ℝ) (F : ℂ → ℂ) :
    PropagationContour.rectContour a h F = LabelExactPeriod.rectIntegral F (-a) a h := by
  simp only [PropagationContour.rectContour,LabelExactPeriod.rectIntegral,
    intervalIntegral.integral_mul_const,Complex.ofReal_neg,neg_mul,sub_eq_add_neg,smul_eq_mul]
  ring

/-- Polynomial Cauchy kernel outside the real window, by Cauchy-Goursat on
the closed rectangle, with the pole proved absent there. -/
theorem kernel_outside {a h q : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    (hq : q < -a ∨ a < q) (r : ℕ) :
    PropagationContour.rectContour a h (fun z => z^r*(z-(q : ℂ))⁻¹) = 0 := by
  let K : ℂ → ℂ := fun z => z^r*(z-(q : ℂ))⁻¹
  have hf : DifferentiableOn ℂ K (Icc (-a) a ×ℂ Icc (-h) h) := by
    intro z hz
    have hzq : z ≠ (q : ℂ) := by
      intro he
      have hr : -a ≤ z.re ∧ z.re ≤ a := hz.1
      rw [he,Complex.ofReal_re] at hr
      rcases hq with hq | hq <;> linarith
    exact ((differentiableAt_id.pow r).mul
      ((differentiableAt_id.sub_const (q : ℂ)).inv (sub_ne_zero.mpr hzq))).differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn K
    ((-a : ℂ)-(h : ℂ)*I) ((a : ℂ)+(h : ℂ)*I)
  have hs : (uIcc (((-a : ℂ)-(h : ℂ)*I).re) (((a : ℂ)+(h : ℂ)*I).re) ×ℂ
      uIcc (((-a : ℂ)-(h : ℂ)*I).im) (((a : ℂ)+(h : ℂ)*I).im)) =
        (Icc (-a) a ×ℂ Icc (-h) h) := by
    simp [uIcc_of_le (by linarith : -a ≤ a),uIcc_of_le (by linarith : -h ≤ h)]
  rw [hs] at hc
  rw [rect_label]
  simpa [LabelExactPeriod.rectIntegral,K] using hc hf

/-- The inside and outside polynomial residues, with both endpoint
exclusions explicit. -/
theorem kernel_rectangle {a h q : ℝ} (ha : 0 ≤ a) (hh : 0 < h)
    (hqa : q ≠ a) (hqb : q ≠ -a) (r : ℕ) :
    PropagationContour.rectContour a h (fun z => z^r*(z-(q : ℂ))⁻¹) =
      (2*(Real.pi : ℂ)*I) * (Ioo (-a) a).indicator (fun t : ℝ => (t : ℂ)^r) q := by
  by_cases hq : q ∈ Ioo (-a) a
  · rw [indicator_of_mem hq,rect_label]
    exact Prop018Period.rect_pow_inv (by linarith) hh.le
      (by simpa using hq.1) (by simpa using hq.2) (by simpa using hh) r
  · rw [indicator_of_notMem hq,mul_zero]
    apply kernel_outside ha hh _ r
    by_cases hlow : q < -a
    · exact Or.inl hlow
    · have hle : -a ≤ q := le_of_not_gt hlow
      have hgt : -a < q := lt_of_le_of_ne hle (Ne.symm hqb)
      have hge : a ≤ q := by
        by_contra hn
        exact hq ⟨hgt,lt_of_not_ge hn⟩
      exact Or.inr (lt_of_le_of_ne hge (Ne.symm hqa))

/-- A concrete finite-measure side interchange. Joint measurability and a
common product-integrable bound are proved from the actual Cauchy kernel. -/
theorem side_fubini (μ : Measure ℝ) [IsFiniteMeasure μ] (γ : ℝ → ℂ) (hγ : Continuous γ)
    {a b Z δ : ℝ} (hab : a ≤ b) (hZ : 0 ≤ Z) (hδ : 0 < δ) (r : ℕ)
    (hγZ : ∀ t ∈ Icc a b, ‖γ t‖ ≤ Z)
    (hgap : ∀ᵐ (q : ℝ) ∂μ, ∀ t ∈ Icc a b, δ ≤ ‖γ t-(q : ℂ)‖) :
    (∫ t in a..b, γ t^r*EmpiricalRapidity.cauchyTransform μ (γ t)) =
      ∫ q, (∫ t in a..b, γ t^r*(γ t-(q : ℂ))⁻¹) ∂μ ∧
    Integrable (fun q : ℝ => ∫ t in a..b, γ t^r*(γ t-(q : ℂ))⁻¹) μ := by
  let ν := volume.restrict (Ioc a b)
  let K : ℝ × ℝ → ℂ := fun p => γ p.2^r*(γ p.2-(p.1 : ℂ))⁻¹
  have hm : Measurable K := by dsimp [K]; fun_prop
  have hb : ∀ᵐ p : ℝ × ℝ ∂μ.prod ν, ‖K p‖ ≤ Z^r*δ⁻¹ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
    filter_upwards [hgap] with q hq
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le,ht.2⟩
    dsimp [K]
    rw [norm_mul,norm_pow,norm_inv]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hγZ t ht') r)
      (inv_anti₀ hδ (hq t ht')) (inv_nonneg.mpr (norm_nonneg _)) (pow_nonneg hZ r)
  have hk : Integrable K (μ.prod ν) :=
    (integrable_const (Z^r*δ⁻¹)).mono' hm.aestronglyMeasurable hb
  have hInt : Integrable (fun q : ℝ => ∫ t in a..b, γ t^r*(γ t-(q : ℂ))⁻¹) μ := by
    simpa only [intervalIntegral.integral_of_le hab,ν,K] using hk.integral_prod_left
  refine ⟨?_,hInt⟩
  rw [intervalIntegral.integral_of_le hab]
  have hs := integral_integral_swap (f := fun q t => K (q,t)) hk
  calc
    _ = ∫ t, (∫ q, K (q,t) ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards with t
      simp only [K,EmpiricalRapidity.cauchyTransform,integral_const_mul]
    _ = ∫ q, (∫ t, K (q,t) ∂ν) ∂μ := hs.symm
    _ = _ := by simp only [intervalIntegral.integral_of_le hab,ν,K]


/-- Both real endpoint gaps give a common support distance along the whole
rectangle, with no normalization of the finite measure. -/
theorem rectangle_distance (μ : Measure ℝ) {a h δ : ℝ} (hh : 0 < h)
    (hg : ∀ᵐ (q : ℝ) ∂μ, δ ≤ |q-a| ∧ δ ≤ |q+a|) :
    ∀ᵐ (q : ℝ) ∂μ, ∀ z ∈ GammaN a h, min δ h ≤ ‖z-(q : ℂ)‖ := by
  filter_upwards [hg] with q hq z hz
  rcases hz with ⟨hr,-⟩ | ⟨hi,-⟩
  · rcases hr with hr | hr
    · exact (min_le_left _ _).trans (Q07FiniteGeometryR16.norm_ge_of_gap hr hq.1)
    · exact (min_le_left _ _).trans
        (Q07FiniteGeometryR16.norm_ge_of_gap hr (by simpa only [sub_neg_eq_add] using hq.2))
  · have he : |z.im| = h := by
      rcases hi with hi | hi <;> simp [hi,abs_of_pos hh]
    have hb := Complex.abs_im_le_norm (z-(q : ℂ))
    have hb' : h ≤ ‖z-(q : ℂ)‖ := by
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,he] using hb
    exact (min_le_right δ h).trans hb' 

/-- The full polynomial Cauchy contour equals its finite-measure residue
integral. Every side interchange is the proved concrete product integral. -/
theorem rectangle_cauchy (μ : Measure ℝ) [IsFiniteMeasure μ] {a h δ : ℝ}
    (ha : 0 ≤ a) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (hg : ∀ᵐ (q : ℝ) ∂μ, δ ≤ |q-a| ∧ δ ≤ |q+a|) :
    PropagationContour.rectContour a h (fun z => z^r*EmpiricalRapidity.cauchyTransform μ z) =
      (2*(Real.pi : ℂ)*I)*∫ q, (Ioo (-a) a).indicator (fun t : ℝ => (t : ℂ)^r) q ∂μ := by
  have hab : ∀ i : Fin 4, lo a h i ≤ hi a h i := by
    intro i; fin_cases i <;> simp [lo,hi] <;> linarith
  let K : Fin 4 → ℝ → ℂ := fun i q =>
    ∫ t in lo a h i..hi a h i, (side a h i t)^r*(side a h i t-(q : ℂ))⁻¹
  have hs : ∀ i : Fin 4,
      (∫ t in lo a h i..hi a h i, (side a h i t)^r*EmpiricalRapidity.cauchyTransform μ (side a h i t)) =
        ∫ q, K i q ∂μ ∧ Integrable (K i) μ := by
    intro i
    have hcont : Continuous (side a h i) := by
      fin_cases i
      · change Continuous (fun t : ℝ => (t : ℂ)-(h : ℂ)*I)
        fun_prop
      · change Continuous (fun t : ℝ => (a : ℂ)+(t : ℂ)*I)
        fun_prop
      · change Continuous (fun t : ℝ => (t : ℂ)+(h : ℂ)*I)
        fun_prop
      · change Continuous (fun t : ℝ => ((-a : ℝ) : ℂ)+(t : ℂ)*I)
        fun_prop
    apply side_fubini μ (side a h i) hcont (hab i) (Z := a+h) (δ := min δ h)
      (by linarith) (lt_min hδ hh) r
    · exact fun t ht => Q07IntegratedHessiansR16.norm_le_of_GammaN ha hh.le (side_mem i ht)
    · filter_upwards [rectangle_distance μ hh hg] with q hq t ht
      exact hq _ (side_mem i ht)
  have hswap : PropagationContour.rectContour a h
      (fun z => z^r*EmpiricalRapidity.cauchyTransform μ z) =
      ∫ q, PropagationContour.rectContour a h (fun z => z^r*(z-(q : ℂ))⁻¹) ∂μ := by
    rw [rect_sum]
    calc
      _ = ∑ i : Fin 4, coefficient i*(∫ q, K i q ∂μ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(hs i).1]
      _ = ∑ i : Fin 4, ∫ q, coefficient i*K i q ∂μ := by simp only [integral_const_mul]
      _ = ∫ q, ∑ i : Fin 4, coefficient i*K i q ∂μ := by
        rw [integral_finsetSum _ (fun i _ => (hs i).2.const_mul _)]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with q
        rw [rect_sum]
  rw [hswap]
  calc
    _ = ∫ q, (2*(Real.pi : ℂ)*I)*(Ioo (-a) a).indicator (fun t : ℝ => (t : ℂ)^r) q ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg] with q hq
      apply kernel_rectangle ha hh _ _ r
      · intro hqa; subst q; simp at hq; linarith [hq.1]
      · intro hqb; subst q; simp at hq; linarith [hq.2]
    _ = _ := integral_const_mul _ _

/-- The polynomial restricted to the finite window is genuinely integrable. -/
theorem indicator_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {a : ℝ}
    (ha : 0 ≤ a) (r : ℕ) :
    Integrable ((Ioo (-a) a).indicator (fun t : ℝ => (t : ℂ)^r)) μ := by
  apply (integrable_const (a^r)).mono'
    (((Complex.continuous_ofReal.pow r).measurable.indicator measurableSet_Ioo).aestronglyMeasurable)
  filter_upwards with q
  by_cases hq : q ∈ Ioo (-a) a
  · rw [indicator_of_mem hq]
    change ‖(q : ℂ)^r‖ ≤ a^r
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨hq.1.le,hq.2.le⟩) r
  · simp only [indicator_of_notMem hq,norm_zero]
    exact pow_nonneg ha r

/-- Exact source prefactor and Cauchy-to-window-measure identity for every
finite positive measure with the proved endpoint gaps. -/
theorem contour_measure (μ : Measure ℝ) [IsFiniteMeasure μ] {κ a h δ : ℝ}
    (hκ : 0 < κ) (ha : 0 ≤ a) (hh : 0 < h) (hδ : 0 < δ) (r : ℕ)
    (hg : ∀ᵐ (q : ℝ) ∂μ, δ ≤ |q-a| ∧ δ ≤ |q+a|) :
    -(1/(2*Real.pi*κ))*(PropagationContour.rectContour a h
      (fun z => z^r*(I*(κ : ℂ)*EmpiricalRapidity.cauchyTransform μ z))).re =
        ∫ q in Ioo (-a) a, q^r ∂μ := by
  have hfac : PropagationContour.rectContour a h
      (fun z => z^r*(I*(κ : ℂ)*EmpiricalRapidity.cauchyTransform μ z)) =
      (I*(κ : ℂ))*PropagationContour.rectContour a h
        (fun z => z^r*EmpiricalRapidity.cauchyTransform μ z) := by
    have he : (fun z : ℂ => z^r*(I*(κ : ℂ)*EmpiricalRapidity.cauchyTransform μ z)) =
        (fun z => (I*(κ : ℂ))*(z^r*EmpiricalRapidity.cauchyTransform μ z)) := by funext z; ring
    rw [he,rect_label,rect_label,PeriodTwoTerm.rectIntegral_const_mul]
  have hre : (∫ q, (Ioo (-a) a).indicator (fun t : ℝ => (t : ℂ)^r) q ∂μ).re =
      ∫ q in Ioo (-a) a, q^r ∂μ := by
    calc
      _ = ∫ q, ((Ioo (-a) a).indicator (fun t : ℝ => (t : ℂ)^r) q).re ∂μ :=
        (Complex.reCLM.integral_comp_comm (indicator_integrable μ ha r)).symm
      _ = ∫ q, (Ioo (-a) a).indicator (fun t : ℝ => t^r) q ∂μ := by
        apply integral_congr_ae
        filter_upwards with q
        by_cases hq : q ∈ Ioo (-a) a
        · simp only [indicator_of_mem hq,← Complex.ofReal_pow,Complex.ofReal_re]
        · simp only [indicator_of_notMem hq,Complex.zero_re]
      _ = _ := integral_indicator measurableSet_Ioo
  rw [hfac,rectangle_cauchy μ ha hh hδ r hg]
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,show (2 : ℂ).re = (2 : ℝ) from rfl,show (2 : ℂ).im = (0 : ℝ) from rfl,
    zero_mul,mul_zero,zero_sub,one_mul,mul_one,sub_zero,zero_add]
  rw [hre]
  field_simp [hκ.ne',Real.pi_ne_zero]
  ring

end QuantumNLS.Q07ContourMeasureR16
