import QuantumNLS.RootScalarDensityR28

/-! The Abel and symmetric principal-value boundary integrals coincide.
All local and tail majorants are proved for the actual integrands. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace QuantumNLS.RootScalarAbelR28
open RootHilbert

lemma integral_odd (f : ℝ → ℝ) (hf : ∀ t,f (-t) = -f t) : ∫ t,f t = 0 := by
  have h := integral_neg_eq_self f (volume : Measure ℝ)
  have he : (fun t => f (-t)) = fun t => -f t := funext hf
  rw [he,integral_neg] at h
  linarith

lemma subtracted_integrable {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) (x : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ Integrable (fun t =>
      (ρ (x-t)-(Ioo (-δ) δ).indicator (fun _ => ρ x) t)/t) := by
  obtain ⟨s,hs,C,r,hr,_,hH⟩ := hρ.holder x
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hs
  let U := Ioo (-δ) δ
  let V := {t : ℝ | δ ≤ |t|}
  have hxs : x ∈ s := hball (Metric.mem_ball_self hδ)
  have hm : Measurable (fun t => (ρ (x-t)-ρ x)/t) :=
    ((hρ.continuous.comp (continuous_const.sub continuous_id)).measurable.sub measurable_const).div measurable_id
  have hb : Integrable (U.indicator (fun t => (C:ℝ)*|t|^((r:ℝ)-1))) := by
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact (integrableOn_abs_rpow (by linarith [r.coe_pos.mpr hr]) hδ).const_mul _
  have hi : Integrable (U.indicator (fun t => (ρ (x-t)-ρ x)/t)) := by
    apply hb.mono' (hm.aestronglyMeasurable.indicator measurableSet_Ioo)
    apply ae_of_all
    intro t
    by_cases ht : t ∈ U
    · rw [indicator_of_mem ht,indicator_of_mem ht,Real.norm_eq_abs]
      by_cases ht0 : t = 0
      · simp [ht0]; positivity
      have hta : |t| < δ := abs_lt.mpr ht
      have hx : x-t ∈ s := hball (by simpa [Metric.mem_ball,Real.dist_eq] using hta)
      have hh := hH.dist_le hx hxs
      simp only [Real.dist_eq,sub_sub_cancel_left,abs_neg] at hh
      rw [abs_div,Real.rpow_sub_one (abs_pos.mpr ht0).ne',← mul_div_assoc]
      exact div_le_div_of_nonneg_right hh (abs_nonneg _)
    · rw [indicator_of_notMem ht,indicator_of_notMem ht,norm_zero]
  have hv : MeasurableSet V := measurableSet_le measurable_const (by fun_prop)
  have ho : Integrable (V.indicator (fun t => ρ (x-t)/t)) :=
    integrable_ind hρ hδ V hv (fun _ ht => ht) x
  refine ⟨δ,hδ, (hi.add ho).congr (ae_of_all _ fun t => ?_)⟩
  by_cases ht : t ∈ U
  · have hv' : t ∉ V := by simpa [V,not_le] using (abs_lt.mpr ht)
    change _ = (ρ (x-t)-U.indicator (fun _ => ρ x) t)/t
    simp [ht,hv',Pi.add_apply]
  · have hv' : t ∈ V := by simpa [V,U,mem_Ioo,← abs_lt,not_lt] using ht
    change _ = (ρ (x-t)-U.indicator (fun _ => ρ x) t)/t
    simp [ht,hv',Pi.add_apply]

lemma abel_limit {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) (x : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t,ρ (x-t)*LabelIdentification.kε ε t)
      (𝓝[>] 0) (𝓝 (hilbertPV ρ x)) := by
  obtain ⟨δ,hδ,hF⟩ := subtracted_integrable hρ x
  let U := Ioo (-δ) δ
  let F := fun t => (ρ (x-t)-U.indicator (fun _ => ρ x) t)/t
  have hmU : MeasurableSet U := measurableSet_Ioo
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    apply ae_iff.mpr
    simpa using (measure_singleton (0:ℝ) : volume {0} = 0)
  have intC : ∀ ε : ℝ, 0 < ε → Integrable (fun t =>
      U.indicator (fun _ => ρ x) t*LabelIdentification.kε ε t) := by
    intro ε hε
    have hh : Integrable (U.indicator (fun _ : ℝ => |ρ x|/ε)) := by
      rw [integrable_indicator_iff hmU]; exact integrableOn_const (by simp [U])
    apply hh.mono' (((aestronglyMeasurable_const.indicator hmU).mul
      (LabelIdentification.continuous_kε hε).aestronglyMeasurable))
    apply ae_of_all
    intro t
    change ‖U.indicator (fun _ => ρ x) t*LabelIdentification.kε ε t‖ ≤
      U.indicator (fun _ => |ρ x|/ε) t
    by_cases ht : t ∈ U
    · simp only [indicator_of_mem ht,norm_mul,Real.norm_eq_abs]
      calc |ρ x| * |LabelIdentification.kε ε t| ≤ |ρ x| * (1/ε) :=
            mul_le_mul_of_nonneg_left (LabelIdentification.abs_kε_le hε t) (abs_nonneg _)
        _ = _ := by ring
    · simp [ht]
  have intT : ∀ ε : ℝ, 0 < ε → Integrable (fun t =>
      {t : ℝ | ε < |t|}.indicator (fun t => U.indicator (fun _ => ρ x) t/t) t) := by
    intro ε hε
    have hh : Integrable (U.indicator (fun _ : ℝ => |ρ x|/ε)) := by
      rw [integrable_indicator_iff hmU]; exact integrableOn_const (by simp [U])
    apply hh.mono' (((measurable_const.indicator hmU).div
      measurable_id).aestronglyMeasurable.indicator (measurableSet_gt_abs ε))
    apply ae_of_all
    intro t
    by_cases ht : t ∈ U
    · rw [indicator_of_mem ht]
      by_cases he : ε < |t|
      · have he' : t ∈ {t : ℝ | ε < |t|} := he
        rw [indicator_of_mem he']
        change ‖U.indicator (fun _ => ρ x) t/t‖ ≤ _
        rw [indicator_of_mem ht,Real.norm_eq_abs,abs_div]
        exact div_le_div_of_nonneg_left (abs_nonneg _) hε he.le
      · have he' : t ∉ {t : ℝ | ε < |t|} := he
        rw [indicator_of_notMem he',norm_zero]; positivity
    · simp [ht]
  have oddU : ∀ t : ℝ, -t ∈ U ↔ t ∈ U := by intro t; simp [U,mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  have eqT : ∀ ε : ℝ, 0 < ε → hilbertTrunc ρ ε x =
      ∫ t,{t : ℝ | ε < |t|}.indicator F t := by
    intro ε hε
    have hi := hF.indicator (measurableSet_gt_abs ε)
    have he : (fun t => {t : ℝ | ε < |t|}.indicator (fun t => ρ (x-t)/t) t) =
        (fun t => {t : ℝ | ε < |t|}.indicator F t +
        {t : ℝ | ε < |t|}.indicator (fun t => U.indicator (fun _ => ρ x) t/t) t) := by
      funext t
      by_cases ht : ε < |t|
      · have ht' : t ∈ {t : ℝ | ε < |t|} := ht
        simp only [indicator_of_mem ht',F]; ring
      · simp [ht]
    rw [hilbertTrunc_eq,he,integral_add hi (intT ε hε)]
    have hz : (∫ t,{t : ℝ | ε < |t|}.indicator (fun t => U.indicator (fun _ => ρ x) t/t) t) = 0 := by
      apply integral_odd
      intro t
      by_cases h1 : ε < |t| <;> by_cases h2 : t ∈ U <;>
        simp [h1,h2,oddU,abs_neg,div_neg]
    rw [hz,add_zero]
  have limT : Tendsto (fun ε : ℝ => ∫ t,{t : ℝ | ε < |t|}.indicator F t)
      (𝓝[>] 0) (𝓝 (∫ t,F t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖F t‖)
      (Eventually.of_forall fun ε => hF.aestronglyMeasurable.indicator (measurableSet_gt_abs ε))
      (Eventually.of_forall fun ε => ae_of_all _ fun t => norm_indicator_le_norm_self _ _) hF.norm
    filter_upwards [hne] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT (abs_pos.mpr ht)] with ε hε
    exact (indicator_of_mem (show t ∈ {t : ℝ | ε < |t|} from hε.2) F).symm
  have hPV : hilbertPV ρ x = ∫ t,F t :=
    tendsto_nhds_unique (tendsto_hilbertPV hρ x) (limT.congr' (hpos.mono fun ε hε => (eqT ε hε).symm))
  rw [hPV]
  let w := fun ε t : ℝ => t^2/(t^2+ε^2)
  have hw : ∀ ε, 0 < ε → ∀ t, |w ε t| ≤ 1 := by
    intro ε hε t
    have hp : 0 < t^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
    dsimp only [w]
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le)]
    exact (div_le_one hp).mpr (by nlinarith [sq_nonneg ε])
  have hiw : ∀ ε, 0 < ε → Integrable (fun t => F t*w ε t) := by
    intro ε hε
    apply hF.norm.mono' (hF.aestronglyMeasurable.mul (by exact (by fun_prop : Measurable (w ε)).aestronglyMeasurable))
    exact ae_of_all _ fun t => by
      change ‖F t*w ε t‖ ≤ ‖F t‖
      simp only [norm_mul,Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hw ε hε t)
  have heq : ∀ ε, 0 < ε → (∫ t,ρ (x-t)*LabelIdentification.kε ε t) = ∫ t,F t*w ε t := by
    intro ε hε
    have he : (fun t => ρ (x-t)*LabelIdentification.kε ε t) =
        (fun t => F t*w ε t+U.indicator (fun _ => ρ x) t*LabelIdentification.kε ε t) := by
      funext t
      dsimp [F,w,LabelIdentification.kε]
      by_cases ht : t = 0
      · simp [ht]
      · field_simp [ht]; ring
    rw [he,integral_add (hiw ε hε) (intC ε hε)]
    have hz : (∫ t,U.indicator (fun _ => ρ x) t*LabelIdentification.kε ε t) = 0 := by
      apply integral_odd
      intro t
      by_cases ht : t ∈ U <;> simp [ht,oddU,LabelIdentification.kε_neg]
    rw [hz,add_zero]
  apply Tendsto.congr' (hpos.mono fun ε hε => (heq ε hε).symm)
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖F t‖)
    (Eventually.of_forall fun ε => hF.aestronglyMeasurable.mul ((by fun_prop : Measurable (w ε)).aestronglyMeasurable))
    (hpos.mono fun ε hε => ae_of_all _ fun t => by
      change ‖F t*w ε t‖ ≤ ‖F t‖
      simp only [norm_mul,Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hw ε hε t)) hF.norm
  filter_upwards [hne] with t ht
  have hh : Tendsto (fun ε : ℝ => w ε t) (𝓝[>] 0) (𝓝 1) := by
    have hp : t^2 ≠ 0 := pow_ne_zero _ ht
    have hc : ContinuousAt (fun ε : ℝ => w ε t) 0 := by dsimp [w]; fun_prop (disch := simpa using hp)
    simpa [w,hp] using hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa using tendsto_const_nhds.mul hh

end QuantumNLS.RootScalarAbelR28
