import Mathlib

set_option autoImplicit false

namespace NlsGge.SpectralFoundations

open MeasureTheory Filter Topology Set

/-- Principal-value Hilbert transform `lim_{δ→0+} ∫_{δ<|t-λ|} v t /(λ-t) dt`
(via `limUnder`; it is the actual limit, see `tendsto_pvHilbert_E02_38`). -/
noncomputable def pvHilbert (v : ℝ → ℝ) (lam : ℝ) : ℝ :=
  limUnder (𝓝[>] (0:ℝ)) (fun δ : ℝ => ∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t))

/-- Standing hypotheses: continuous, supported in `[-A,A]`, Hölder-1/2 with constant `H`. -/
structure PlemeljHypE02_38 (v : ℝ → ℝ) (H A : ℝ) : Prop where
  cont : Continuous v
  hH : 0 ≤ H
  hA : 0 ≤ A
  supp : ∀ t, t ∉ Icc (-A) A → v t = 0
  holder : ∀ s t, |v s - v t| ≤ H * √|s - t|

namespace PlemeljHypE02_38

variable {v : ℝ → ℝ} {H A : ℝ}

lemma integrable (h : PlemeljHypE02_38 v H A) : Integrable v := by
  apply h.cont.integrable_of_hasCompactSupport
  exact HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) (fun t ht => h.supp t ht)

lemma bounded (h : PlemeljHypE02_38 v H A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |v t| ≤ B := by
  have hH := h.hH
  refine ⟨H * √(2 * A + 1), by positivity, fun t => ?_⟩
  by_cases ht : t ∈ Icc (-A) A
  · have h1 := h.holder t (A + 1)
    have h0 : v (A + 1) = 0 := h.supp _ (by simp only [mem_Icc, not_and, not_le]; intro; linarith)
    rw [h0, sub_zero] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hH)
    rw [abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.1]
  · rw [h.supp t ht]; simp; positivity

end PlemeljHypE02_38

/-- the folded integrand `(v(λ-s) - v(λ+s))/s`. -/
noncomputable def wfunE02_38 (v : ℝ → ℝ) (lam s : ℝ) : ℝ := (v (lam - s) - v (lam + s)) / s

namespace PlemeljHypE02_38

variable {v : ℝ → ℝ} {H A : ℝ}

lemma w_bound (h : PlemeljHypE02_38 v H A) (lam : ℝ) {s : ℝ} (hs : 0 < s) :
    |wfunE02_38 v lam s| ≤ H * √2 * s ^ (-(1/2:ℝ)) := by
  unfold wfunE02_38
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have h1 := h.holder (lam - s) (lam + s)
  have e : |lam - s - (lam + s)| = 2 * s := by
    rw [show lam - s - (lam + s) = -(2 * s) by ring, abs_neg, abs_of_pos (by linarith)]
  rw [e, Real.sqrt_mul (by norm_num)] at h1
  have hk : s ^ (-(1/2:ℝ)) * s = √s := by
    have := Real.rpow_add hs (-(1/2:ℝ)) 1
    rw [Real.rpow_one] at this
    rw [← this, Real.sqrt_eq_rpow]; norm_num
  calc |v (lam - s) - v (lam + s)| ≤ H * (√2 * √s) := h1
    _ = H * √2 * s ^ (-(1/2:ℝ)) * s := by rw [← hk]; ring

/-- dominating function -/
noncomputable def Dfun (v : ℝ → ℝ) (H lam : ℝ) (s : ℝ) : ℝ :=
  (Ioc (0:ℝ) 1).indicator (fun s : ℝ => H * √2 * s ^ (-(1/2:ℝ))) s
    + (|v (lam - s)| + |v (lam + s)|)

lemma Dfun_nonneg (h : PlemeljHypE02_38 v H A) (lam s : ℝ) : 0 ≤ Dfun v H lam s := by
  unfold Dfun
  have hH := h.hH
  refine add_nonneg (indicator_nonneg (fun x hx => by have := hx.1; positivity) _) (by positivity)

lemma Dfun_integrable (h : PlemeljHypE02_38 v H A) (lam : ℝ) : Integrable (Dfun v H lam) := by
  have hr : IntegrableOn (fun s : ℝ => s ^ (-(1/2:ℝ))) (Ioc (0:ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1/2:ℝ))
      (by norm_num)).1
  have h0 : IntegrableOn (fun s : ℝ => H * √2 * s ^ (-(1/2:ℝ))) (Ioc (0:ℝ) 1) :=
    Integrable.const_mul hr (H * √2)
  have h1 : Integrable ((Ioc (0:ℝ) 1).indicator (fun s : ℝ => H * √2 * s ^ (-(1/2:ℝ)))) :=
    h0.integrable_indicator measurableSet_Ioc
  exact h1.add (((h.integrable.comp_sub_left lam).abs).add ((h.integrable.comp_add_left lam).abs))

lemma w_dom (h : PlemeljHypE02_38 v H A) (lam : ℝ) {s : ℝ} (hs : 0 < s) :
    |wfunE02_38 v lam s| ≤ Dfun v H lam s := by
  unfold Dfun
  have hH := h.hH
  by_cases h1 : s ≤ 1
  · rw [indicator_of_mem (show s ∈ Ioc (0:ℝ) 1 from ⟨hs, h1⟩)]
    have := h.w_bound lam hs
    have : 0 ≤ |v (lam - s)| + |v (lam + s)| := by positivity
    linarith [h.w_bound lam hs]
  · have h2 : (0:ℝ) ≤ (Ioc (0:ℝ) 1).indicator (fun s : ℝ => H * √2 * s ^ (-(1/2:ℝ))) s :=
      indicator_nonneg (fun x hx => by have := hx.1; positivity) _
    have h3 : |wfunE02_38 v lam s| ≤ |v (lam - s)| + |v (lam + s)| := by
      unfold wfunE02_38
      rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
      have : |v (lam - s) - v (lam + s)| ≤ |v (lam - s)| + |v (lam + s)| := abs_sub _ _
      have h4 : 0 ≤ |v (lam - s)| + |v (lam + s)| := by positivity
      nlinarith
    linarith

lemma w_meas (h : PlemeljHypE02_38 v H A) (lam : ℝ) :
    AEStronglyMeasurable (wfunE02_38 v lam) (volume.restrict (Ioi (0:ℝ))) := by
  have hc := h.cont
  have : ContinuousOn (wfunE02_38 v lam) (Ioi 0) := by
    unfold wfunE02_38
    refine ContinuousOn.div ?_ continuousOn_id (fun s hs => ne_of_gt hs)
    exact ((hc.comp (continuous_const.sub continuous_id)).sub
      (hc.comp (continuous_const.add continuous_id))).continuousOn
  exact this.aestronglyMeasurable measurableSet_Ioi

lemma w_integrableOn (h : PlemeljHypE02_38 v H A) (lam : ℝ) :
    IntegrableOn (wfunE02_38 v lam) (Ioi (0:ℝ)) := by
  refine Integrable.mono' (g := Dfun v H lam) (Dfun_integrable h lam).integrableOn (h.w_meas lam) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  rw [Real.norm_eq_abs]; exact h.w_dom lam hs


lemma Dfun_integral (h : PlemeljHypE02_38 v H A) (lam : ℝ) :
    ∫ s, Dfun v H lam s
      = H * √2 * (∫ s in Ioc (0:ℝ) 1, s ^ (-(1/2:ℝ))) + 2 * ∫ t, |v t| := by
  have hr : IntegrableOn (fun s : ℝ => s ^ (-(1/2:ℝ))) (Ioc (0:ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1/2:ℝ))
      (by norm_num)).1
  have h0 : IntegrableOn (fun s : ℝ => H * √2 * s ^ (-(1/2:ℝ))) (Ioc (0:ℝ) 1) :=
    Integrable.const_mul hr (H * √2)
  have h1 : Integrable ((Ioc (0:ℝ) 1).indicator (fun s : ℝ => H * √2 * s ^ (-(1/2:ℝ)))) :=
    h0.integrable_indicator measurableSet_Ioc
  have ha : Integrable (fun s : ℝ => |v (lam - s)|) := (h.integrable.comp_sub_left lam).abs
  have hb : Integrable (fun s : ℝ => |v (lam + s)|) := (h.integrable.comp_add_left lam).abs
  unfold Dfun
  rw [integral_add h1 (g := fun s => |v (lam - s)| + |v (lam + s)|) (by exact ha.add hb), integral_indicator measurableSet_Ioc, integral_const_mul,
    integral_add ha hb, integral_sub_left_eq_self (fun x => |v x|) volume lam,
    integral_add_left_eq_self (fun x => |v x|) lam]
  ring

lemma fold_eq (h : PlemeljHypE02_38 v H A) (lam δ : ℝ) (hδ : 0 < δ) :
    ∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t)
      = ∫ s in Ioi δ, wfunE02_38 v lam s := by
  set g : ℝ → ℝ := fun x => v (lam + x) / (lam - (lam + x)) with hg
  have gbd : ∀ x, δ < |x| → |g x| ≤ |v (lam + x)| / δ := by
    intro x hx
    simp only [hg]
    rw [show lam - (lam + x) = -x by ring, abs_div, abs_neg]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hδ hx.le
  have gm : AEStronglyMeasurable g (volume : Measure ℝ) := by
    have := h.cont.measurable
    exact (by simp only [hg]; fun_prop : Measurable g).aestronglyMeasurable
  have m1 : MeasurableSet {t : ℝ | δ < |t - lam|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have key : ∀ x : ℝ, (δ < |lam + x - lam|) ↔ (x ∈ Ioi δ ∪ Iio (-δ)) := by
    intro x
    rw [add_sub_cancel_left, lt_abs, lt_neg]
    simp only [mem_union, mem_Ioi, mem_Iio]
  have hS : ∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t) = ∫ x in Ioi δ ∪ Iio (-δ), g x := by
    rw [← integral_indicator m1, ← integral_add_left_eq_self _ lam,
      ← integral_indicator (measurableSet_Ioi.union measurableSet_Iio)]
    congr 1; ext x
    simp only [indicator, mem_setOf_eq]
    by_cases hx : x ∈ Ioi δ ∪ Iio (-δ)
    · rw [if_pos ((key x).2 hx), if_pos hx]
    · rw [if_neg (fun hh => hx ((key x).1 hh)), if_neg hx]
  have ig1 : IntegrableOn g (Ioi δ) := by
    refine Integrable.mono' (g := fun x => |v (lam + x)| / δ)
      ((h.integrable.comp_add_left lam).abs.div_const δ).integrableOn gm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs]
    exact gbd x (lt_of_lt_of_le hx (le_abs_self x))
  have ig2 : IntegrableOn g (Iio (-δ)) := by
    refine Integrable.mono' (g := fun x => |v (lam + x)| / δ)
      ((h.integrable.comp_add_left lam).abs.div_const δ).integrableOn gm.restrict ?_
    refine (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs]
    refine gbd x ?_
    have : x < -δ := hx
    rw [lt_abs]; right; linarith
  have ig3 : IntegrableOn (fun x => g (-x)) (Ioi δ) := by
    refine Integrable.mono' (g := fun x => |v (lam - x)| / δ)
      ((h.integrable.comp_sub_left lam).abs.div_const δ).integrableOn
      (by have := h.cont.measurable; exact (by simp only [hg]; fun_prop : Measurable (fun x => g (-x))).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs]
    have := gbd (-x) (by rw [abs_neg]; exact lt_of_lt_of_le hx (le_abs_self x))
    rwa [← sub_eq_add_neg] at this
  rw [hS, setIntegral_union (Set.disjoint_left.2 (fun x hx1 hx2 => by
      have h1 : δ < x := hx1
      have h2 : x < -δ := hx2
      linarith)) measurableSet_Iio ig1 ig2,
    ← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi δ g, ← integral_add ig1 ig3]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : 0 < x := lt_trans hδ hx
  simp only [hg, wfunE02_38]
  rw [show lam - (lam + x) = -x by ring, show lam - (lam + -x) = x by ring,
    show lam + -x = lam - x by ring]
  field_simp
  ring


lemma tendsto_Ioi (h : PlemeljHypE02_38 v H A) (lam : ℝ) :
    Tendsto (fun δ : ℝ => ∫ s in Ioi δ, wfunE02_38 v lam s) (𝓝[>] (0:ℝ))
      (𝓝 (∫ s in Ioi (0:ℝ), wfunE02_38 v lam s)) := by
  have hw := h.w_integrableOn lam
  have key : Tendsto (fun δ : ℝ => ∫ s in Ioi (0:ℝ), (Ioi δ).indicator (wfunE02_38 v lam) s)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ s in Ioi (0:ℝ), wfunE02_38 v lam s)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖wfunE02_38 v lam s‖)
      (Eventually.of_forall fun δ => (h.w_meas lam).indicator measurableSet_Ioi)
      (Eventually.of_forall fun δ => Eventually.of_forall fun s => norm_indicator_le_norm_self _ _)
      hw.norm ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    refine tendsto_const_nhds.congr' ?_
    have : Iio s ∈ 𝓝[>] (0:ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs)
    filter_upwards [this] with δ hδ
    rw [indicator_of_mem (show s ∈ Ioi δ from hδ)]
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : (0:ℝ) < δ := hδ
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hδ'.le]

lemma bound_Ioi (h : PlemeljHypE02_38 v H A) (lam δ : ℝ) (hδ : 0 < δ) :
    |∫ s in Ioi δ, wfunE02_38 v lam s|
      ≤ H * √2 * (∫ s in Ioc (0:ℝ) 1, s ^ (-(1/2:ℝ))) + 2 * ∫ t, |v t| := by
  have hD := Dfun_integrable h lam
  have hsub : IntegrableOn (wfunE02_38 v lam) (Ioi δ) :=
    (h.w_integrableOn lam).mono_set (Ioi_subset_Ioi hδ.le)
  calc |∫ s in Ioi δ, wfunE02_38 v lam s|
      ≤ ∫ s in Ioi δ, |wfunE02_38 v lam s| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := volume.restrict (Ioi δ))
          (wfunE02_38 v lam)
    _ ≤ ∫ s in Ioi δ, Dfun v H lam s := by
        refine setIntegral_mono_on hsub.abs hD.integrableOn measurableSet_Ioi (fun s hs => ?_)
        exact h.w_dom lam (lt_trans hδ hs)
    _ ≤ ∫ s, Dfun v H lam s :=
        setIntegral_le_integral hD (Eventually.of_forall fun s => Dfun_nonneg h lam s)
    _ = _ := Dfun_integral h lam

end PlemeljHypE02_38

theorem tendsto_pvHilbert_E02_38 {v : ℝ → ℝ} {H A : ℝ} (hv : Continuous v) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0)
    (hhol : ∀ s t, |v s - v t| ≤ H * √|s - t|) (lam : ℝ) :
    Tendsto (fun δ : ℝ => ∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t)) (𝓝[>] (0:ℝ))
      (𝓝 (pvHilbert v lam)) := by
  have h : PlemeljHypE02_38 v H A := ⟨hv, hH, hA, hsupp, hhol⟩
  have hT : Tendsto (fun δ : ℝ => ∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ s in Ioi (0:ℝ), wfunE02_38 v lam s)) := by
    refine (h.tendsto_Ioi lam).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (h.fold_eq lam δ hδ).symm
  have := hT.limUnder_eq
  unfold pvHilbert
  rw [this]
  exact hT

theorem truncatedHilbert_tendsto_E02_38 {v : ℝ → ℝ} {H A : ℝ} (hv : Continuous v) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0)
    (hhol : ∀ s t, |v s - v t| ≤ H * √|s - t|) :
    ∀ lam : ℝ, ∃ T : ℝ, Tendsto (fun δ : ℝ => ∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t))
      (𝓝[>] (0:ℝ)) (𝓝 T) :=
  fun lam => ⟨pvHilbert v lam, tendsto_pvHilbert_E02_38 hv hH hA hsupp hhol lam⟩

theorem truncatedHilbert_bound_E02_38 {v : ℝ → ℝ} {H A : ℝ} (hv : Continuous v) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0)
    (hhol : ∀ s t, |v s - v t| ≤ H * √|s - t|) :
    ∃ M : ℝ, ∀ lam : ℝ, ∀ δ : ℝ, 0 < δ →
      |∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t)| ≤ M := by
  have h : PlemeljHypE02_38 v H A := ⟨hv, hH, hA, hsupp, hhol⟩
  refine ⟨H * √2 * (∫ s in Ioc (0:ℝ) 1, s ^ (-(1/2:ℝ))) + 2 * ∫ t, |v t|, fun lam δ hδ => ?_⟩
  rw [h.fold_eq lam δ hδ]
  exact h.bound_Ioi lam δ hδ


namespace PlemeljHypE02_38

variable {v : ℝ → ℝ} {H A : ℝ}

lemma kerR_int (h : PlemeljHypE02_38 v H A) (lam ε : ℝ) (hε : 0 < ε) :
    Integrable (fun s : ℝ => v (lam + s) * (s / (s ^ 2 + ε ^ 2))) := by
  have hm := h.cont.measurable
  refine Integrable.mono' (g := fun s => |v (lam + s)| * (1 / ε))
    ((h.integrable.comp_add_left lam).abs.mul_const (1 / ε))
    (by fun_prop : Measurable (fun s : ℝ => v (lam + s) * (s / (s ^ 2 + ε ^ 2)))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hp : 0 < s ^ 2 + ε ^ 2 := by positivity
  rw [abs_div, abs_of_pos hp, div_le_div_iff₀ hp hε]
  nlinarith [sq_nonneg (|s| - ε), sq_abs s]

lemma kerP_int (h : PlemeljHypE02_38 v H A) (lam ε : ℝ) (hε : 0 < ε) :
    Integrable (fun s : ℝ => v (lam + s) * (ε / (s ^ 2 + ε ^ 2))) := by
  have hm := h.cont.measurable
  refine Integrable.mono' (g := fun s => |v (lam + s)| * (1 / ε))
    ((h.integrable.comp_add_left lam).abs.mul_const (1 / ε))
    (by fun_prop : Measurable (fun s : ℝ => v (lam + s) * (ε / (s ^ 2 + ε ^ 2)))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hp : 0 < s ^ 2 + ε ^ 2 := by positivity
  rw [abs_div, abs_of_pos hp, abs_of_pos hε, div_le_div_iff₀ hp hε]
  nlinarith [sq_nonneg s]

lemma int_split_odd (f : ℝ → ℝ) (hf : Integrable f) :
    ∫ s, f s = ∫ s in Ioi (0:ℝ), (f s + f (-s)) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi hf.integrableOn hf.integrableOn]
  have := integral_comp_neg_Ioi (0:ℝ) f
  rw [neg_zero] at this
  rw [integral_add hf.integrableOn hf.comp_neg.integrableOn, this, add_comm]

lemma R_tendsto (h : PlemeljHypE02_38 v H A) (lam : ℝ) :
    Tendsto (fun ε : ℝ => ∫ s, v (lam + s) * (s / (s ^ 2 + ε ^ 2))) (𝓝[>] (0:ℝ))
      (𝓝 (-∫ s in Ioi (0:ℝ), wfunE02_38 v lam s)) := by
  have hm := h.cont.measurable
  have hw := h.w_integrableOn lam
  have key : Tendsto (fun ε : ℝ => ∫ s in Ioi (0:ℝ),
      (v (lam + s) - v (lam - s)) * (s / (s ^ 2 + ε ^ 2))) (𝓝[>] (0:ℝ))
      (𝓝 (∫ s in Ioi (0:ℝ), -wfunE02_38 v lam s)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖wfunE02_38 v lam s‖)
      (Eventually.of_forall fun ε => ?_) ?_ hw.norm ?_
    · exact (by fun_prop : Measurable (fun s : ℝ =>
        (v (lam + s) - v (lam - s)) * (s / (s ^ 2 + ε ^ 2)))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
      have hs' : (0:ℝ) < s := hs
      have hp : 0 < s ^ 2 + ε ^ 2 := by positivity
      have e : (v (lam + s) - v (lam - s)) * (s / (s ^ 2 + ε ^ 2))
          = -wfunE02_38 v lam s * (s ^ 2 / (s ^ 2 + ε ^ 2)) := by
        unfold wfunE02_38; field_simp; ring
      rw [e, norm_mul, norm_neg]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one hp]
      nlinarith [sq_nonneg ε]
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
      have hs' : (0:ℝ) < s := hs
      have hc : ContinuousAt (fun ε : ℝ => (v (lam + s) - v (lam - s)) * (s / (s ^ 2 + ε ^ 2))) 0 := by
        refine continuousAt_const.mul (continuousAt_const.div (by fun_prop) ?_)
        positivity
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      convert this using 2
      unfold wfunE02_38
      field_simp
      ring
  rw [integral_neg] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0:ℝ) < ε := hε
  rw [int_split_odd _ (h.kerR_int lam ε hε')]
  refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  rw [show lam + -s = lam - s by ring, neg_sq]
  ring

lemma P_tendsto (h : PlemeljHypE02_38 v H A) (lam : ℝ) :
    Tendsto (fun ε : ℝ => ∫ s, v (lam + s) * (ε / (s ^ 2 + ε ^ 2))) (𝓝[>] (0:ℝ))
      (𝓝 (v lam * Real.pi)) := by
  obtain ⟨B, hB0, hB⟩ := h.bounded
  have hm := h.cont.measurable
  have key : Tendsto (fun ε : ℝ => ∫ u, v (lam + ε * u) * (1 + u ^ 2)⁻¹) (𝓝[>] (0:ℝ))
      (𝓝 (∫ u, v lam * (1 + u ^ 2)⁻¹)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => B * (1 + u ^ 2)⁻¹)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => Eventually.of_forall fun u => ?_)
      (integrable_inv_one_add_sq.const_mul B) (Eventually.of_forall fun u => ?_)
    · exact (by fun_prop : Measurable (fun u : ℝ => v (lam + ε * u) * (1 + u ^ 2)⁻¹)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (1 + u ^ 2)⁻¹)]
      exact mul_le_mul_of_nonneg_right (hB _) (by positivity)
    · have hc : ContinuousAt (fun ε : ℝ => v (lam + ε * u) * (1 + u ^ 2)⁻¹) 0 :=
        ((h.cont.comp (continuous_const.add (continuous_id.mul continuous_const))).mul
          continuous_const).continuousAt
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using this
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0:ℝ) < ε := hε
  set g : ℝ → ℝ := fun s => v (lam + s) * (ε / (s ^ 2 + ε ^ 2)) with hg
  have h1 := Measure.integral_comp_mul_left g ε
  have h2 : ∀ u : ℝ, g (ε * u) = ε⁻¹ * (v (lam + ε * u) * (1 + u ^ 2)⁻¹) := by
    intro u
    simp only [hg]
    have : (ε * u) ^ 2 + ε ^ 2 = ε ^ 2 * (1 + u ^ 2) := by ring
    rw [this]
    field_simp
  simp only [h2] at h1
  rw [integral_const_mul, abs_of_pos (inv_pos.2 hε'), smul_eq_mul] at h1
  have h3 := mul_left_cancel₀ (inv_pos.2 hε').ne' h1
  exact h3.symm.trans rfl ▸ h3.symm

lemma pv_eq (h : PlemeljHypE02_38 v H A) (lam : ℝ) :
    pvHilbert v lam = ∫ s in Ioi (0:ℝ), wfunE02_38 v lam s := by
  have hT : Tendsto (fun δ : ℝ => ∫ t in {t : ℝ | δ < |t - lam|}, v t / (lam - t)) (𝓝[>] (0:ℝ))
      (𝓝 (∫ s in Ioi (0:ℝ), wfunE02_38 v lam s)) := by
    refine (h.tendsto_Ioi lam).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (h.fold_eq lam δ hδ).symm
  unfold pvHilbert
  exact hT.limUnder_eq

end PlemeljHypE02_38


theorem plemelj_boundary_E02_38 {v : ℝ → ℝ} {H A : ℝ} (hv : Continuous v) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0)
    (hhol : ∀ s t, |v s - v t| ≤ H * √|s - t|) :
    ∀ lam : ℝ, Tendsto
      (fun ε : ℝ => (1 / Real.pi : ℂ) * ∫ t, (v t : ℂ) / ((t : ℂ) - (lam + Complex.I * ε)))
      (𝓝[>] (0:ℝ))
      (𝓝 (((-(1 / Real.pi) * pvHilbert v lam : ℝ) : ℂ) + Complex.I * (v lam : ℂ))) := by
  intro lam
  have h : PlemeljHypE02_38 v H A := ⟨hv, hH, hA, hsupp, hhol⟩
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hR := (h.R_tendsto lam).const_mul (1 / Real.pi)
  have hP := (h.P_tendsto lam).const_mul (1 / Real.pi)
  rw [← h.pv_eq lam] at hR
  have e1 : 1 / Real.pi * -pvHilbert v lam = -(1 / Real.pi) * pvHilbert v lam := by ring
  have e2 : 1 / Real.pi * (v lam * Real.pi) = v lam := by field_simp
  rw [e1] at hR
  rw [e2] at hP
  have hlim := ((Complex.continuous_ofReal.tendsto _).comp hR).add
    (tendsto_const_nhds (x := Complex.I) |>.mul ((Complex.continuous_ofReal.tendsto _).comp hP))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : (0:ℝ) < ε := hε
  simp only [Function.comp]
  have hne : ∀ s : ℝ, (s : ℂ) - Complex.I * ε ≠ 0 := by
    intro s h0
    have := congrArg Complex.im h0
    simp at this
    exact hε'.ne' this
  have hsh : ∫ t : ℝ, (v t : ℂ) / ((t : ℂ) - (lam + Complex.I * ε))
      = ∫ s : ℝ, (v (lam + s) : ℂ) / ((s : ℂ) - Complex.I * ε) := by
    rw [← integral_add_left_eq_self (fun t : ℝ => (v t : ℂ) / ((t : ℂ) - (lam + Complex.I * ε))) lam]
    congr 1; ext s
    push_cast
    congr 1; ring
  have hpt : ∀ s : ℝ, (v (lam + s) : ℂ) / ((s : ℂ) - Complex.I * ε)
      = ((v (lam + s) * (s / (s ^ 2 + ε ^ 2)) : ℝ) : ℂ)
        + Complex.I * ((v (lam + s) * (ε / (s ^ 2 + ε ^ 2)) : ℝ) : ℂ) := by
    intro s
    have hp : ((s : ℂ) ^ 2 + (ε : ℂ) ^ 2) ≠ 0 := by
      have : (0:ℝ) < s ^ 2 + ε ^ 2 := by positivity
      exact_mod_cast this.ne'
    push_cast
    have := hne s
    field_simp
    linear_combination ((v (lam + s) : ℂ) * (ε : ℂ) ^ 2) * Complex.I_sq
  rw [hsh]
  simp only [hpt]
  rw [integral_add (h.kerR_int lam ε hε').ofReal ((h.kerP_int lam ε hε').ofReal.const_mul _),
    integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  push_cast
  ring

end NlsGge.SpectralFoundations
