import Mathlib
set_option autoImplicit false
open Set Filter Topology Metric
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G3005C4
noncomputable section

theorem ext_right (f : ℝ → ℂ) (L : ℂ) (hf : ContinuousOn f (Ico 0 1))
    (hL : Tendsto f (𝓝[<] (1:ℝ)) (𝓝 L)) :
    ContinuousOn (fun t : ℝ => if t = 1 then L else f t) (Icc 0 1) := by
  intro t ht
  by_cases h1 : t = 1
  · subst h1
    have hA : Tendsto (fun t : ℝ => if t = 1 then L else f t) (𝓝[Iio (1:ℝ)] 1) (𝓝 L) := by
      refine hL.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hne : s ≠ 1 := ne_of_lt (show s < 1 from hs)
      simp [hne]
    have hsub : Icc (0:ℝ) 1 ⊆ Iio 1 ∪ {1} := fun x hx => by
      rcases lt_or_eq_of_le hx.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
    rw [nhdsWithin_union, nhdsWithin_singleton]
    simp only [if_true]
    exact Tendsto.sup hA (tendsto_pure_left.2 fun s hs => by simpa using mem_of_mem_nhds hs)
  · have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
    have hmem : Ico (0:ℝ) 1 ∈ 𝓝[Icc 0 1] t :=
      mem_nhdsWithin.2 ⟨Iio 1, isOpen_Iio, ht1, fun x hx => ⟨hx.2.1, hx.1⟩⟩
    have hfa : ContinuousWithinAt f (Icc 0 1) t :=
      (hf t ⟨ht.1, ht1⟩).mono_of_mem_nhdsWithin hmem
    refine hfa.congr_of_eventuallyEq ?_ (by simp [h1])
    exact ((eventually_ne_nhds h1).filter_mono nhdsWithin_le_nhds).mono (fun s hs => by simp [hs])

theorem ext_left (f : ℝ → ℂ) (L : ℂ) (hf : ContinuousOn f (Ioc 0 1))
    (hL : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 L)) :
    ContinuousOn (fun t : ℝ => if t = 0 then L else f t) (Icc 0 1) := by
  intro t ht
  by_cases h0 : t = 0
  · subst h0
    have hA : Tendsto (fun t : ℝ => if t = 0 then L else f t) (𝓝[Ioi (0:ℝ)] 0) (𝓝 L) := by
      refine hL.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hne : s ≠ 0 := ne_of_gt (show 0 < s from hs)
      simp [hne]
    have hsub : Icc (0:ℝ) 1 ⊆ Ioi 0 ∪ {0} := fun x hx => by
      rcases lt_or_eq_of_le hx.1 with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
    rw [nhdsWithin_union, nhdsWithin_singleton]
    simp only [if_true]
    exact Tendsto.sup hA (tendsto_pure_left.2 fun s hs => by simpa using mem_of_mem_nhds hs)
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h0)
    have hmem : Ioc (0:ℝ) 1 ∈ 𝓝[Icc 0 1] t :=
      mem_nhdsWithin.2 ⟨Ioi 0, isOpen_Ioi, ht0, fun x hx => ⟨hx.1, hx.2.2⟩⟩
    have hfa : ContinuousWithinAt f (Icc 0 1) t :=
      (hf t ⟨ht0, ht.2⟩).mono_of_mem_nhdsWithin hmem
    refine hfa.congr_of_eventuallyEq ?_ (by simp [h0])
    exact ((eventually_ne_nhds h0).filter_mono nhdsWithin_le_nhds).mono (fun s hs => by simp [hs])

theorem sq_tendsto_zero (s q : ℝ → ℂ) (F : Filter ℝ) (hq : Tendsto q F (𝓝 0))
    (hsq : ∀ᶠ t in F, s t ^ 2 = q t) : Tendsto s F (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun t => Real.sqrt ‖q t‖) F (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_zero_iff_norm_tendsto_zero.1 hq)
    rw [Real.sqrt_zero] at this
    exact this
  refine h1.congr' ?_
  filter_upwards [hsq] with t ht
  rw [← ht, norm_pow, Real.sqrt_sq (norm_nonneg _)]

theorem tend_of_ball (s q : ℝ → ℂ) (r : ℂ) (F : Filter ℝ) (hr : r ≠ 0)
    (hq : Tendsto q F (𝓝 (r ^ 2)))
    (hev : ∀ᶠ t in F, s t ∈ ball r ‖r‖ ∧ s t ^ 2 = q t) : Tendsto s F (𝓝 r) := by
  have hη : 0 < ‖r‖ := norm_pos_iff.2 hr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hq' : Tendsto (fun t => ‖q t - r ^ 2‖ / ‖r‖) F (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 hq).div_const ‖r‖)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hq'
  filter_upwards [hev] with t ⟨hb, hsq⟩
  have hb' : ‖s t - r‖ < ‖r‖ := by simpa [dist_eq_norm] using hb
  have h2 : ‖r‖ < ‖s t + r‖ := by
    have : ‖(2:ℂ) * r‖ ≤ ‖s t + r‖ + ‖s t - r‖ := by
      calc ‖(2:ℂ) * r‖ = ‖(s t + r) - (s t - r)‖ := by ring_nf
        _ ≤ ‖s t + r‖ + ‖s t - r‖ := norm_sub_le _ _
    have h3 : ‖(2:ℂ) * r‖ = 2 * ‖r‖ := by rw [norm_mul]; simp
    linarith
  have hfac : q t - r ^ 2 = (s t - r) * (s t + r) := by rw [← hsq]; ring
  rw [le_div_iff₀ hη, hfac, norm_mul]
  exact mul_le_mul_of_nonneg_left h2.le (norm_nonneg _)

theorem sheet_limit (s q : ℝ → ℂ) (r : ℂ) (hs : ContinuousOn s (Ico 0 1))
    (hq : ContinuousOn q (Icc 0 1)) (hsq : ∀ t ∈ Ico (0:ℝ) 1, s t ^ 2 = q t) (hr : r ^ 2 = q 1) :
    ∃ e : ℂ, (e = 1 ∨ e = -1) ∧ Tendsto (fun t => e * s t) (𝓝[<] (1:ℝ)) (𝓝 r) := by
  have hIoo : Ioo (0:ℝ) 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT zero_lt_one
  have hqt : Tendsto q (𝓝[<] (1:ℝ)) (𝓝 (q 1)) := by
    have h := (hq 1 ⟨zero_le_one, le_rfl⟩).mono Ioo_subset_Icc_self
    rwa [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT zero_lt_one] at h
  have hsqF : ∀ᶠ t in 𝓝[<] (1:ℝ), s t ^ 2 = q t :=
    Filter.mem_of_superset hIoo (fun t ht => hsq t ⟨ht.1.le, ht.2⟩)
  by_cases hr0 : r = 0
  · refine ⟨1, Or.inl rfl, ?_⟩
    subst hr0
    have h0 : q 1 = 0 := by rw [← hr]; ring
    rw [h0] at hqt
    simpa using sq_tendsto_zero s q _ hqt hsqF
  · have hη : 0 < ‖r‖ := norm_pos_iff.2 hr0
    have hqr : Tendsto q (𝓝[<] (1:ℝ)) (𝓝 (r ^ 2)) := by rw [hr]; exact hqt
    have hev : ∀ᶠ t in 𝓝[<] (1:ℝ), ‖q t - r ^ 2‖ < ‖r‖ ^ 2 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hqr).eventually (gt_mem_nhds (by positivity : (0:ℝ) < ‖r‖ ^ 2))
      exact this
    have hev' : ∀ᶠ t in 𝓝[<] (1:ℝ), ‖q t - r ^ 2‖ < ‖r‖ ^ 2 ∧ (t ∈ Ioo (0:ℝ) 1 ∧ s t ^ 2 = q t) :=
      hev.and ((show ∀ᶠ t in 𝓝[<] (1:ℝ), t ∈ Ioo (0:ℝ) 1 from hIoo).and hsqF)
    obtain ⟨l, hl, hsub0⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev'
    have hsub : ∀ t ∈ Ioo l 1, ‖q t - r ^ 2‖ < ‖r‖ ^ 2 ∧ (t ∈ Ioo (0:ℝ) 1 ∧ s t ^ 2 = q t) :=
      fun t ht => hsub0 ht
    have hI : IsPreconnected (Ioo l 1) := isPreconnected_Ioo
    have hsc : ContinuousOn s (Ioo l 1) := hs.mono (fun t ht => ⟨((hsub t ht).2.1).1.le, ht.2⟩)
    have himg : IsPreconnected (s '' Ioo l 1) := hI.image s hsc
    have hcov : s '' Ioo l 1 ⊆ ball r ‖r‖ ∪ ball (-r) ‖r‖ := by
      rintro _ ⟨t, ht, rfl⟩
      obtain ⟨hq1, -, hsqt⟩ := hsub t ht
      by_contra hcon
      simp only [mem_union, mem_ball, dist_eq_norm, not_or, not_lt] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have h2' : ‖r‖ ≤ ‖s t + r‖ := by simpa [sub_neg_eq_add] using h2
      have hfac : q t - r ^ 2 = (s t - r) * (s t + r) := by rw [← hsqt]; ring
      have : ‖r‖ ^ 2 ≤ ‖q t - r ^ 2‖ := by
        rw [hfac, norm_mul, sq]; exact mul_le_mul h1 h2' hη.le (norm_nonneg _)
      linarith
    have hdisj : Disjoint (ball r ‖r‖) (ball (-r) ‖r‖) := by
      apply ball_disjoint_ball
      have h3 : ‖(2:ℂ) * r‖ = 2 * ‖r‖ := by rw [norm_mul]; simp
      have h4 : dist r (-r) = ‖(2:ℂ) * r‖ := by
        rw [dist_eq_norm, sub_neg_eq_add]; congr 1; ring
      rw [h4, h3]; linarith
    have hmemF : Ioo l 1 ∈ 𝓝[<] (1:ℝ) := Ioo_mem_nhdsLT hl
    rcases himg.subset_or_subset isOpen_ball isOpen_ball hdisj hcov with hA | hB
    · refine ⟨1, Or.inl rfl, ?_⟩
      simp only [one_mul]
      refine tend_of_ball s q r _ hr0 hqr ?_
      filter_upwards [hmemF, hsqF] with t ht hst
      exact ⟨hA ⟨t, ht, rfl⟩, hst⟩
    · refine ⟨-1, Or.inr rfl, ?_⟩
      refine tend_of_ball (fun t => -1 * s t) q r _ hr0 hqr ?_
      filter_upwards [hmemF, hsqF] with t ht hst
      refine ⟨?_, by rw [← hst]; ring⟩
      have := hB ⟨t, ht, rfl⟩
      simp only [mem_ball, dist_eq_norm] at this ⊢
      have e : -1 * s t - r = -(s t - (-r)) := by ring
      rw [e, norm_neg]; exact this

end
end G3005C4
end NlsGge.GKDefinitionDesign
