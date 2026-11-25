import Mathlib
import NlsGge.Herglotz38.PlemeljBoundaryE02_38
import NlsGge.ThirdConsultation.I.I013Weights

                                                                                                      
                                                                                           
                                                                                                           
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.I.I013B

/-- A continuous `v` vanishing off `[-A,A]` is bounded. -/
theorem exists_abs_bound (v : ℝ → ℝ) (hv : Continuous v) (A : ℝ)
    (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |v t| ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn hv.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (-A) A
  · have h := hC t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · rw [hsupp t ht, abs_zero]
    exact le_max_right _ _

/-- Tail bound: for `2A+1 ≤ |x|`, `|∫_{|t-x|>δ} v t/(x-t) dt| · |x| ≤ 4AB`, uniformly in `δ`. -/
theorem truncHilbert_tail (v : ℝ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) (hB' : ∀ t, |v t| ≤ B)
    (δ x : ℝ) (hx : 2 * A + 1 ≤ |x|) :
    |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| * |x| ≤ 4 * A * B := by
  have hx0 : 0 < |x| := by linarith
  have hS : MeasurableSet {t : ℝ | δ < |t - x|} :=
    measurableSet_lt measurable_const ((continuous_id.sub continuous_const).abs.measurable)
  have hc0 : 0 ≤ 2 * B / |x| := by positivity
  have hgi : Integrable ((Icc (-A) A).indicator (fun _ : ℝ => 2 * B / |x|)) := by
    refine (integrable_indicator_iff measurableSet_Icc).2 ?_
    exact integrableOn_const (isCompact_Icc.measure_lt_top).ne
  have hbound : ‖∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)‖ ≤ 2 * A * (2 * B / |x|) := by
    rw [← integral_indicator hS]
    calc ‖∫ t, {t : ℝ | δ < |t - x|}.indicator (fun t => v t / (x - t)) t‖
        ≤ ∫ t, (Icc (-A) A).indicator (fun _ : ℝ => 2 * B / |x|) t := by
          apply norm_integral_le_of_norm_le hgi
          refine Eventually.of_forall fun t => ?_
          by_cases htS : t ∈ {t : ℝ | δ < |t - x|}
          · rw [indicator_of_mem htS]
            by_cases ht : t ∈ Icc (-A) A
            · rw [indicator_of_mem ht, Real.norm_eq_abs, abs_div]
              have hxt : |x| ≤ 2 * |x - t| := by
                have h1 : |x| ≤ |x - t| + |t| := by
                  have := abs_add_le (x - t) t
                  rwa [sub_add_cancel] at this
                have h2 : |t| ≤ A := abs_le.mpr ht
                linarith
              have hpos : 0 < |x - t| := by linarith
              rw [div_le_div_iff₀ hpos hx0]
              nlinarith [mul_le_mul_of_nonneg_right (hB' t) hx0.le,
                mul_nonneg hB (show (0:ℝ) ≤ 2 * |x - t| - |x| by linarith)]
            · rw [indicator_of_notMem ht, hsupp t ht]
              simp
          · rw [indicator_of_notMem htS, norm_zero]
            exact indicator_nonneg (fun _ _ => hc0) t
      _ = 2 * A * (2 * B / |x|) := by
          rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith),
            smul_eq_mul]
          ring
  rw [Real.norm_eq_abs] at hbound
  calc |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| * |x|
      ≤ 2 * A * (2 * B / |x|) * |x| := mul_le_mul_of_nonneg_right hbound hx0.le
    _ = 4 * A * B := by field_simp <;> ring

/-- Uniform square-weighted bound for the truncations, given a uniform pointwise bound `M`. -/
theorem truncHilbert_sq_weight (v : ℝ → ℝ) (M A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) (hB' : ∀ t, |v t| ≤ B)
    (hM : ∀ x δ : ℝ, 0 < δ → |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| ≤ M)
    (δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    (∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)) ^ 2 * (1 + x ^ 2) ≤
      M ^ 2 * (1 + (2 * A + 1) ^ 2) + 2 * (4 * A * B) ^ 2 :=
  NlsGge.ThirdConsultation.I.I013A.sq_weight_bound
    (fun y => ∫ t in {t : ℝ | δ < |t - y|}, v t / (y - t)) M (4 * A * B) (2 * A + 1)
    (by linarith) (fun y _ => hM y δ hδ)
    (fun y hy => truncHilbert_tail v A B hA hB hsupp hB' δ y hy) x

/-- Pointwise PV bound, from the limit of the truncations. -/
theorem pv_abs_le (v : ℝ → ℝ) (H A M : ℝ) (hv : Continuous v) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0)
    (hhol : ∀ s t, |v s - v t| ≤ H * Real.sqrt |s - t|)
    (hM : ∀ x δ : ℝ, 0 < δ → |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| ≤ M) (y : ℝ) :
    |pvHilbert v y| ≤ M :=
  le_of_tendsto (tendsto_pvHilbert_E02_38 hv hH hA hsupp hhol y).abs
    (eventually_nhdsWithin_of_forall fun δ hδ => hM y δ hδ)

/-- Pointwise PV tail bound, from the limit of the tail bounds. -/
theorem pv_tail_le (v : ℝ → ℝ) (H A B : ℝ) (hv : Continuous v) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) (hB' : ∀ t, |v t| ≤ B)
    (hhol : ∀ s t, |v s - v t| ≤ H * Real.sqrt |s - t|) (y : ℝ) (hy : 2 * A + 1 ≤ |y|) :
    |pvHilbert v y| * |y| ≤ 4 * A * B :=
  le_of_tendsto ((tendsto_pvHilbert_E02_38 hv hH hA hsupp hhol y).abs.mul_const |y|)
    (eventually_nhdsWithin_of_forall fun δ _ => truncHilbert_tail v A B hA hB hsupp hB' δ y hy)

/-- Square-weighted bound for the actual PV transform, with the same constant as the truncations. -/
theorem pv_sq_weight (v : ℝ → ℝ) (H M A B : ℝ) (hv : Continuous v) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0) (hB' : ∀ t, |v t| ≤ B)
    (hhol : ∀ s t, |v s - v t| ≤ H * Real.sqrt |s - t|)
    (hM : ∀ x δ : ℝ, 0 < δ → |∫ t in {t : ℝ | δ < |t - x|}, v t / (x - t)| ≤ M) (x : ℝ) :
    pvHilbert v x ^ 2 * (1 + x ^ 2) ≤ M ^ 2 * (1 + (2 * A + 1) ^ 2) + 2 * (4 * A * B) ^ 2 :=
  NlsGge.ThirdConsultation.I.I013A.sq_weight_bound (pvHilbert v) M (4 * A * B) (2 * A + 1)
    (by linarith) (fun y _ => pv_abs_le v H A M hv hH hA hsupp hhol hM y)
    (fun y hy => pv_tail_le v H A B hv hH hA hB hsupp hB' hhol y hy) x

end NlsGge.ThirdConsultation.I.I013B

end
