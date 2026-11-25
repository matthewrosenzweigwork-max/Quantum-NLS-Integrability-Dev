import NlsGge.Spectral.ActualConvexMomentE02_38
import NlsGge.Spectral.ActualActionSumE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # H∞: the boundary Hilbert formula for infinite-gap H¹ fields (campaign 38, F04 route (ii))

v2 (A:eq:Hilbert) `λ - p(λ) = (1/π) pv∫ v(t)/(λ - t) dt`, proved for every H¹ field by splitting `v` at a band
cut `L` (where `v = 0` on `L - d < |t| < L + d`). The compact part `v ∘ clamp_L` uses the finite-gap Plemelj formula.
The far part is supported at distance `≥ d` from `[-L, L]`, so its Cauchy integral is continuous up to the
boundary by dominated convergence. -/

/-- `clamp_L t = max (-L) (min t L)`. -/
def clampE02_38 (L t : ℝ) : ℝ := max (-L) (min t L)

theorem clampE02_38_mem (L : ℝ) (hL : 0 ≤ L) (t : ℝ) : clampE02_38 L t ∈ Icc (-L) L :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clampE02_38_of_mem (L t : ℝ) (ht : t ∈ Icc (-L) L) : clampE02_38 L t = t := by
  unfold clampE02_38; rw [min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_clampE02_38 (L : ℝ) : Continuous (clampE02_38 L) := by
  unfold clampE02_38; fun_prop

theorem abs_clampE02_38_sub_le (L : ℝ) (s t : ℝ) :
    |clampE02_38 L s - clampE02_38 L t| ≤ |s - t| := by
  unfold clampE02_38
  have h1 := abs_max_sub_max_le_max (-L) (min s L) (-L) (min t L)
  have h2 := abs_min_sub_min_le_max s L t L
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min s L - min t L))] at h1
  rw [max_eq_left (abs_nonneg (s - t))] at h2
  exact h1.trans h2

theorem clampE02_38_of_not_mem (L t : ℝ) (hL : 0 ≤ L) (ht : L < |t|) :
    clampE02_38 L t = L ∨ clampE02_38 L t = -L := by
  unfold clampE02_38
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht
    left; rw [min_eq_right ht.le, max_eq_right (by linarith)]
  · rw [abs_of_neg h] at ht
    right; rw [min_eq_left (by linarith), max_eq_left (by linarith)]

/-- The compact part `v_L = v ∘ clamp_L` (equal to `v` on `[-L, L]` and to `0` outside when `v(±L) = 0`). -/
def gapCutE02_38 (u : PhysicalL2) (L : ℝ) : ℝ → ℝ :=
  fun t => actualGapHeightE02_38 u (clampE02_38 L t)

/-- The far part `v - v_L`. -/
def gapTailE02_38 (u : PhysicalL2) (L : ℝ) : ℝ → ℝ :=
  fun t => actualGapHeightE02_38 u t - gapCutE02_38 u L t

/-- Band-cut hypothesis: `v = 0` on `L - d < |t| < L + d`. -/
def IsBandCutE02_38 (u : PhysicalL2) (L d : ℝ) : Prop :=
  0 < d ∧ d ≤ L ∧ ∀ t, L - d < |t| → |t| < L + d → actualGapHeightE02_38 u t = 0

section
variable {u : PhysicalL2} {L d : ℝ}

theorem IsBandCutE02_38.v_pm (h : IsBandCutE02_38 u L d) :
    actualGapHeightE02_38 u L = 0 ∧ actualGapHeightE02_38 u (-L) = 0 := by
  obtain ⟨hd, hdL, hz⟩ := h
  have hL : 0 ≤ L := by linarith
  refine ⟨hz L ?_ ?_, hz (-L) ?_ ?_⟩ <;> simp [abs_of_nonneg hL] <;> linarith

theorem IsBandCutE02_38.cut_eq_of_mem (_h : IsBandCutE02_38 u L d) (t : ℝ) (ht : |t| ≤ L) :
    gapCutE02_38 u L t = actualGapHeightE02_38 u t := by
  unfold gapCutE02_38; rw [clampE02_38_of_mem L t (abs_le.mp ht)]

theorem IsBandCutE02_38.cut_eq_zero (h : IsBandCutE02_38 u L d) (t : ℝ) (ht : L - d < |t|) :
    gapCutE02_38 u L t = 0 := by
  have hL : 0 ≤ L := by linarith [h.1, h.2.1]
  by_cases h1 : |t| ≤ L
  · rw [h.cut_eq_of_mem t h1]; exact h.2.2 t ht (by linarith [h.1])
  · push Not at h1
    unfold gapCutE02_38
    rcases clampE02_38_of_not_mem L t hL h1 with h2 | h2 <;> rw [h2]
    · exact h.v_pm.1
    · exact h.v_pm.2

theorem IsBandCutE02_38.tail_eq_zero (h : IsBandCutE02_38 u L d) (t : ℝ) (ht : |t| < L + d) :
    gapTailE02_38 u L t = 0 := by
  unfold gapTailE02_38
  by_cases h1 : |t| ≤ L
  · rw [h.cut_eq_of_mem t h1, sub_self]
  · push Not at h1
    rw [h.cut_eq_zero t (by linarith [h.1]), h.2.2 t (by linarith [h.1]) ht, sub_zero]

theorem IsBandCutE02_38.tail_eq (h : IsBandCutE02_38 u L d) (t : ℝ) (ht : L < |t|) :
    gapTailE02_38 u L t = actualGapHeightE02_38 u t := by
  unfold gapTailE02_38; rw [h.cut_eq_zero t (by linarith [h.1]), sub_zero]

theorem IsBandCutE02_38.tail_le (h : IsBandCutE02_38 u L d) (t : ℝ) :
    0 ≤ gapTailE02_38 u L t ∧ gapTailE02_38 u L t ≤ actualGapHeightE02_38 u t := by
  by_cases h1 : L < |t|
  · rw [h.tail_eq t h1]; exact ⟨actualGapHeightE02_38_nonneg u t, le_rfl⟩
  · push Not at h1
    rw [h.tail_eq_zero t (by linarith [h.1])]
    exact ⟨le_rfl, actualGapHeightE02_38_nonneg u t⟩

theorem IsBandCutE02_38.cut_supp (h : IsBandCutE02_38 u L d) :
    ∀ t, t ∉ Icc (-L) L → gapCutE02_38 u L t = 0 := by
  intro t ht
  apply h.cut_eq_zero
  have : L < |t| := by
    by_contra hc; push Not at hc; exact ht (abs_le.mp hc)
  linarith [h.1]

end

theorem continuous_gapCutE02_38 (u : PhysicalL2) (L : ℝ) : Continuous (gapCutE02_38 u L) :=
  (continuous_actualGapHeightE02_38 u).comp (continuous_clampE02_38 L)

theorem gapCut_holder_E02_38 (u : PhysicalL2) (L : ℝ) (hL : 0 ≤ L) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ s t, |gapCutE02_38 u L s - gapCutE02_38 u L t| ≤ H * Real.sqrt |s - t| := by
  obtain ⟨H0, hH0⟩ := actualGapHeight_holder_E02_38 u L
  refine ⟨|H0|, abs_nonneg _, fun s t => ?_⟩
  have h1 := hH0 _ (clampE02_38_mem L hL s) _ (clampE02_38_mem L hL t)
  refine h1.trans (mul_le_mul (le_abs_self _) (Real.sqrt_le_sqrt (abs_clampE02_38_sub_le L s t))
    (Real.sqrt_nonneg _) (abs_nonneg _))

theorem continuous_gapTailE02_38 (u : PhysicalL2) (L : ℝ) : Continuous (gapTailE02_38 u L) :=
  (continuous_actualGapHeightE02_38 u).sub (continuous_gapCutE02_38 u L)

theorem integrable_gapTailE02_38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (L d : ℝ) (h : IsBandCutE02_38 u L d) : Integrable (gapTailE02_38 u L) := by
  have hv := (actualGapHeight_integral_eq_normSq_E02_38 u hu).1
  refine hv.mono' (continuous_gapTailE02_38 u L).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (h.tail_le t).1]
  exact (h.tail_le t).2

theorem tail_dist_E02_38 {u : PhysicalL2} {L d : ℝ} (h : IsBandCutE02_38 u L d) (l : ℝ) (hl : |l| ≤ L)
    (t : ℝ) (ht : gapTailE02_38 u L t ≠ 0) : d ≤ |t - l| := by
  have h1 : L + d ≤ |t| := by
    by_contra hc; push Not at hc; exact ht (h.tail_eq_zero t hc)
  have h2 := abs_sub_abs_le_abs_sub t l
  linarith

theorem norm_tail_div_le_E02_38 {u : PhysicalL2} {L d : ℝ} (h : IsBandCutE02_38 u L d) (l : ℝ)
    (hl : |l| ≤ L) (t : ℝ) (z : ℂ) (hz : z.re = l) :
    ‖((gapTailE02_38 u L t : ℝ) : ℂ) / ((t:ℂ) - z)‖ ≤ gapTailE02_38 u L t / d := by
  by_cases ht : gapTailE02_38 u L t = 0
  · simp [ht]
  have hd := tail_dist_E02_38 h l hl t ht
  have hd0 : 0 < d := h.1
  have hre : |t - l| ≤ ‖(t:ℂ) - z‖ := by
    have := Complex.abs_re_le_norm ((t:ℂ) - z)
    simpa [hz] using this
  have hpos : 0 < ‖(t:ℂ) - z‖ := by linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.tail_le t).1]
  exact div_le_div_of_nonneg_left (h.tail_le t).1 hd0 (le_trans hd hre)

/-- **H∞ (A:eq:Hilbert, split form) for every H¹ field.** At a band cut `L` and any `|l| ≤ L`,
`l - p(l) = (1/π) (pv∫ v_L(t)/(l - t) dt + ∫ (v - v_L)(t)/(l - t) dt)`. -/
theorem realPart_sub_split_E02_38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (L d : ℝ) (h : IsBandCutE02_38 u L d) (l : ℝ) (hl : |l| ≤ L) :
    l - actualQuasimomentumRealPartE02_38 u l =
      (1/Real.pi) * (pvHilbert (gapCutE02_38 u L) l + ∫ t, gapTailE02_38 u L t / (l - t)) := by
  set v := actualGapHeightE02_38 u
  set vL := gapCutE02_38 u L
  set w := gapTailE02_38 u L
  have hL : 0 ≤ L := by linarith [h.1, h.2.1]
  have hd0 : 0 < d := h.1
  obtain ⟨H, hH, hhol⟩ := gapCut_holder_E02_38 u L hL
  have hvLc : Continuous vL := continuous_gapCutE02_38 u L
  have hwc : Continuous w := continuous_gapTailE02_38 u L
  have hwi : Integrable w := integrable_gapTailE02_38 u hu L d h
  have hvLcs : HasCompactSupport vL :=
    HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun t ht => h.cut_supp t ht
  have hvLi : Integrable vL := hvLc.integrable_of_hasCompactSupport hvLcs
  have hpl := plemelj_boundary_E02_38 hvLc hH hL h.cut_supp hhol l
  set z : ℝ → ℂ := fun ε => (l:ℂ) + Complex.I*(ε:ℂ)
  have hzre : ∀ ε, (z ε).re = l := fun ε => by simp [z]
  have hzim : ∀ ε, (z ε).im = ε := fun ε => by simp [z]
  -- far part
  have hfar : Tendsto (fun ε : ℝ => (1/Real.pi : ℂ) * ∫ t, (w t : ℂ) / ((t:ℂ) - z ε)) (𝓝[>] 0)
      (𝓝 ((1/Real.pi : ℂ) * ∫ t, (w t : ℂ) / ((t:ℂ) - (l:ℂ)))) := by
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun t => w t / d) ?_ ?_
      (hwi.div_const d) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hne : ∀ t : ℝ, (t:ℂ) - z ε ≠ 0 := by
        intro t h0
        have := congrArg Complex.im h0
        simp [z] at this
        exact (ne_of_gt (show (0:ℝ) < ε from hε)) this
      exact (((Complex.continuous_ofReal.comp hwc)).div
        (Complex.continuous_ofReal.sub continuous_const) hne).aestronglyMeasurable
    · exact Eventually.of_forall fun ε => Eventually.of_forall fun t =>
        norm_tail_div_le_E02_38 h l hl t (z ε) (hzre ε)
    · refine Eventually.of_forall fun t => ?_
      by_cases ht : w t = 0
      · simp [ht]
      have htl : (t:ℂ) - (l:ℂ) ≠ 0 := by
        have := tail_dist_E02_38 h l hl t ht
        intro h0
        have h1 : t - l = 0 := by exact_mod_cast h0
        rw [h1, abs_zero] at this; linarith
      have hc : ContinuousAt (fun ε : ℝ => (w t : ℂ) / ((t:ℂ) - z ε)) 0 := by
        apply ContinuousAt.div continuousAt_const (by fun_prop)
        simpa [z] using htl
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa [z] using this
  -- Herglotz splitting
  have hherg := actualQuasimomentum_herglotz_E02_38 u hu
  have hk := (tendsto_actualQuasimomentumBoundaryE02_38 u l).comp (vertical_tendsto_upper_E02_38 l)
  have hpath : Tendsto z (𝓝[>] 0) (𝓝 (l:ℂ)) := by
    have hc : Continuous z := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa [z] using this
  have hdiff := hk.sub hpath
  have heq : (fun ε : ℝ => actualQuasimomentumE02_38 u (z ε) - z ε) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ((1/Real.pi : ℂ) * ∫ t, (vL t : ℂ) / ((t:ℂ) - z ε)) +
        ((1/Real.pi : ℂ) * ∫ t, (w t : ℂ) / ((t:ℂ) - z ε))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    have hz : 0 < (z ε).im := by rw [hzim]; exact hε'
    rw [(hherg _ hz).2, add_sub_cancel_left, ← mul_add]
    have hn : ∀ t : ℝ, ε ≤ ‖(t:ℂ) - z ε‖ := by
      intro t
      have := Complex.abs_im_le_norm ((t:ℂ) - z ε)
      simp [z] at this
      rwa [abs_of_pos hε'] at this
    have hint1 : Integrable (fun t => (vL t : ℂ) / ((t:ℂ) - z ε)) := by
      refine (hvLi.norm.div_const ε).mono' ?_ (Eventually.of_forall fun t => ?_)
      · have hne : ∀ t : ℝ, (t:ℂ) - z ε ≠ 0 := fun t h0 => by
          have := hn t; rw [h0, norm_zero] at this; linarith
        exact ((Complex.continuous_ofReal.comp hvLc).div
          (Complex.continuous_ofReal.sub continuous_const) hne).aestronglyMeasurable
      · rw [norm_div, Complex.norm_real]
        exact div_le_div_of_nonneg_left (norm_nonneg _) hε' (hn t)
    have hint2 : Integrable (fun t => (w t : ℂ) / ((t:ℂ) - z ε)) := by
      refine (hwi.div_const d).mono' ?_ (Eventually.of_forall fun t => ?_)
      · have hne : ∀ t : ℝ, (t:ℂ) - z ε ≠ 0 := fun t h0 => by
          have := hn t; rw [h0, norm_zero] at this; linarith
        exact ((Complex.continuous_ofReal.comp hwc).div
          (Complex.continuous_ofReal.sub continuous_const) hne).aestronglyMeasurable
      · exact norm_tail_div_le_E02_38 h l hl t (z ε) (hzre ε)
    rw [← integral_add hint1 hint2]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    have : actualGapHeightE02_38 u t = vL t + w t := by simp only [w, gapTailE02_38]; ring
    rw [this, Complex.ofReal_add, add_div]
  have hpl' : Tendsto (fun ε : ℝ => (1/Real.pi : ℂ) * ∫ t, (vL t : ℂ) / ((t:ℂ) - z ε)) (𝓝[>] 0)
      (𝓝 (((-(1 / Real.pi) * pvHilbert vL l : ℝ) : ℂ) + Complex.I * (vL l : ℂ))) := hpl
  have hlim := tendsto_nhds_unique (hdiff.congr' heq) (hpl'.add hfar)
  have hre := congrArg Complex.re hlim
  have hwre : (∫ t, (w t : ℂ) / ((t:ℂ) - (l:ℂ))).re = ∫ t, w t / (t - l) := by
    have : (fun t => (w t : ℂ) / ((t:ℂ) - (l:ℂ))) = fun t => ((w t / (t - l) : ℝ) : ℂ) := by
      funext t; push_cast; rfl
    rw [this, integral_complex_ofReal, Complex.ofReal_re]
  have hneg : ∫ t, w t / (l - t) = -∫ t, w t / (t - l) := by
    rw [← integral_neg]; congr 1; funext t
    rw [show l - t = -(t - l) by ring, div_neg]
  simp only [Function.comp, Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, sub_zero, mul_zero] at hre
  have hc1 : ((1/Real.pi : ℂ)).re = 1/Real.pi := by simp
  have hc2 : ((1/Real.pi : ℂ)).im = 0 := by simp
  rw [hc1, hc2, hwre] at hre
  have : actualQuasimomentumRealPartE02_38 u l = (actualQuasimomentumBoundaryE02_38 u l).re := rfl
  rw [this, hneg]
  simp only [zero_mul, sub_zero] at hre
  linarith

end NlsGge.SpectralFoundations
end
