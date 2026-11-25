import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.Spectral.ActualQuasimomentumDecayE02_38
import NlsGge.Herglotz38.PlemeljBoundaryE02_38
import NlsGge.Herglotz38.TruncatedSymmetrizationE02_38
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # S02 (campaign 38): v2 A:lem:convex for finite-gap fields

Route departure (recorded in STATUS_E02_38.md): A:eq:Hilbert as a pointwise principal value with
uniformly bounded truncations (Hölder-½ `v`), dominated convergence in the truncation, and Fubini
on `{|λ-t| > δ}` (`truncatedHilbert_pairing_nonneg_E02_38`). -/

/-- Global Hölder bound from a bound on `[-A,A]`, for a function vanishing on `|x| > A'` with
`0 ≤ A' < A` (clamping is 1-Lipschitz and preserves the values). -/
theorem holder_global_of_Icc_E02_38 (v : ℝ → ℝ) (A A' H : ℝ) (hH : 0 ≤ H) (hA' : 0 ≤ A')
    (hAA : A' < A) (hzero : ∀ x, A' < |x| → v x = 0)
    (hloc : ∀ s ∈ Icc (-A) A, ∀ t ∈ Icc (-A) A, |v s - v t| ≤ H * Real.sqrt |s - t|) :
    ∀ s t, |v s - v t| ≤ H * Real.sqrt |s - t| := by
  let c : ℝ → ℝ := fun s => max (-A) (min s A)
  have hc : ∀ s, c s ∈ Icc (-A) A := fun s =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hcv : ∀ s, v (c s) = v s := by
    intro s
    by_cases hs : s ∈ Icc (-A) A
    · have : c s = s := by simp only [c]; rw [min_eq_left hs.2, max_eq_right hs.1]
      rw [this]
    · simp only [mem_Icc, not_and_or, not_le] at hs
      have h1 : v s = 0 := hzero s (by
        rcases hs with hs | hs
        · exact lt_of_lt_of_le (by linarith) (neg_le_abs s)
        · exact lt_of_lt_of_le (by linarith) (le_abs_self s))
      have h2 : v (c s) = 0 := by
        apply hzero
        rcases hs with hs | hs
        · have : c s = -A := by
            simp only [c]; rw [min_eq_left (by linarith), max_eq_left hs.le]
          rw [this, abs_neg, abs_of_pos (by linarith)]; exact hAA
        · have : c s = A := by
            simp only [c]; rw [min_eq_right hs.le, max_eq_right (by linarith)]
          rw [this, abs_of_pos (by linarith)]; exact hAA
      rw [h1, h2]
  have hlip : ∀ s t, |c s - c t| ≤ |s - t| := by
    intro s t
    calc |c s - c t| = |max (min s A) (-A) - max (min t A) (-A)| := by
          simp only [c, max_comm (-A)]
      _ ≤ |min s A - min t A| := abs_max_sub_max_le_abs _ _ _
      _ ≤ |s - t| := by
          have := abs_min_sub_min_le_max s A t A
          simpa using this
  intro s t
  rw [← hcv s, ← hcv t]
  exact (hloc _ (hc s) _ (hc t)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hlip s t)) hH)


/-- v2 A:eq:Hilbert (real boundary values of the Herglotz formula): for every real `λ`,
`λ - p(λ) = (1/π) pv ∫ v(t)/(λ - t) dt`. -/
theorem realPart_sub_eq_pvHilbert_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (H A : ℝ) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hsupp : ∀ t, t ∉ Icc (-A) A → actualGapHeightE02_38 u t = 0)
    (hhol : ∀ s t, |actualGapHeightE02_38 u s - actualGapHeightE02_38 u t| ≤ H * Real.sqrt |s - t|)
    (l : ℝ) :
    l - actualQuasimomentumRealPartE02_38 u l =
      (1/Real.pi) * pvHilbert (actualGapHeightE02_38 u) l := by
  set v := actualGapHeightE02_38 u
  have hvc : Continuous v := continuous_actualGapHeightE02_38 u
  have hpl := plemelj_boundary_E02_38 hvc hH hA hsupp hhol l
  have hherg := actualQuasimomentum_herglotz_E02_38 u hu
  have hk := (tendsto_actualQuasimomentumBoundaryE02_38 u l).comp (vertical_tendsto_upper_E02_38 l)
  have hpath : Tendsto (fun ε : ℝ => (l:ℂ) + Complex.I*(ε:ℂ)) (𝓝[>] 0) (𝓝 (l:ℂ)) := by
    have h : Continuous (fun ε : ℝ => (l:ℂ) + Complex.I*(ε:ℂ)) := by fun_prop
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  have hdiff := hk.sub hpath
  have heq : (fun ε : ℝ => actualQuasimomentumE02_38 u ((l:ℂ) + Complex.I*(ε:ℂ)) -
      ((l:ℂ) + Complex.I*(ε:ℂ))) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => (1/Real.pi : ℂ) * ∫ t, (v t : ℂ) / ((t:ℂ) - ((l:ℂ) + Complex.I*(ε:ℂ)))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hz : 0 < ((l:ℂ) + Complex.I*(ε:ℂ)).im := by simpa using hε
    rw [(hherg _ hz).2]; ring
  have hlim := tendsto_nhds_unique (hdiff.congr' heq) hpl
  have hre := congrArg Complex.re hlim
  simp only [Function.comp, Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, sub_zero, mul_zero] at hre
  have : actualQuasimomentumRealPartE02_38 u l = (actualQuasimomentumBoundaryE02_38 u l).re := rfl
  rw [this]
  linarith


/-- Measurability of the truncated Hilbert transform in the base point. -/
theorem stronglyMeasurable_truncHilbert_E02_38 (v : ℝ → ℝ) (hv : Continuous v) (δ : ℝ) :
    StronglyMeasurable (fun l : ℝ => ∫ t in {t | δ < |t - l|}, v t / (l - t)) := by
  let G : ℝ × ℝ → ℝ := Set.indicator {q : ℝ × ℝ | δ < |q.2 - q.1|} (fun q => v q.2 / (q.1 - q.2))
  have hG : StronglyMeasurable G := by
    apply Measurable.stronglyMeasurable
    apply Measurable.indicator
    · exact (hv.comp continuous_snd).measurable.div (continuous_fst.sub continuous_snd).measurable
    · exact measurableSet_lt measurable_const ((continuous_snd.sub continuous_fst).abs.measurable)
  have h := hG.integral_prod_right' (ν := (volume : Measure ℝ))
  convert h using 1
  funext l
  have hS : MeasurableSet {t : ℝ | δ < |t - l|} :=
    measurableSet_lt measurable_const ((continuous_id.sub continuous_const).abs.measurable)
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards with t
  simp only [G, Set.indicator, Set.mem_setOf_eq]

/-- S02 (v2 A:lem:convex). For a field with finitely many open gaps (and `u ∈ H¹`) and every
convex `C²` function `W`, both sides are finite and
`∑' n, W(2πn) I_n ≤ (2/π) ∫ W(2λ) v(λ) dλ`. -/
theorem actualConvexMoment_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W) :
    Integrable (fun l : ℝ => W (2*l) * actualGapHeightE02_38 u l) ∧
    Summable (fun n : ℤ => W (2*Real.pi*n) * actualGapActionAllE02_38 u n) ∧
    ∑' n : ℤ, W (2*Real.pi*n) * actualGapActionAllE02_38 u n ≤
      (2/Real.pi) * ∫ l : ℝ, W (2*l) * actualGapHeightE02_38 u l := by
  set v := actualGapHeightE02_38 u with hvdef
  set p := actualQuasimomentumRealPartE02_38 u with hpdef
  have hvc : Continuous v := continuous_actualGapHeightE02_38 u
  have hv0 : ∀ t, 0 ≤ v t := actualGapHeightE02_38_nonneg u
  have hpc : Continuous p := continuous_actualQuasimomentumRealPartE02_38 u
  have hpm : Monotone p := monotone_actualQuasimomentumRealPartE02_38 u
  obtain ⟨-, A0, hA0⟩ := actualGapHeight_support_finiteGap_E02_38 u hfin
  set A' := |A0|
  set A := A' + 1
  have hA'0 : 0 ≤ A' := abs_nonneg _
  have hzero : ∀ x, A' < |x| → v x = 0 := fun x hx => hA0 x (lt_of_le_of_lt (le_abs_self _) hx)
  have hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0 := by
    intro t ht
    apply hzero
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
    · exact lt_of_lt_of_le (by linarith) (le_abs_self t)
  have hsupp' : ∀ t, A < |t| → v t = 0 := fun t ht => hzero t (by linarith)
  obtain ⟨H0, hH0⟩ := actualGapHeight_holder_E02_38 u A
  set H := |H0|
  have hloc : ∀ s ∈ Icc (-A) A, ∀ t ∈ Icc (-A) A, |v s - v t| ≤ H * Real.sqrt |s - t| :=
    fun s hs t ht => (hH0 s hs t ht).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  have hhol := holder_global_of_Icc_E02_38 v A A' H (abs_nonneg _) hA'0 (by linarith) hzero hloc
  have hA0' : 0 ≤ A := by linarith
  have hvcs : HasCompactSupport v := HasCompactSupport.intro isCompact_Icc (fun x hx => hsupp x hx)
  have hvi : Integrable v := hvc.integrable_of_hasCompactSupport hvcs
  -- the convex function f(x) = W(2x)
  let f : ℝ → ℝ := fun x => W (2*x)
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hfd : Differentiable ℝ f := hWd.comp (differentiable_id.const_mul 2)
  have hfc : Continuous f := hfd.continuous
  have hfconv : ConvexOn ℝ Set.univ f := by
    have := hconv.comp_linearMap ((2:ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    simpa [f, Function.comp_def] using this
  have hfmono : Monotone (deriv f) := by
    have h := hfconv.monotoneOn_deriv (fun x _ => hfd x)
    exact fun x y hxy => h (Set.mem_univ x) (Set.mem_univ y) hxy
  have htan : ∀ x y : ℝ, f x + deriv f x * (y - x) ≤ f y := by
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have h := hfconv.deriv_le_slope (Set.mem_univ x) (Set.mem_univ y) hxy (hfd x)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at h; linarith
    · rw [hxy]; simp
    · have h := hfconv.slope_le_deriv (Set.mem_univ y) (Set.mem_univ x) hxy (hfd x)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h; linarith
  let φ : ℝ → ℝ := fun l => deriv f (p l)
  have hφ : Monotone φ := hfmono.comp hpm
  -- integrability and the finite sum
  have hfv : Integrable (fun l => f l * v l) :=
    (hfc.mul hvc).integrable_of_hasCompactSupport (hvcs.mul_left)
  obtain ⟨hfpv, hsum⟩ := actualGapHeight_integral_eq_sum_E02_38 u hfin f hfc
  -- the Hilbert transform: bounds and identity
  obtain ⟨M, hM⟩ := truncatedHilbert_bound_E02_38 hvc (abs_nonneg H0) hA0' hsupp hhol
  have hpvb : ∀ l, |pvHilbert v l| ≤ M := by
    intro l
    have ht := tendsto_pvHilbert_E02_38 hvc (abs_nonneg H0) hA0' hsupp hhol l
    exact le_of_tendsto ht.abs (eventually_nhdsWithin_of_forall fun δ hδ => hM l δ hδ)
  have hid : ∀ l, l - p l = (1/Real.pi) * pvHilbert v l := fun l =>
    realPart_sub_eq_pvHilbert_E02_38 u hu H A (abs_nonneg _) hA0' hsupp hhol l
  set Φ := max |φ (-A)| |φ A|
  have hφb : ∀ l, v l ≠ 0 → |φ l| ≤ Φ := by
    intro l hl
    have hlI : l ∈ Icc (-A) A := by by_contra h; exact hl (hsupp l h)
    have h1 := hφ hlI.1; have h2 := hφ hlI.2
    rw [abs_le]; constructor
    · have := neg_abs_le (φ (-A)); have := le_max_left |φ (-A)| |φ A|; linarith
    · have := le_abs_self (φ A); have := le_max_right |φ (-A)| |φ A|; linarith
  have hPint : Integrable (fun l => φ l * v l * pvHilbert v l) := by
    refine (hvi.norm.const_mul (Φ * M)).mono' ?_ (Eventually.of_forall fun l => ?_)
    · have hpvm : AEStronglyMeasurable (fun l => pvHilbert v l) volume := by
        have : (fun l => pvHilbert v l) = fun l => Real.pi * (l - p l) := by
          funext l; rw [hid l]; field_simp
        rw [this]; exact (continuous_const.mul (continuous_id.sub hpc)).aestronglyMeasurable
      exact ((hφ.measurable.aestronglyMeasurable.mul hvc.aestronglyMeasurable).mul hpvm)
    · by_cases hl : v l = 0
      · simp [hl]
      · rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs]
        have h1 := hφb l hl; have h2 := hpvb l
        have hΦ : 0 ≤ Φ := le_trans (abs_nonneg _) (le_max_left _ _)
        calc |φ l| * |v l| * |pvHilbert v l| ≤ Φ * |v l| * M := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2
                (abs_nonneg _) (by positivity)
          _ = Φ * M * |v l| := by ring
  -- dominated convergence for the truncations
  have hlimit : Tendsto (fun δ : ℝ => ∫ l, φ l * v l * ∫ t in {t | δ < |t - l|}, v t / (l - t))
      (𝓝[>] 0) (𝓝 (∫ l, φ l * v l * pvHilbert v l)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun l => Φ * M * |v l|)
    · exact Eventually.of_forall fun δ =>
        ((hφ.measurable.aestronglyMeasurable.mul hvc.aestronglyMeasurable).mul
          (stronglyMeasurable_truncHilbert_E02_38 v hvc δ).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact Eventually.of_forall fun l => by
        by_cases hl : v l = 0
        · simp [hl]
        · rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have h1 := hφb l hl; have h2 := hM l δ hδ
          calc |φ l| * |v l| * |∫ t in {t | δ < |t - l|}, v t / (l - t)| ≤ Φ * |v l| * M := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2
                  (abs_nonneg _) (by positivity)
            _ = Φ * M * |v l| := by ring
    · exact hvi.norm.const_mul _
    · exact Eventually.of_forall fun l =>
        ((tendsto_pvHilbert_E02_38 hvc (abs_nonneg H0) hA0' hsupp hhol l).const_mul (φ l * v l))
  have hpos : 0 ≤ ∫ l, φ l * v l * pvHilbert v l := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact truncatedHilbert_pairing_nonneg_E02_38 v φ hvc hv0 A hsupp' hφ δ hδ
  -- the main difference
  have hdiff : 0 ≤ ∫ l, (f l - f (p l)) * v l := by
    have hlow : ∫ l, φ l * (l - p l) * v l ≤ ∫ l, (f l - f (p l)) * v l := by
      apply integral_mono
      · have : (fun l => φ l * (l - p l) * v l) = fun l => (1/Real.pi) * (φ l * v l * pvHilbert v l) := by
          funext l; rw [hid l]; ring
        rw [this]; exact hPint.const_mul _
      · exact (hfv.sub hfpv).congr (Eventually.of_forall fun l => by simp only [Pi.sub_apply]; ring)
      · intro l
        have := htan (p l) l
        exact mul_le_mul_of_nonneg_right (by simp only [φ]; linarith) (hv0 l)
    have heq : ∫ l, φ l * (l - p l) * v l = (1/Real.pi) * ∫ l, φ l * v l * pvHilbert v l := by
      rw [← integral_const_mul]
      apply integral_congr_ae; filter_upwards with l; rw [hid l]; ring
    rw [heq] at hlow
    have : 0 ≤ (1/Real.pi) * ∫ l, φ l * v l * pvHilbert v l :=
      mul_nonneg (by positivity) hpos
    linarith
  -- finite support of the series
  have hzeroI : ∀ n : ℤ, n ∉ hfin.toFinset → actualGapActionAllE02_38 u n = 0 := by
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    simp only [Set.mem_setOf_eq, not_lt] at hn
    obtain ⟨hne, hIcc⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
    have hle : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
      obtain ⟨x, hx⟩ := hne; rw [hIcc] at hx; exact hx.1.trans hx.2
    have heq : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n := le_antisymm hle hn
    simp [actualGapActionAllE02_38, heq]
  have hterm0 : ∀ n : ℤ, n ∉ hfin.toFinset → W (2*Real.pi*n) * actualGapActionAllE02_38 u n = 0 :=
    fun n hn => by rw [hzeroI n hn, mul_zero]
  have hsummable : Summable (fun n : ℤ => W (2*Real.pi*n) * actualGapActionAllE02_38 u n) :=
    summable_of_ne_finset_zero hterm0
  have htsum : ∑' n : ℤ, W (2*Real.pi*n) * actualGapActionAllE02_38 u n =
      (2/Real.pi) * ∫ l, f (p l) * v l := by
    rw [tsum_eq_sum hterm0, hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [actualGapActionAllE02_38, f]
    rw [show 2 * ((n:ℝ) * Real.pi) = 2 * Real.pi * n by ring]
    ring
  refine ⟨hfv, hsummable, ?_⟩
  rw [htsum]
  have hsplit : ∫ l, (f l - f (p l)) * v l = (∫ l, f l * v l) - ∫ l, f (p l) * v l := by
    rw [← integral_sub hfv hfpv]; apply integral_congr_ae; filter_upwards with l; ring
  rw [hsplit] at hdiff
  have : ∫ l, f (p l) * v l ≤ ∫ l, f l * v l := by linarith
  exact mul_le_mul_of_nonneg_left this (by positivity)

end NlsGge.SpectralFoundations
end
