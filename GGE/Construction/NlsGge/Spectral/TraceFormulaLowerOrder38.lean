import NlsGge.Spectral.ActualActionSumE02_38
import NlsGge.Spectral.ChargeJensenSobolev38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core NlsGge.Sobolev38

/-! # R1 (TF-H^k): lower-order trace formulas `M_{2j} = Q_{2j}` on `H^{j+1}`, and Lemma A

Route of `ActualActionSumE02_38`: Fourier truncations, smooth trace formulas, uniform tails from the
`(j+1)`-th moment (bounded because `Q_{2j+2}` is continuous on `H^{m-1}`), E03-cont local uniform
convergence. -/

/-- Abstract: nonnegative continuous `f` with uniformly bounded interval integrals is integrable. -/
theorem integrable_of_Icc_bound38 (f : ℝ → ℝ) (hc : Continuous f) (h0 : ∀ t, 0 ≤ f t) (B : ℝ)
    (hB : ∀ L : ℝ, 0 ≤ L → ∫ t in Icc (-L) L, f t ≤ B) :
    Integrable f ∧ ∫ t, f t ≤ B := by
  have hnat : Tendsto (fun i : ℕ => (i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnatneg : Tendsto (fun i : ℕ => -(i:ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hnat
  have hint : Integrable f := by
    refine integrable_of_intervalIntegral_norm_bounded (l := atTop) (a := fun i : ℕ => -(i:ℝ))
      (b := fun i : ℕ => (i:ℝ)) B (fun i => ?_) hnatneg hnat (Eventually.of_forall fun i => ?_)
    · exact hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
      rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
      have e : ∫ x in Icc (-(i:ℝ)) i, ‖f x‖ = ∫ x in Icc (-(i:ℝ)) i, f x := by
        congr 1; funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
      rw [e]; exact hB i hi
  refine ⟨hint, ?_⟩
  have ht := intervalIntegral_tendsto_integral hint hnatneg hnat
  refine le_of_tendsto' ht fun i => ?_
  have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  exact hB i hi

/-- Local uniform convergence gives convergence of interval integrals against a continuous weight. -/
theorem setIntegral_tendsto_of_unif38 (p : ℝ → ℝ) (hp : Continuous p) (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hFc : ∀ N, Continuous (F N)) (hGc : Continuous G)
    (hunif : ∀ L ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Icc (-L) L, |F N t - G t| < ε)
    (L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun N => ∫ t in Icc (-L) L, p t * F N t) atTop (𝓝 (∫ t in Icc (-L) L, p t * G t)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := (isCompact_Icc (a := -L) (b := L)).exists_bound_of_continuousOn
    hp.continuousOn
  have hP0 : 0 ≤ |P| := abs_nonneg P
  set ε' := ε / (2 * (|P| + 1) * (2 * L + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨N₀, hN₀⟩ := hunif L ε' hε'pos
  refine ⟨N₀, fun N hN => ?_⟩
  have hIcc : volume (Icc (-L) L) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have h1 : IntegrableOn (fun t => p t * F N t) (Icc (-L) L) :=
    (hp.mul (hFc N)).continuousOn.integrableOn_Icc
  have h2 : IntegrableOn (fun t => p t * G t) (Icc (-L) L) :=
    (hp.mul hGc).continuousOn.integrableOn_Icc
  have hd : ‖∫ t in Icc (-L) L, (p t * F N t - p t * G t)‖ ≤
      ((|P| + 1) * ε') * volume.real (Icc (-L) L) := by
    refine norm_setIntegral_le_of_norm_le_const hIcc fun t ht => ?_
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := hN₀ N hN t ht
    have hpt : |p t| ≤ |P| + 1 := by
      have h := hP t ht
      rw [Real.norm_eq_abs] at h
      linarith [le_abs_self P]
    exact mul_le_mul hpt this.le (abs_nonneg _) (by positivity)
  have hvol : volume.real (Icc (-L) L) = 2 * L := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
  rw [hvol, integral_sub h1 h2] at hd
  rw [Real.dist_eq]
  have hb : (|P| + 1) * ε' * (2 * L) < ε := by
    have e : (|P| + 1) * ε' * (2 * L) = ε / 2 * (2 * L / (2 * L + 1)) := by
      simp only [hε']; field_simp
    rw [e]
    have : 2 * L / (2 * L + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  have := lt_of_le_of_lt (Real.norm_eq_abs _ ▸ hd) hb
  exact this

/-- Fatou half: if the `p_j`-moments of `F N` are eventually bounded by `C + ε`, so is that of `G`. -/
theorem moment_fatou38 (j : ℕ) (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hFc : ∀ N, Continuous (F N)) (hGc : Continuous G)
    (hF0 : ∀ N t, 0 ≤ F N t) (hG0 : ∀ t, 0 ≤ G t)
    (hunif : ∀ L ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Icc (-L) L, |F N t - G t| < ε)
    (hFp : ∀ N, Integrable (fun t => (2*t)^(2*j) * F N t)) (C : ℝ)
    (hbd : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∫ t, (2*t)^(2*j) * F N t ≤ C + ε) :
    Integrable (fun t => (2*t)^(2*j) * G t) ∧ ∫ t, (2*t)^(2*j) * G t ≤ C := by
  have hp : Continuous (fun t : ℝ => (2*t)^(2*j)) := by fun_prop
  have hp0 : ∀ t : ℝ, 0 ≤ (2*t)^(2*j) := fun t => by
    rw [pow_mul]; positivity
  have hB : ∀ L : ℝ, 0 ≤ L → ∫ t in Icc (-L) L, (2*t)^(2*j) * G t ≤ C := by
    intro L hL
    refine le_of_forall_pos_le_add fun ε hε => ?_
    refine le_of_tendsto (setIntegral_tendsto_of_unif38 _ hp F G hFc hGc hunif L hL) ?_
    filter_upwards [hbd ε hε] with N hN
    exact le_trans (setIntegral_le_integral (hFp N)
      (Eventually.of_forall fun t => mul_nonneg (hp0 t) (hF0 N t))) hN
  exact integrable_of_Icc_bound38 _ (hp.mul hGc) (fun t => mul_nonneg (hp0 t) (hG0 t)) C hB

/-- Tail estimate for the `2j`-moment through the `2j+2` moment. -/
theorem tail_moment38 (j : ℕ) (Φ : ℝ → ℝ) (h0 : ∀ t, 0 ≤ Φ t)
    (hp : Integrable (fun t => (2*t)^(2*j) * Φ t))
    (hq : Integrable (fun t => (2*t)^(2*(j+1)) * Φ t)) (L : ℝ) (hL : 0 < L) :
    0 ≤ (∫ t, (2*t)^(2*j) * Φ t) - (∫ t in Icc (-L) L, (2*t)^(2*j) * Φ t) ∧
    (∫ t, (2*t)^(2*j) * Φ t) - (∫ t in Icc (-L) L, (2*t)^(2*j) * Φ t) ≤
      (∫ t, (2*t)^(2*(j+1)) * Φ t) / (4 * L^2) := by
  have hp0 : ∀ t : ℝ, 0 ≤ (2*t)^(2*j) := fun t => by
    rw [pow_mul]; positivity
  have hpos : 0 < 4 * L^2 := by positivity
  have hsplit := integral_add_compl (s := Icc (-L) L) measurableSet_Icc hp
  constructor
  · rw [← hsplit, add_sub_cancel_left]
    exact setIntegral_nonneg measurableSet_Icc.compl fun t _ => mul_nonneg (hp0 t) (h0 t)
  · rw [← hsplit, add_sub_cancel_left, le_div_iff₀ hpos]
    have h1 : ∫ t in (Icc (-L) L)ᶜ, (4 * L^2) * ((2*t)^(2*j) * Φ t) ≤
        ∫ t in (Icc (-L) L)ᶜ, (2*t)^(2*(j+1)) * Φ t := by
      refine setIntegral_mono_on (hp.integrableOn.const_mul _) hq.integrableOn
        measurableSet_Icc.compl ?_
      intro t ht
      have ht' : L < |t| := by
        by_contra hc; push Not at hc
        exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
      have hLt : L^2 ≤ t^2 := by
        have := mul_le_mul ht'.le ht'.le hL.le (abs_nonneg t)
        nlinarith [sq_abs t]
      have e : (2*t)^(2*(j+1)) = (2*t)^(2*j) * (2*t)^2 := by ring
      rw [e]
      have : 4 * L^2 ≤ (2*t)^2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this (mul_nonneg (hp0 t) (h0 t))
      nlinarith [this]
    have h2 : ∫ t in (Icc (-L) L)ᶜ, (2*t)^(2*(j+1)) * Φ t ≤ ∫ t, (2*t)^(2*(j+1)) * Φ t :=
      setIntegral_le_integral hq (Eventually.of_forall fun t => mul_nonneg
        (by rw [pow_mul]; positivity) (h0 t))
    rw [integral_const_mul] at h1
    linarith

/-- Equality half: bounded `(2j+2)`-moments and convergent `2j`-moments pass to the limit. -/
theorem moment_eq38 (j : ℕ) (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hFc : ∀ N, Continuous (F N)) (hGc : Continuous G)
    (hF0 : ∀ N t, 0 ≤ F N t) (hG0 : ∀ t, 0 ≤ G t)
    (hunif : ∀ L ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Icc (-L) L, |F N t - G t| < ε)
    (hFp : ∀ N, Integrable (fun t => (2*t)^(2*j) * F N t))
    (hFq : ∀ N, Integrable (fun t => (2*t)^(2*(j+1)) * F N t)) (C : ℝ)
    (hC : ∀ N, ∫ t, (2*t)^(2*(j+1)) * F N t ≤ C) (A : ℝ)
    (hA : Tendsto (fun N => ∫ t, (2*t)^(2*j) * F N t) atTop (𝓝 A)) :
    Integrable (fun t => (2*t)^(2*j) * G t) ∧ ∫ t, (2*t)^(2*j) * G t = A := by
  have hp : Continuous (fun t : ℝ => (2*t)^(2*j)) := by fun_prop
  have hFat1 := moment_fatou38 (j+1) F G hFc hGc hF0 hG0 hunif hFq C
    (fun ε hε => Eventually.of_forall fun N => by linarith [hC N])
  have hFat0 := moment_fatou38 j F G hFc hGc hF0 hG0 hunif hFp A
    (fun ε hε => by
      have := hA.eventually (Iio_mem_nhds (show A < A + ε by linarith))
      filter_upwards [this] with N hN using hN.le)
  obtain ⟨hGq, hGqle⟩ := hFat1
  obtain ⟨hGp, _⟩ := hFat0
  refine ⟨hGp, ?_⟩
  have hC0 : 0 ≤ C := le_trans (integral_nonneg fun t => mul_nonneg
    (by rw [pow_mul]; positivity) (hF0 0 t)) (hC 0)
  refine tendsto_nhds_unique ?_ hA
  rw [Metric.tendsto_atTop]
  intro ε hε
  set L := C / ε + 1 with hLdef
  have hL : 0 < L := by positivity
  have hLb : C / (4 * L^2) ≤ ε / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : C ≤ ε * (L - 1) := by
      have : ε * (C / ε) = C := by field_simp
      simp only [hLdef]; linarith
    nlinarith [sq_nonneg (L - 1)]
  have hI := setIntegral_tendsto_of_unif38 _ hp F G hFc hGc hunif L hL.le
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hI) (ε / 4) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have tN := tail_moment38 j (F N) (hF0 N) (hFp N) (hFq N) L hL
  have tG := tail_moment38 j G hG0 hGp hGq L hL
  have hpos : 0 < 4 * L^2 := by positivity
  have e1 : (∫ t, (2*t)^(2*(j+1)) * F N t) / (4 * L^2) ≤ ε / 4 :=
    le_trans (div_le_div_of_nonneg_right (hC N) hpos.le) hLb
  have e2 : (∫ t, (2*t)^(2*(j+1)) * G t) / (4 * L^2) ≤ ε / 4 :=
    le_trans (div_le_div_of_nonneg_right hGqle hpos.le) hLb
  have e3 := hN₀ N hN
  rw [Real.dist_eq, abs_lt] at e3 ⊢
  constructor <;> linarith [e3.1, e3.2, tN.1, tN.2, tG.1, tG.2]

/-! ## Linking `PhysicalL2` and the Sobolev carrier -/

/-- A square-summable (weighted) Fourier sequence of `u` defines a Sobolev element. -/
theorem exists_sobolev_link38 (r : ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable r (physicalFourier u)) :
    ∃ y : SobolevHilbert r, ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight r) from y) n = physicalFourier u n := by
  have hmem : Memℓp (weightedCoordinates (sobolevModeWeight r) (fun n => physicalFourier u n)) 2 := by
    rw [weightedCoordinates_mem_l2_iff (sobolevModeWeight r) (fun n => (Real.rpow_pos_of_pos (japaneseBracket_pos n) (2 * r)).le)]
    exact hu
  exact ⟨(⟨fun n => physicalFourier u n, hmem⟩ : WeightedHilbert (sobolevModeWeight r)),
    fun n => rfl⟩

/-! ## The truncation data -/

section Main

variable (m : ℕ) (u : PhysicalL2) (y : SobolevHilbert ((m - 1 : ℕ) : ℝ))
  (hy : ∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) n =
    physicalFourier u n)

include hy in
theorem truncPlane_eq_sobolev38 (N : ℕ) :
    truncPlaneE02_38 u N = fun i => (show WeightedHilbert
      (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from y) (modeIndex N i) :=
  funext fun i => (hy _).symm

include hy in
/-- Smooth trace formula along the Fourier truncations, in terms of `Q_{2i}` of the truncation. -/
theorem truncation_trace_charge38 (hm : 2 ≤ m) (i : ℕ) (hi : i ≤ m) (N : ℕ) :
    Integrable (fun t : ℝ => (2*t)^(2*i) * actualGapHeightE02_38 (truncL2E02_38 u N) t) ∧
    (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*i) * actualGapHeightE02_38 (truncL2E02_38 u N) t =
      chargeSobolev38 m i (truncSobolev38 _ N y) := by
  obtain ⟨h1, h2⟩ := truncL2_trace_E02_38 u N i
  rw [chargeSobolev38_trunc m i hm hi N y, ← truncPlane_eq_sobolev38 m u y hy N]
  exact ⟨h1, h2.symm⟩

include hy in
theorem truncation_moment_tendsto38 (hm : 2 ≤ m) (i : ℕ) (hi : i ≤ m - 1) :
    Tendsto (fun N : ℕ => ∫ t : ℝ, (2*t)^(2*i) * actualGapHeightE02_38 (truncL2E02_38 u N) t)
      atTop (𝓝 ((Real.pi / 2) * chargeSobolev38 m i y)) := by
  have hQ : Tendsto (fun N : ℕ => chargeSobolev38 m i (truncSobolev38 _ N y)) atTop
      (𝓝 (chargeSobolev38 m i y)) :=
    ((continuous_chargeSobolev38 m i hi).tendsto y).comp (tendsto_truncSobolev38 _ y)
  refine (hQ.const_mul (Real.pi / 2)).congr fun N => ?_
  have := (truncation_trace_charge38 m u y hy hm i (by omega) N).2
  have hpi := Real.pi_pos
  rw [← this]; field_simp

theorem truncation_unif38 (u : PhysicalL2) :
    ∀ L ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Icc (-L) L,
      |actualGapHeightE02_38 (truncL2E02_38 u N) t - actualGapHeightE02_38 u t| < ε := by
  intro L ε hε
  obtain ⟨τ, hτ, hclose⟩ := gapHeight_uniform_close_E02_38 u (-L) L ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (tendsto_truncL2_E02_38 u)) τ hτ
  refine ⟨N₀, fun N hN t ht => hclose _ ?_ t ht⟩
  have := hN₀ N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
  exact this.le

include hy in
/-- **Lemma A (Fatou).** For `y ∈ H^{m-1}` linked to `u`, `j ≤ m-1`:
the `2j`-moment is finite and `(2/π)∫(2t)^{2j} v ≤ Q_{2j}`. -/
theorem actualMoment_le_charge38 (hm : 2 ≤ m) (j : ℕ) (hj : j ≤ m - 1) :
    Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) ∧
    (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t ≤ chargeSobolev38 m j y := by
  have hpi := Real.pi_pos
  have hA := truncation_moment_tendsto38 m u y hy hm j hj
  obtain ⟨hI, hle⟩ := moment_fatou38 j (fun N => actualGapHeightE02_38 (truncL2E02_38 u N))
    (actualGapHeightE02_38 u) (fun N => continuous_actualGapHeightE02_38 _)
    (continuous_actualGapHeightE02_38 u) (fun N t => actualGapHeightE02_38_nonneg _ t)
    (actualGapHeightE02_38_nonneg u) (truncation_unif38 u)
    (fun N => (truncation_trace_charge38 m u y hy hm j (by omega) N).1)
    ((Real.pi / 2) * chargeSobolev38 m j y)
    (fun ε hε => by
      have := hA.eventually (Iio_mem_nhds (show (Real.pi / 2) * chargeSobolev38 m j y <
        (Real.pi / 2) * chargeSobolev38 m j y + ε by linarith))
      filter_upwards [this] with N hN using hN.le)
  refine ⟨hI, ?_⟩
  have : ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t ≤ (Real.pi / 2) * chargeSobolev38 m j y := hle
  calc (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t
      ≤ (2/Real.pi) * ((Real.pi / 2) * chargeSobolev38 m j y) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = chargeSobolev38 m j y := by field_simp

include hy in
/-- **R1.** `M_{2j} = Q_{2j}` on `H^{j+1}` (`j + 2 ≤ m`, `y ∈ H^{m-1}` linked to `u`). -/
theorem actualTraceFormula_lower_E02_38 (j : ℕ) (hjm : j + 2 ≤ m) :
    Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) ∧
    (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t = chargeSobolev38 m j y := by
  have hpi := Real.pi_pos
  have hm : 2 ≤ m := by omega
  have hA := truncation_moment_tendsto38 m u y hy hm j (by omega)
  have hB := truncation_moment_tendsto38 m u y hy hm (j+1) (by omega)
  obtain ⟨C, hC⟩ := hB.bddAbove_range
  obtain ⟨hI, heq⟩ := moment_eq38 j (fun N => actualGapHeightE02_38 (truncL2E02_38 u N))
    (actualGapHeightE02_38 u) (fun N => continuous_actualGapHeightE02_38 _)
    (continuous_actualGapHeightE02_38 u) (fun N t => actualGapHeightE02_38_nonneg _ t)
    (actualGapHeightE02_38_nonneg u) (truncation_unif38 u)
    (fun N => (truncation_trace_charge38 m u y hy hm j (by omega) N).1)
    (fun N => (truncation_trace_charge38 m u y hy hm (j+1) (by omega) N).1) C
    (fun N => hC ⟨N, rfl⟩) _ hA
  refine ⟨hI, ?_⟩
  rw [heq]; field_simp

end Main

/-- **Lemma A** (F04.01-.03): `u ∈ H^j`, `j ≥ 1` has a finite `2j`-moment of the gap height. -/
theorem actualMoment_integrable_of_sobolev38 (j : ℕ) (hj : 1 ≤ j) (u : PhysicalL2)
    (hu : SobolevSquareSummable (j : ℝ) (physicalFourier u)) :
    Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) := by
  have hu' : SobolevSquareSummable (((j + 1 - 1 : ℕ)) : ℝ) (physicalFourier u) := hu
  obtain ⟨y, hy⟩ := exists_sobolev_link38 _ u hu'
  exact (actualMoment_le_charge38 (j + 1) u y hy (by omega) j (by omega)).1

/-- Lemma A with the bound: `(2/π)∫(2t)^{2j} v ≤ Q_{2j}(u)` for the `H^j` extension `Q_{2j}`. -/
theorem actualMoment_bound_of_sobolev38 (j : ℕ) (hj : 1 ≤ j) (u : PhysicalL2)
    (hu : SobolevSquareSummable (j : ℝ) (physicalFourier u)) :
    ∃ y : SobolevHilbert (((j + 1 - 1 : ℕ)) : ℝ),
      (∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight (((j + 1 - 1 : ℕ)) : ℝ)) from y) n =
        physicalFourier u n) ∧
      (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t ≤
        chargeSobolev38 (j + 1) j y := by
  have hu' : SobolevSquareSummable (((j + 1 - 1 : ℕ)) : ℝ) (physicalFourier u) := hu
  obtain ⟨y, hy⟩ := exists_sobolev_link38 _ u hu'
  exact ⟨y, hy, (actualMoment_le_charge38 (j + 1) u y hy (by omega) j (by omega)).2⟩

/-- R1 for a field in `H^{j+1}`. -/
theorem actualTraceFormula_lower_of_sobolev38 (j : ℕ) (u : PhysicalL2)
    (hu : SobolevSquareSummable ((j + 1 : ℕ) : ℝ) (physicalFourier u)) :
    ∃ y : SobolevHilbert (((j + 2 - 1 : ℕ)) : ℝ),
      (∀ n : ℤ, (show WeightedHilbert (sobolevModeWeight (((j + 2 - 1 : ℕ)) : ℝ)) from y) n =
        physicalFourier u n) ∧
      Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 u t) ∧
      (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 u t =
        chargeSobolev38 (j + 2) j y := by
  have hu' : SobolevSquareSummable (((j + 2 - 1 : ℕ)) : ℝ) (physicalFourier u) := hu
  obtain ⟨y, hy⟩ := exists_sobolev_link38 _ u hu'
  exact ⟨y, hy, actualTraceFormula_lower_E02_38 (j + 2) u y hy j le_rfl⟩

end NlsGge.SpectralFoundations
end
