import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB8Test

/-! # Track B, contract 6 preparation: strip pairings, mode decomposition, integration by parts

* `integrable_strip`: `F(t, x mod 1) b(t,x)` is `stripMeasure`-integrable for slab-integrable `F`
  and bounded measurable `b` vanishing for `|t| > T`;
* `strip_mode`: `∫ F(t,x mod 1) d(t) e^{2πimx} = ∫ d(t) F̂(t)(-m) dt` (Fubini, `x ↦ x mod 1`);
* `strip_series`: for a test function `ψ`, `∫ F ψ = ∑ₘ ∫ cT ψ m t F̂(t)(-m) dt`
  (pointwise Fourier series of `ψ(t,·)`, uniform coefficient decay, `integral_tsum`);
* `ibp_primitive`: `∫ ψ' a = -∫ ψ g` for `a = a(0) + ∫₀ᵗ g` (`g ∈ L¹_loc`) and `ψ ∈ C¹` with
  compact support (Fubini on the triangle, no differentiability of `a`);
* `mode_lhs_eq`, `mode_rhs_eq`: the interaction-picture algebra of one Fourier mode.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

attribute [local instance] isProbabilityMeasure_spatial

/-- Integrability on every slab `[-T,T] × 𝕋`. -/
def IsSlabInt (F : ℝ × PhysicalCircle → ℂ) : Prop :=
  ∀ T : ℝ, Integrable F (((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod spatialMeasure)

theorem isSlabInt_of_isL4Loc {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) : IsSlabInt U := by
  intro T
  have h := h4 T
  rw [spacetimeMeasure, slab_eq] at h
  have := isFiniteMeasure_slab (-T) T
  exact h.integrable (by norm_num)

theorem isSlabInt_cubic {U : ℝ × PhysicalCircle → ℂ} (h4 : IsL4Loc U) :
    IsSlabInt (fun p => cubicNL (U p)) := fun T => cubic_slab_integrable h4 T

theorem volume_eq_spatial : (volume : Measure PhysicalCircle) = spatialMeasure := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  rfl

theorem measurePreserving_stripMap_slab (T : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1, (p.2 : PhysicalCircle)))
      (((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 1)))
      (((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod spatialMeasure) := by
  have h := AddCircle.measurePreserving_mk (T := (1 : ℝ)) 0
  rw [zero_add, volume_eq_spatial] at h
  exact (MeasurePreserving.id ((volume : Measure ℝ).restrict (Set.Icc (-T) T))).prod h

theorem strip_restrict_eq (T : ℝ) :
    stripMeasure.restrict (Set.Icc (-T) T ×ˢ Set.univ) =
      ((volume : Measure ℝ).restrict (Set.Icc (-T) T)).prod
        ((volume : Measure ℝ).restrict (Set.Ioc 0 1)) := by
  have h := Measure.prod_restrict (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 1)) (Set.Icc (-T) T) Set.univ
  rw [Measure.restrict_univ] at h
  rw [stripMeasure, h]

theorem integrable_strip {F : ℝ × PhysicalCircle → ℂ} (hF : IsSlabInt F) {b : ℝ × ℝ → ℂ}
    (hb : AEStronglyMeasurable b stripMeasure) {B T : ℝ} (hB : ∀ p, ‖b p‖ ≤ B)
    (hT : ∀ p : ℝ × ℝ, T < |p.1| → b p = 0) :
    Integrable (fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)) * b p) stripMeasure := by
  have h1 : Integrable (fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)))
      (stripMeasure.restrict (Set.Icc (-T) T ×ˢ Set.univ)) := by
    rw [strip_restrict_eq]
    exact ((measurePreserving_stripMap_slab T).integrable_comp (hF T).aestronglyMeasurable).2 (hF T)
  have h2 : Integrable (fun p : ℝ × ℝ => b p * F (p.1, (p.2 : PhysicalCircle)))
      (stripMeasure.restrict (Set.Icc (-T) T ×ˢ Set.univ)) :=
    h1.bdd_mul hb.restrict (ae_of_all _ hB)
  have h3 : IntegrableOn (fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)) * b p)
      (Set.Icc (-T) T ×ˢ Set.univ) stripMeasure :=
    h2.congr (ae_of_all _ fun p => mul_comm _ _)
  refine h3.integrable_of_forall_notMem_eq_zero fun p hp => ?_
  have : T < |p.1| := by
    by_contra h
    rw [not_lt] at h
    exact hp ⟨abs_le.mp h, trivial⟩
  rw [hT p this, mul_zero]

theorem strip_mode {F : ℝ × PhysicalCircle → ℂ} {d : ℝ → ℂ} (m : ℤ)
    (hi : Integrable (fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)) * (d p.1 * ex m p.2))
      stripMeasure) :
    ∫ p, F (p.1, (p.2 : PhysicalCircle)) * (d p.1 * ex m p.2) ∂stripMeasure =
      ∫ t, d t * physicalFourier (fun y => F (t, y)) (-m) := by
  rw [stripMeasure, integral_prod _ hi]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have h := AddCircle.integral_preimage 1 0 (fun y => F (t, y) * fourier m y)
  rw [zero_add, volume_eq_spatial] at h
  have e : (fun x : ℝ => F (t, (x : PhysicalCircle)) * (d t * ex m x)) =
      fun x : ℝ => d t * (F (t, (x : PhysicalCircle)) * fourier m (x : PhysicalCircle)) := by
    funext x
    simp only [ex]
    ring
  simp only
  rw [e, integral_const_mul, h]
  congr 1
  unfold physicalFourier fourierCoeff spatialMeasure
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [neg_neg, smul_eq_mul]
  ring

theorem cT_eq_zero {φ : ℝ × ℝ → ℂ} {T : ℝ} (hT : ∀ t x, T < |t| → φ (t, x) = 0) (m : ℤ)
    {t : ℝ} (ht : T < |t|) : cT φ m t = 0 := by
  unfold cT cf
  have : (fun x => ex (-m) x * φ (t, x)) = fun _ => 0 := funext fun x => by rw [hT t x ht, mul_zero]
  rw [this, intervalIntegral.integral_zero]

theorem continuous_cT {φ : ℝ × ℝ → ℂ} (hφ : IsSpacetimeTest φ) (m : ℤ) :
    Continuous (fun t => cT φ m t) :=
  continuous_iff_continuousAt.2 fun t => (cT_hasDerivAt hφ m t).continuousAt

/-- Series form of the strip pairing with a test function. -/
theorem strip_series {F : ℝ × PhysicalCircle → ℂ} (hF : IsSlabInt F) {ψ : ℝ × ℝ → ℂ}
    (hψ : IsSpacetimeTest ψ) :
    Integrable (fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)) * ψ p) stripMeasure ∧
      ∫ p, F (p.1, (p.2 : PhysicalCircle)) * ψ p ∂stripMeasure =
        ∑' m : ℤ, ∫ t, cT ψ m t * physicalFourier (fun y => F (t, y)) (-m) := by
  obtain ⟨T, hT⟩ := hψ.compact_time
  obtain ⟨K, hK0, hK⟩ := cT_bound hψ
  obtain ⟨Bψ, -, hBψ⟩ := hψ.bounded
  have hint : Integrable (fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)) * ψ p) stripMeasure :=
    integrable_strip hF hψ.continuous.aestronglyMeasurable hBψ (fun p hp => by
      obtain ⟨t, x⟩ := p; exact hT t x hp)
  refine ⟨hint, ?_⟩
  set f : ℤ → ℝ × ℝ → ℂ := fun m p => F (p.1, (p.2 : PhysicalCircle)) * (cT ψ m p.1 * ex m p.2)
    with hfdef
  have hfi : ∀ m, Integrable (f m) stripMeasure := fun m =>
    integrable_strip hF (((continuous_cT hψ m).comp continuous_fst).mul
      ((continuous_ex m).comp continuous_snd)).aestronglyMeasurable
      (B := K / (1 + disp m)) (fun p => by rw [norm_mul, norm_ex, mul_one]; exact hK m p.1)
      (fun p hp => by rw [cT_eq_zero hT m hp, zero_mul])
  set b0 : ℝ × ℝ → ℂ := (Set.Icc (-T) T ×ˢ Set.univ).indicator (fun _ => (1 : ℂ)) with hb0
  have hb0m : AEStronglyMeasurable b0 stripMeasure :=
    (measurable_const.indicator (measurableSet_Icc.prod MeasurableSet.univ)).aestronglyMeasurable
  have hH : Integrable (fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)) * b0 p) stripMeasure :=
    integrable_strip hF hb0m (B := 1)
      (fun p => by
        rw [hb0]
        by_cases h : p ∈ Set.Icc (-T) T ×ˢ Set.univ
        · rw [Set.indicator_of_mem h, norm_one]
        · rw [Set.indicator_of_notMem h, norm_zero]; norm_num)
      (fun p hp => by
        rw [hb0, Set.indicator_of_notMem]
        rintro ⟨h1, -⟩
        exact absurd (abs_le.mpr h1) (not_le.mpr hp))
  have hle : ∀ m, ∫ p, ‖f m p‖ ∂stripMeasure ≤
      K / (1 + disp m) * ∫ p, ‖F (p.1, (p.2 : PhysicalCircle)) * b0 p‖ ∂stripMeasure := by
    intro m
    rw [← integral_const_mul]
    refine integral_mono (hfi m).norm (hH.norm.const_mul _) fun p => ?_
    simp only [hfdef]
    by_cases h : p ∈ Set.Icc (-T) T ×ˢ Set.univ
    · rw [hb0, Set.indicator_of_mem h, mul_one, norm_mul, norm_mul, norm_ex, mul_one, mul_comm]
      exact mul_le_mul_of_nonneg_right (hK m p.1) (norm_nonneg _)
    · have hp : T < |p.1| := by
        by_contra h'
        rw [not_lt] at h'
        exact h ⟨abs_le.mp h', trivial⟩
      rw [cT_eq_zero hT m hp, zero_mul, mul_zero, norm_zero]
      exact mul_nonneg (div_nonneg hK0 (by linarith [disp_nonneg' m])) (norm_nonneg _)
  have hsum : Summable fun m => ∫ p, ‖f m p‖ ∂stripMeasure := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun p => norm_nonneg _) hle ?_
    have := (summable_weight.mul_left K).mul_right
      (∫ p, ‖F (p.1, (p.2 : PhysicalCircle)) * b0 p‖ ∂stripMeasure)
    refine this.congr fun m => ?_
    rw [mul_one_div]
  have htsum := integral_tsum_of_summable_integral_norm hfi hsum
  have hpt : (fun p => ∑' m, f m p) = fun p : ℝ × ℝ => F (p.1, (p.2 : PhysicalCircle)) * ψ p := by
    funext p
    simp only [hfdef]
    rw [tsum_mul_left, (cT_hasSum hψ p.1 p.2).tsum_eq]
  rw [hpt] at htsum
  rw [← htsum]
  refine tsum_congr fun m => ?_
  exact strip_mode m (hfi m)

/-! ### Integration by parts against a primitive -/

theorem integral_indicator_Ici_Ioc {g : ℝ → ℂ} {s t q : ℝ} (hq : q ∈ Set.Ioc s t) :
    ∫ r, (Set.Ici q).indicator g r ∂((volume : Measure ℝ).restrict (Set.Ioc s t)) =
      ∫ r in q..t, g r := by
  rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    intervalIntegral.integral_of_le hq.2, ← integral_Icc_eq_integral_Ioc]
  congr 2
  ext r
  simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
  constructor
  · rintro ⟨h1, -, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, lt_of_lt_of_le hq.1 h1, h3⟩

theorem fubini_triangle {g ψ' : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    (hg : IntegrableOn g (Set.Ioc s t)) (hψ' : IntegrableOn ψ' (Set.Ioc s t)) :
    ∫ r in s..t, ψ' r * ∫ q in s..r, g q = ∫ q in s..t, g q * ∫ r in q..t, ψ' r := by
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioc s t) with hμ
  set H : ℝ × ℝ → ℂ := fun p => g p.1 * ψ' p.2 with hHdef
  have hH : Integrable H (μ.prod μ) := hg.mul_prod hψ'
  set S : Set (ℝ × ℝ) := {p | p.1 ≤ p.2} with hSdef
  have hS : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  have hA : ∫ p in S, H p ∂(μ.prod μ) = ∫ r in s..t, ψ' r * ∫ q in s..r, g q := by
    rw [← integral_indicator hS, integral_prod_symm _ (hH.indicator hS),
      intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hpt : (fun q => S.indicator H (q, r)) =
        fun q => (Set.Iic r).indicator g q * ψ' r := by
      funext q
      by_cases hq : q ≤ r
      · simp [S, H, Set.indicator, hq]
      · simp [S, H, Set.indicator, hq]
    rw [hpt, integral_mul_const, integral_indicator_Iic_Ioc ⟨hr.1.le, hr.2⟩, mul_comm]
  have hB : ∫ p in S, H p ∂(μ.prod μ) = ∫ q in s..t, g q * ∫ r in q..t, ψ' r := by
    rw [← integral_indicator hS, integral_prod _ (hH.indicator hS),
      intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun q hq => ?_
    have hpt : (fun r => S.indicator H (q, r)) =
        fun r => g q * (Set.Ici q).indicator ψ' r := by
      funext r
      by_cases hr : q ≤ r
      · simp [S, H, Set.indicator, hr]
      · simp [S, H, Set.indicator, hr]
    rw [hpt, integral_const_mul, integral_indicator_Ici_Ioc hq]
  rw [← hA, hB]

theorem hasDerivAt_eq_zero_of_vanish {ψ ψ' : ℝ → ℂ} {T : ℝ} (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hT : ∀ t, T < |t| → ψ t = 0) {t : ℝ} (ht : T < |t|) : ψ' t = 0 := by
  have hev : ψ =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
    have hopen : IsOpen {s : ℝ | T < |s|} := isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds ht] with s hs
    exact hT s hs
  exact (hψ t).unique ((hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hev)

theorem integral_eq_interval_of_vanish {f : ℝ → ℂ} {T R : ℝ} (hR : T < R) (hR0 : 0 ≤ R)
    (hf : ∀ t, T < |t| → f t = 0) : ∫ t, f t = ∫ t in -R..R, f t := by
  have hle : -R ≤ R := by linarith
  rw [intervalIntegral.integral_of_le hle]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => hf t ?_).symm
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-- **Integration by parts** against the primitive of an `L¹_loc` function. -/
theorem ibp_primitive {a g ψ ψ' : ℝ → ℂ} {T : ℝ} (hg : ∀ s t, IntervalIntegrable g volume s t)
    (ha : ∀ t, a t = a 0 + ∫ r in (0 : ℝ)..t, g r) (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : Continuous ψ') (hT : ∀ t, T < |t| → ψ t = 0) :
    ∫ t, ψ' t * a t = -∫ t, ψ t * g t := by
  set R := |T| + 1 with hRdef
  have hTR : T < R := by linarith [le_abs_self T]
  have hR0 : 0 < R := by linarith [abs_nonneg T]
  have hle : -R ≤ R := by linarith
  have hψ'0 : ∀ t, T < |t| → ψ' t = 0 := fun t ht => hasDerivAt_eq_zero_of_vanish hψ hT ht
  rw [integral_eq_interval_of_vanish hTR hR0.le (fun t ht => by rw [hψ'0 t ht, zero_mul]),
    integral_eq_interval_of_vanish hTR hR0.le (fun t ht => by rw [hT t ht, zero_mul])]
  have ha' : ∀ t, a t = a (-R) + ∫ r in (-R)..t, g r := by
    intro t
    rw [ha t, ha (-R), add_assoc, ← intervalIntegral.integral_add_adjacent_intervals (hg (-R) 0)
      (hg 0 t), ← add_assoc, ← add_assoc]
    congr 1
    rw [add_assoc, intervalIntegral.integral_symm 0 (-R), add_neg_cancel, add_zero]
  have hGc : Continuous fun t => ∫ r in (-R)..t, g r := intervalIntegral.continuous_primitive hg _
  have hsplit : (∫ t in (-R)..R, ψ' t * a t) =
      (∫ t in (-R)..R, ψ' t * a (-R)) + ∫ t in (-R)..R, ψ' t * ∫ r in (-R)..t, g r := by
    rw [← intervalIntegral.integral_add (f := fun t => ψ' t * a (-R))
      (g := fun t => ψ' t * ∫ r in (-R)..t, g r)
      ((hψ'.mul continuous_const).intervalIntegrable _ _)
      ((hψ'.mul hGc).intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [ha' t]
    ring
  have hFTC : ∀ q, ∫ r in q..R, ψ' r = ψ R - ψ q := fun q =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hψ x) (hψ'.intervalIntegrable _ _)
  have hψR : ψ R = 0 := hT R (by rw [abs_of_pos hR0]; exact hTR)
  rw [hsplit, intervalIntegral.integral_mul_const, hFTC, hψR,
    hT (-R) (by rw [abs_neg, abs_of_pos hR0]; exact hTR), sub_self, zero_mul, zero_add,
    fubini_triangle hle ((hg (-R) R).1) ((hψ'.intervalIntegrable (-R) R).1),
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun q _ => ?_
  rw [hFTC, hψR]
  ring

/-! ### Interaction-picture algebra of one mode -/

theorem hasDerivAt_freePhase (n : ℤ) (t : ℝ) :
    HasDerivAt (fun s => freePhase s n) (-((disp n : ℝ) : ℂ) * Complex.I * freePhase t n) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s * disp n : ℝ) : ℂ)) ((1 * disp n : ℝ) : ℂ) t :=
    ((hasDerivAt_id t).mul_const (disp n)).ofReal_comp
  have h2 := (h1.neg.mul_const Complex.I).cexp
  unfold freePhase
  convert h2 using 1
  simp only [Pi.neg_apply]
  push_cast
  ring

theorem physicalFourier_eq_intA (u : ℝ → PhysicalL2) (n : ℤ) (t : ℝ) :
    physicalFourier (u t) n = freePhase t n * intA u n t := by
  rw [intA, ← mul_assoc, freePhase_mul_neg, one_mul]

theorem mode_lhs_eq (u : ℝ → PhysicalL2) (n : ℤ) (c c' : ℝ → ℂ) :
    (∫ t, (-((disp n : ℝ) : ℂ) * c t - Complex.I * c' t) * physicalFourier (u t) n) =
      -Complex.I * ∫ t, (c' t * freePhase t n +
        c t * (-((disp n : ℝ) : ℂ) * Complex.I * freePhase t n)) * intA u n t := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only
  rw [physicalFourier_eq_intA]
  linear_combination (-((disp n : ℝ) : ℂ) * c t * freePhase t n * intA u n t) * Complex.I_mul_I

theorem mode_rhs_eq (U : ℝ × PhysicalCircle → ℂ) (n : ℤ) (c : ℝ → ℂ) :
    (∫ t, c t * physicalFourier (fun x => cubicNL (U (t, x))) n) =
      Complex.I * ∫ t, (c t * freePhase t n) * intG U n t := by
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [intG]
  linear_combination (c t * physicalFourier (fun x => cubicNL (U (t, x))) n) *
    Complex.I_mul_I + (Complex.I * Complex.I * c t *
      physicalFourier (fun x => cubicNL (U (t, x))) n) * freePhase_mul_neg t n

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
