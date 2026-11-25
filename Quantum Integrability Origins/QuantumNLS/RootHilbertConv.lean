import Mathlib
import QuantumNLS.RootHilbertTruncations
import QuantumNLS.HilbertMultiplier

/-!
# R-064239ED: the convolutions `K_{a,b} * ρ`, their Fourier transforms and the Parseval energy bound

For `ρ` with `HilbertHyp ρ` and `ρc = (ρ : ℂ)`:
* `Gc a b = K_{a,b} ⋆ ρc` is integrable, bounded by `‖ρ‖₁/a`, in `L²`, and equals the real truncated integral
  `Tr ρ a b x = ∫_{a<|t|<b} ρ(x−t)/t dt` (`Gc_eq`);
* `|Tr ρ ε R x − H_ε ρ(x)| ≤ ‖ρ‖₁/R` (`abs_Tr_sub_le`) — "the convolution differs pointwise from `H_ε ρ` by at most `‖ρ‖₁/R`";
* `𝓕 (Gc a b) = 𝓕 K_{a,b} · 𝓕 ρc` (convolution theorem, Mathlib) and, by Parseval (`RealFourierInfra`),
  `∫‖Gc a' R − Gc a R‖² ≤ E(a − a') := ∫ (2 min(4, 2π|ξ|(a−a')))² ‖ρ̂(ξ)‖²` and `∫‖Gc a R‖² ≤ 64 ∫ ρ²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform ENNReal NNReal Convolution

namespace QuantumNLS.RootHilbert

/-- `ρ` as a complex-valued function. -/
def rhoc (ρ : ℝ → ℝ) : ℝ → ℂ := fun x => ((ρ x : ℝ) : ℂ)

/-- The convolution `K_{a,b} ⋆ ρ`. -/
def Gc (ρ : ℝ → ℝ) (a b : ℝ) : ℝ → ℂ :=
  convolution (Kc a b) (rhoc ρ) (ContinuousLinearMap.lsmul ℂ ℂ) volume

/-- Real truncated Hilbert integral over the annulus `a < |t| < b`. -/
def Tr (ρ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∫ t, {t : ℝ | a < |t| ∧ |t| < b}.indicator (fun t => ρ (x - t) / t) t

theorem integrable_rhoc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) : Integrable (rhoc ρ) (volume : Measure ℝ) :=
  hρ.integrable.ofReal

theorem Gc_eq (ρ : ℝ → ℝ) (a b x : ℝ) : Gc ρ a b x = ((Tr ρ a b x : ℝ) : ℂ) := by
  unfold Gc Tr convolution
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
  by_cases h : a < |t| ∧ |t| < b
  · simp only [ContinuousLinearMap.lsmul_apply, rhoc, Kc,
      Set.indicator_of_mem (show t ∈ {t : ℝ | a < |t| ∧ |t| < b} from h), smul_eq_mul]
    push_cast
    ring
  · simp only [ContinuousLinearMap.lsmul_apply, rhoc, Kc,
      Set.indicator_of_notMem (show t ∉ {t : ℝ | a < |t| ∧ |t| < b} from h), smul_eq_mul]
    simp


theorem HilbertHyp.continuous {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) : Continuous ρ := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨s, hs, C, r, hr, -, hH⟩ := hρ.holder x
  exact (hH.continuousOn hr).continuousAt hs

theorem HilbertHyp.ae_le {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) : ∃ M : ℝ, ∀ᵐ x ∂(volume : Measure ℝ), ρ x ≤ M := by
  refine ⟨(eLpNormEssSup ρ (volume : Measure ℝ)).toReal, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := ρ) (μ := (volume : Measure ℝ))] with x hx
  have hfin : eLpNormEssSup ρ (volume : Measure ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top hρ.linfty.eLpNorm_lt_top.ne eLpNormEssSup_le_eLpNorm_top
  have h3 : ‖ρ x‖ ≤ (eLpNormEssSup ρ (volume : Measure ℝ)).toReal := by
    have := ENNReal.toReal_mono hfin hx
    simpa using this
  exact (le_abs_self _).trans (by simpa using h3)

theorem memLp_two_of_bdd {f : ℝ → ℂ} (hi : Integrable f (volume : Measure ℝ)) (C : ℝ)
    (hb : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ ≤ C) : MemLp f 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm hi.1]
  refine Integrable.mono' (hi.norm.const_mul C) (hi.1.norm.mul hi.1.norm |>.congr ?_) ?_
  · exact Eventually.of_forall (fun x => by simp [sq])
  · filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem memLp_rhoc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) : MemLp (rhoc ρ) 2 (volume : Measure ℝ) := by
  obtain ⟨M, hM⟩ := hρ.ae_le
  refine memLp_two_of_bdd (integrable_rhoc hρ) M ?_
  filter_upwards [hM] with x hx
  simp only [rhoc, Complex.norm_real, Real.norm_eq_abs]
  exact (abs_of_nonneg (hρ.nonneg x)).le.trans hx

/-- A truncated Hilbert integral over a set `S` on which `|t| ≥ ε > 0` is bounded by `‖ρ‖₁/ε`. -/
theorem abs_int_ind_le {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {ε : ℝ} (hε : 0 < ε) (S : Set ℝ)
    (hS : MeasurableSet S) (hSε : ∀ t ∈ S, ε ≤ |t|) (x : ℝ) :
    |∫ t, S.indicator (fun t => ρ (x - t) / t) t| ≤ (∫ y, ρ y) / ε := by
  have hint : Integrable (fun t => ρ (x - t)) (volume : Measure ℝ) := hρ.integrable.comp_sub_left x
  have hmeas : Measurable (S.indicator (fun t => ρ (x - t) / t)) :=
    ((hρ.continuous.comp (continuous_const.sub continuous_id)).measurable.div measurable_id).indicator hS
  have hbd : ∀ t, ‖S.indicator (fun t => ρ (x - t) / t) t‖ ≤ ρ (x - t) / ε := by
    intro t
    by_cases ht : t ∈ S
    · rw [Set.indicator_of_mem ht, Real.norm_eq_abs, abs_div, abs_of_nonneg (hρ.nonneg _)]
      exact div_le_div_of_nonneg_left (hρ.nonneg _) hε (hSε t ht)
    · rw [Set.indicator_of_notMem ht, norm_zero]
      exact div_nonneg (hρ.nonneg _) hε.le
  have h1 : ‖∫ t, S.indicator (fun t => ρ (x - t) / t) t‖ ≤ ∫ t, ρ (x - t) / ε :=
    norm_integral_le_of_norm_le (hint.div_const ε) (Eventually.of_forall hbd)
  have h2 : ∫ t, ρ (x - t) / ε = (∫ y, ρ y) / ε := by
    rw [integral_div, integral_sub_left_eq_self (fun t => ρ t) (volume : Measure ℝ) x]
  rw [← Real.norm_eq_abs]
  linarith

theorem measurableSet_ge_abs (R : ℝ) : MeasurableSet {t : ℝ | R ≤ |t|} :=
  measurableSet_le measurable_const continuous_abs.measurable

theorem measurableSet_gt_abs (R : ℝ) : MeasurableSet {t : ℝ | R < |t|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

theorem abs_Tr_le {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    |Tr ρ a b x| ≤ (∫ y, ρ y) / a :=
  abs_int_ind_le hρ ha _ (measurableSet_Kc a b) (fun t ht => ht.1.le) x

theorem norm_Gc_le {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    ‖Gc ρ a b x‖ ≤ (∫ y, ρ y) / a := by
  rw [Gc_eq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_Tr_le hρ ha b x

theorem integrable_ind {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {ε : ℝ} (hε : 0 < ε) (S : Set ℝ)
    (hS : MeasurableSet S) (hSε : ∀ t ∈ S, ε ≤ |t|) (x : ℝ) :
    Integrable (S.indicator (fun t => ρ (x - t) / t)) (volume : Measure ℝ) := by
  have hint : Integrable (fun t => ρ (x - t)) (volume : Measure ℝ) := hρ.integrable.comp_sub_left x
  have hmeas : Measurable (S.indicator (fun t => ρ (x - t) / t)) :=
    ((hρ.continuous.comp (continuous_const.sub continuous_id)).measurable.div measurable_id).indicator hS
  refine Integrable.mono' (hint.div_const ε) hmeas.aestronglyMeasurable (Eventually.of_forall (fun t => ?_))
  by_cases ht : t ∈ S
  · rw [Set.indicator_of_mem ht, Real.norm_eq_abs, abs_div, abs_of_nonneg (hρ.nonneg _)]
    exact div_le_div_of_nonneg_left (hρ.nonneg _) hε (hSε t ht)
  · rw [Set.indicator_of_notMem ht, norm_zero]
    exact div_nonneg (hρ.nonneg _) hε.le

/-- `|H_ε ρ(x) - Tr ρ ε R x| ≤ ‖ρ‖₁ / R` for `0 < ε < R`. -/
theorem abs_hilbertTrunc_sub_Tr_le {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (x : ℝ) : |hilbertTrunc ρ ε x - Tr ρ ε R x| ≤ (∫ y, ρ y) / R := by
  have hR : 0 < R := hε.trans hεR
  rw [hilbertTrunc_eq]
  unfold Tr
  have h1 := integrable_ind hρ hε {t : ℝ | ε < |t|} (measurableSet_gt_abs ε) (fun t ht => ht.le) x
  have h2 := integrable_ind hρ hε {t : ℝ | ε < |t| ∧ |t| < R} (measurableSet_Kc ε R)
    (fun t ht => ht.1.le) x
  rw [← integral_sub h1 h2]
  have hfun : (fun t => {t : ℝ | ε < |t|}.indicator (fun t => ρ (x - t) / t) t -
      {t : ℝ | ε < |t| ∧ |t| < R}.indicator (fun t => ρ (x - t) / t) t) =
      {t : ℝ | R ≤ |t|}.indicator (fun t => ρ (x - t) / t) := by
    funext t
    by_cases h : R ≤ |t|
    · have a1 : t ∈ {t : ℝ | ε < |t|} := lt_of_lt_of_le hεR h
      have a2 : t ∉ {t : ℝ | ε < |t| ∧ |t| < R} := fun h' => absurd h'.2 (not_lt.mpr h)
      have a3 : t ∈ {t : ℝ | R ≤ |t|} := h
      rw [Set.indicator_of_mem a1, Set.indicator_of_notMem a2, Set.indicator_of_mem a3, sub_zero]
    · have hlt : |t| < R := not_le.mp h
      have a3 : t ∉ {t : ℝ | R ≤ |t|} := h
      rw [Set.indicator_of_notMem a3]
      by_cases h' : ε < |t|
      · have a1 : t ∈ {t : ℝ | ε < |t|} := h'
        have a2 : t ∈ {t : ℝ | ε < |t| ∧ |t| < R} := ⟨h', hlt⟩
        rw [Set.indicator_of_mem a1, Set.indicator_of_mem a2, sub_self]
      · have a1 : t ∉ {t : ℝ | ε < |t|} := h'
        have a2 : t ∉ {t : ℝ | ε < |t| ∧ |t| < R} := fun h'' => h' h''.1
        rw [Set.indicator_of_notMem a1, Set.indicator_of_notMem a2, sub_self]
  rw [hfun]
  exact abs_int_ind_le hρ hR _ (measurableSet_ge_abs R) (fun t ht => ht) x

end QuantumNLS.RootHilbert
