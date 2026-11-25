import NlsGge.Hierarchy.GaussianTailContractionsF06_38
import NlsGge.Hierarchy.RiccatiLocalRemainderPaperForm38
import NlsGge.Measure.CountableReconstruction
import NlsGge.Measure.ActualCountableGaussianFiniteRestriction
import NlsGge.Sobolev.SmoothFourier
import NlsGge.Sobolev.PhysicalProjection
import Mathlib.Tactic

/-! Batch 38, F06-C2a: the finite-order Gaussian tail on `H^{m-1}`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 Filter
open scoped ENNReal Topology ContDiff

section Rates

variable (m : ℕ) (β : ℕ → ℝ)

theorem rate_lower38 (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (n : ℤ) :
    β 0 + β m * (2 * Real.pi * (n : ℝ)) ^ (2 * m) ≤ finiteHierarchyRate38 m β n := by
  unfold finiteHierarchyRate38 finiteHierarchyW38
  rw [Finset.sum_range_succ]
  have h0 : β 0 * (2 * Real.pi * (n : ℝ)) ^ (2 * 0) ≤
      ∑ j ∈ Finset.range m, β j * (2 * Real.pi * (n : ℝ)) ^ (2 * j) :=
    Finset.single_le_sum (f := fun j => β j * (2 * Real.pi * (n : ℝ)) ^ (2 * j))
      (fun j hj => mul_nonneg (hβ j (by have := Finset.mem_range.1 hj; omega))
        (by rw [pow_mul]; positivity)) (Finset.mem_range.2 (by omega))
  simp only [mul_zero, pow_zero, mul_one] at h0
  linarith

theorem rate_pos38 (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m)
    (n : ℤ) : 0 < finiteHierarchyRate38 m β n := by
  have := rate_lower38 m β hm hβ n
  have h2 : 0 ≤ β m * (2 * Real.pi * (n : ℝ)) ^ (2 * m) := by
    rw [pow_mul]; have := hβ m le_rfl; positivity
  linarith

/-- `a_n ≥ c (1+n²)^m` with `c > 0` depending on `m, β`. -/
theorem rate_lower_bracket38 (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0)
    (hM : 0 < β m) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℤ, c * (1 + (n : ℝ) ^ 2) ^ m ≤ finiteHierarchyRate38 m β n := by
  set c' := min (β 0) (β m * (2 * Real.pi) ^ (2 * m)) with hc'
  have hc'pos : 0 < c' := lt_min h0 (by positivity)
  refine ⟨c' / 2 ^ m, by positivity, fun n => ?_⟩
  refine le_trans ?_ (rate_lower38 m β hm hβ n)
  set x : ℝ := (n : ℝ) ^ 2 with hx
  have hx0 : 0 ≤ x := sq_nonneg _
  have h1 : (1 + x) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
    by_cases hx1 : x ≤ 1
    · calc (1 + x) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ ≤ 2 ^ m * (1 + x ^ m) := le_mul_of_one_le_right (by positivity)
            (by have : 0 ≤ x ^ m := by positivity
                linarith)
    · push Not at hx1
      calc (1 + x) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ = 2 ^ m * x ^ m := mul_pow _ _ _
        _ ≤ 2 ^ m * (1 + x ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : β m * (2 * Real.pi * (n : ℝ)) ^ (2 * m) = β m * (2 * Real.pi) ^ (2 * m) * x ^ m := by
    rw [hx, ← pow_mul, mul_pow]
    ring
  rw [h2]
  have h3 : c' ≤ β 0 := min_le_left _ _
  have h4 : c' ≤ β m * (2 * Real.pi) ^ (2 * m) := min_le_right _ _
  have hxm : 0 ≤ x ^ m := by positivity
  calc c' / 2 ^ m * (1 + x) ^ m ≤ c' / 2 ^ m * (2 ^ m * (1 + x ^ m)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c' * (1 + x ^ m) := by field_simp
    _ ≤ β 0 + β m * (2 * Real.pi) ^ (2 * m) * x ^ m := by nlinarith

theorem sobolevWeight_eq38 (k : ℕ) (n : ℤ) :
    sobolevModeWeight (k : ℝ) n = (1 + (n : ℝ) ^ 2) ^ k := by
  unfold sobolevModeWeight
  show (japaneseBracket n) ^ (2 * (k : ℝ)) = _
  rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, pow_mul,
    japaneseBracket_sq]

/-- Target 1: `Σ_n ⟨n⟩^{2(m-1)} / a_n < ∞`. -/
theorem summable_tailRatio38 (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0)
    (hM : 0 < β m) :
    Summable (fun n : ℤ =>
      sobolevModeWeight ((m - 1 : ℕ) : ℝ) n / finiteHierarchyRate38 m β n) := by
  obtain ⟨c, hc, hcn⟩ := rate_lower_bracket38 m β (by omega) hβ h0 hM
  have hs := (summable_japaneseBracket_inv_sq.mul_left (1 / c))
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · exact div_nonneg (by rw [sobolevWeight_eq38]; positivity)
      (rate_pos38 m β (by omega) hβ h0 hM n).le
  · rw [sobolevWeight_eq38, inv_pow, japaneseBracket_sq]
    have hp : 0 < 1 + (n : ℝ) ^ 2 := by positivity
    have hapos := rate_pos38 m β (by omega) hβ h0 hM n
    rw [div_le_iff₀ hapos]
    have hk : (1 + (n : ℝ) ^ 2) ^ m = (1 + (n : ℝ) ^ 2) ^ (m - 1) * (1 + (n : ℝ) ^ 2) := by
      rw [← pow_succ]; congr 1; omega
    have := hcn n
    rw [hk] at this
    have e : 1 / c * (1 + (n : ℝ) ^ 2)⁻¹ * finiteHierarchyRate38 m β n ≥
        1 / c * (1 + (n : ℝ) ^ 2)⁻¹ * (c * ((1 + (n : ℝ) ^ 2) ^ (m - 1) * (1 + (n : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    refine le_trans (le_of_eq ?_) e
    field_simp

end Rates

/-- Borel structure on the Sobolev Hilbert space (none existed). -/
instance sobolevHilbertMeasurableSpace38 (r : ℝ) : MeasurableSpace (SobolevHilbert r) :=
  borel _

instance sobolevHilbertBorelSpace38 (r : ℝ) : BorelSpace (SobolevHilbert r) := ⟨rfl⟩

instance sobolevCarrierMeasurableSpace38 (r : ℝ) : MeasurableSpace (SobolevCarrier38 r) :=
  borel _

instance sobolevCarrierBorelSpace38 (r : ℝ) : BorelSpace (SobolevCarrier38 r) := ⟨rfl⟩

section Realization

local instance fact_one_le_two38 : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

variable (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)]
  [MeasurableSpace (WeightedRealHilbert w)] [BorelSpace (WeightedRealHilbert w)]

/-- Totalized realization of a coefficient sequence in the weighted Hilbert space: the sequence
itself when `Σ w_n |z_n|² < ∞`, else `0`. -/
def seqRealization38 (z : ℤ → ℂ) : WeightedRealHilbert w := by
  classical
  exact if hz : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2) then
    (show WeightedHilbert w from
      ⟨z, (weightedCoordinates_mem_l2_iff w (fun n => (hw.out n).le) z).2 hz⟩)
  else 0

theorem seqRealization_apply38 (z : ℤ → ℂ) (hz : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2))
    (n : ℤ) : (show WeightedHilbert w from seqRealization38 w z) n = z n := by
  simp [seqRealization38, hz]

theorem seqRealization_norm_sq38 (z : ℤ → ℂ) (hz : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)) :
    ‖seqRealization38 w z‖ ^ 2 = ∑' n : ℤ, w n * ‖z n‖ ^ 2 := by
  have h := weightedHilbert_norm_sq w (show WeightedHilbert w from seqRealization38 w z)
  exact h.trans (tsum_congr (fun n => by rw [seqRealization_apply38 w z hz n]))

theorem seqRealization_of_not_summable38 (z : ℤ → ℂ)
    (hz : ¬ Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)) : seqRealization38 w z = 0 := by
  simp [seqRealization38, hz]

def seqPartial38 (N : ℕ) (z : ℤ → ℂ) : WeightedRealHilbert w :=
  (weightedIsometry w).symm
    (∑ n ∈ symmetricModes N, lp.single 2 n (weightedCoordinates w z n))

theorem continuous_seqPartial38 (N : ℕ) : Continuous (seqPartial38 w N) := by
  have hterm (n : ℤ) : Continuous (fun z : ℤ → ℂ =>
      lp.single (E := fun _ : ℤ => ℂ) 2 n (weightedCoordinates w z n)) := by
    have hc : Continuous (fun z : ℤ → ℂ => weightedCoordinates w z n) :=
      continuous_const.mul (continuous_apply n)
    exact (lp.isometry_single (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ) n).continuous.comp hc
  have hsum : Continuous (fun z : ℤ → ℂ =>
      (∑ n ∈ symmetricModes N, lp.single 2 n (weightedCoordinates w z n) :
        lp (fun _ : ℤ => ℂ) 2)) :=
    continuous_finsetSum (symmetricModes N) (fun n _ => hterm n)
  exact (weightedIsometry w).symm.continuous.comp hsum

def seqApprox38 (N : ℕ) (z : ℤ → ℂ) : WeightedRealHilbert w := by
  classical
  exact if Summable (fun n : ℤ => w n * ‖z n‖ ^ 2) then seqPartial38 w N z else 0

theorem measurable_seqApprox38 (N : ℕ) : Measurable (seqApprox38 w N) := by
  classical
  exact Measurable.ite (measurableSet_sequenceSummable w (fun n => (hw.out n).le))
    (continuous_seqPartial38 w N).measurable measurable_const

theorem seqApprox_tendsto38 (z : ℤ → ℂ) :
    Tendsto (fun N : ℕ => seqApprox38 w N z) atTop (𝓝 (seqRealization38 w z)) := by
  classical
  by_cases hz : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)
  · have heq (N : ℕ) : seqPartial38 w N z =
        weightedProjection w (symmetricModes N) (seqRealization38 w z) := by
      unfold seqPartial38 weightedProjection
      apply congrArg (weightedIsometry w).symm
      apply Finset.sum_congr rfl
      intro n _
      apply congrArg (lp.single (E := fun _ : ℤ => ℂ) 2 n)
      change weightedCoordinates w z n = weightedCoordinates w
          (fun j => (show WeightedHilbert w from seqRealization38 w z) j) n
      unfold weightedCoordinates
      exact congrArg (fun value : ℂ => (Real.sqrt (w n) : ℂ) * value)
        (seqRealization_apply38 w z hz n).symm
    have ht := weightedProjection_tendsto w (show WeightedHilbert w from seqRealization38 w z)
    have ht' : Tendsto (fun N : ℕ => (show WeightedRealHilbert w from
          weightedProjection w (symmetricModes N) (seqRealization38 w z))) atTop
          (𝓝 (seqRealization38 w z)) := by
      convert! ht using 1
    simpa [seqApprox38, hz, heq] using ht'
  · simp only [seqApprox38, hz, ↓reduceIte, seqRealization_of_not_summable38 w z hz]
    exact tendsto_const_nhds

theorem measurable_seqRealization38 : Measurable (seqRealization38 w) :=
  measurable_of_tendsto_metrizable (measurable_seqApprox38 w)
    (tendsto_pi_nhds.mpr (seqApprox_tendsto38 w))

end Realization

section Masks

variable (w : ℤ → ℝ) [hw : Fact (∀ n : ℤ, 0 < w n)]
  [MeasurableSpace (WeightedRealHilbert w)] [BorelSpace (WeightedRealHilbert w)]

theorem summable_mask38 (T : Set ℤ) (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)) :
    Summable (fun n : ℤ => w n * ‖T.indicator z n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hw.out n).le (sq_nonneg _))
    (fun n => ?_) hz
  by_cases h : n ∈ T <;> simp [Set.indicator, h] <;>
    exact mul_nonneg (hw.out n).le (sq_nonneg _)

theorem norm_sq_mask_le38 (T : Set ℤ) (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)) :
    ‖seqRealization38 w (T.indicator z)‖ ^ 2 ≤ ‖seqRealization38 w z‖ ^ 2 := by
  rw [seqRealization_norm_sq38 w _ (summable_mask38 w T z hz), seqRealization_norm_sq38 w z hz]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_mask38 w T z hz) hz
  by_cases h : n ∈ T <;> simp [Set.indicator, h] <;>
    exact mul_nonneg (hw.out n).le (sq_nonneg _)

theorem measurable_indicator38 (T : Set ℤ) : Measurable (fun z : ℤ → ℂ => T.indicator z) := by
  classical
  refine measurable_pi_iff.2 (fun n => ?_)
  by_cases h : n ∈ T
  · simp only [Set.indicator, h, ↓reduceIte]; exact measurable_pi_apply n
  · simp only [Set.indicator, h, ↓reduceIte]; exact measurable_const

theorem measurable_maskRealization38 (T : Set ℤ) :
    Measurable (fun z : ℤ → ℂ => seqRealization38 w (T.indicator z)) :=
  (measurable_seqRealization38 w).comp (measurable_indicator38 T)

/-- A coordinate-finite truncation of a mask is the Hilbert projection. -/
theorem seqRealization_projection38 (T : Set ℤ) (s : Finset ℤ) (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => w n * ‖T.indicator z n‖ ^ 2)) :
    seqRealization38 w ((T ∩ (s : Set ℤ)).indicator z) =
      weightedProjection w s (seqRealization38 w (T.indicator z)) := by
  classical
  have hs : Summable (fun n : ℤ => w n * ‖(T ∩ (s : Set ℤ)).indicator z n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hw.out n).le (sq_nonneg _))
      (fun n => ?_) hz
    by_cases h : n ∈ T <;> by_cases h' : n ∈ s <;> simp [Set.indicator, h, h'] <;>
      exact mul_nonneg (hw.out n).le (sq_nonneg _)
  apply Subtype.ext
  funext n
  have h1 := seqRealization_apply38 w _ hs n
  have h2 := weightedProjection_apply w s (show WeightedHilbert w from
    seqRealization38 w (T.indicator z)) n
  have h3 := seqRealization_apply38 w _ hz n
  refine h1.trans (Eq.trans ?_ h2.symm)
  rw [h3]
  by_cases h : n ∈ T <;> by_cases h' : n ∈ s <;> simp [Set.indicator, h, h']

end Masks

section Moments

variable (q : ℤ → ℝ)

theorem integrable_sqNorm_pow38 (n : ℤ) (k : ℕ) :
    Integrable (fun z : ℤ → ℂ => ‖z n‖ ^ (2 * k)) (countableComplexGaussian q) := by
  have h := (measurePreserving_eval_infinitePi
    (fun k : ℤ => complexGaussian (q k)) n).integrable_comp_of_integrable
      (integrable_complexGaussian_norm_pow (q n) (2 * k))
  simpa only [countableComplexGaussian, Function.comp_def, Function.eval] using h

theorem integral_sqNorm_pow38 (hq : ∀ n : ℤ, 0 < q n) (n : ℤ) (k : ℕ) :
    ∫ z : ℤ → ℂ, ‖z n‖ ^ (2 * k) ∂countableComplexGaussian q = k.factorial / q n ^ k := by
  have h := integral_complexGaussian_monomial (q n) (hq n) k k
  have hc : (fun z : ℂ => z ^ k * star z ^ k) = fun z => (((‖z‖ ^ (2 * k) : ℝ)) : ℂ) := by
    funext z
    rw [← mul_pow, show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, pow_mul]
    push_cast; rfl
  rw [hc, integral_complex_ofReal] at h
  simp only [ite_true] at h
  have h2 : ∫ z : ℂ, ‖z‖ ^ (2 * k) ∂complexGaussian (q n) = k.factorial / q n ^ k :=
    Complex.ofReal_injective (by simpa using h)
  have h3 := h2
  rw [← countableComplexGaussian_map_eval q n,
    integral_map (measurable_pi_apply n).aemeasurable (by fun_prop)] at h3
  exact h3

/-- Finite Jensen step. -/
theorem pow_sum_le38 (hq : ∀ n : ℤ, 0 < q n) (w : ℤ → ℝ) (hw : ∀ n : ℤ, 0 < w n)
    (s : Finset ℤ) (k : ℕ) (hk : 1 ≤ k) (x : ℤ → ℝ) (hx : ∀ n, 0 ≤ x n) :
    (∑ n ∈ s, w n * x n) ^ k ≤
      (∑ n ∈ s, w n / q n) ^ (k - 1) * ∑ n ∈ s, (w n / q n) * (q n ^ k * x n ^ k) := by
  classical
  set S := ∑ n ∈ s, w n / q n with hS
  by_cases hs : s = ∅
  · subst hs; simp [Nat.pos_iff_ne_zero.1 hk]
  have hSpos : 0 < S := Finset.sum_pos (fun n _ => div_pos (hw n) (hq n))
    (Finset.nonempty_iff_ne_empty.2 hs)
  have h := Real.pow_arith_mean_le_arith_mean_pow s (fun n => (w n / q n) / S)
    (fun n => q n * x n) (fun n _ => (div_pos (div_pos (hw n) (hq n)) hSpos).le)
    (by rw [← Finset.sum_div, ← hS, div_self hSpos.ne'])
    (fun n _ => mul_nonneg (hq n).le (hx n)) k
  have e1 : ∑ n ∈ s, (w n / q n) / S * (q n * x n) = (∑ n ∈ s, w n * x n) / S := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun n _ => ?_
    have := (hq n).ne'; field_simp
  rw [e1, div_pow] at h
  have e2 : ∑ n ∈ s, (w n / q n) / S * (q n * x n) ^ k =
      (∑ n ∈ s, (w n / q n) * (q n ^ k * x n ^ k)) / S := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_pow]; ring
  rw [e2] at h
  rw [div_le_div_iff₀ (pow_pos hSpos k) hSpos] at h
  have hk' : S ^ k = S ^ (k - 1) * S := by rw [← pow_succ]; congr 1; omega
  rw [hk'] at h
  have := le_of_mul_le_mul_right (by nlinarith [h] : (∑ n ∈ s, w n * x n) ^ k * S ≤
    (S ^ (k - 1) * ∑ n ∈ s, (w n / q n) * (q n ^ k * x n ^ k)) * S) hSpos
  exact this

end Moments

section MomentsFinite

variable (q : ℤ → ℝ)

theorem finiteEnergy_pow_integral_le38 (hq : ∀ n : ℤ, 0 < q n) (w : ℤ → ℝ)
    (hw : ∀ n : ℤ, 0 < w n) (s : Finset ℤ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun z : ℤ → ℂ => (∑ n ∈ s, w n * ‖z n‖ ^ 2) ^ k) (countableComplexGaussian q) ∧
    ∫ z : ℤ → ℂ, (∑ n ∈ s, w n * ‖z n‖ ^ 2) ^ k ∂countableComplexGaussian q ≤
      k.factorial * (∑ n ∈ s, w n / q n) ^ k := by
  set S := ∑ n ∈ s, w n / q n with hS
  set B : (ℤ → ℂ) → ℝ := fun z =>
    S ^ (k - 1) * ∑ n ∈ s, (w n / q n) * (q n ^ k * ‖z n‖ ^ (2 * k)) with hB
  have hBi : Integrable B (countableComplexGaussian q) :=
    (integrable_finsetSum _ fun n _ =>
      ((integrable_sqNorm_pow38 q n k).const_mul (q n ^ k)).const_mul (w n / q n)).const_mul _
  have hF : Measurable (fun z : ℤ → ℂ => (∑ n ∈ s, w n * ‖z n‖ ^ 2) ^ k) := by fun_prop
  have hle : ∀ z : ℤ → ℂ, (∑ n ∈ s, w n * ‖z n‖ ^ 2) ^ k ≤ B z := by
    intro z
    have := pow_sum_le38 q hq w hw s k hk (fun n => ‖z n‖ ^ 2) (fun n => sq_nonneg _)
    simpa only [← pow_mul, hB] using this
  have hnn : ∀ z : ℤ → ℂ, 0 ≤ (∑ n ∈ s, w n * ‖z n‖ ^ 2) ^ k := fun z =>
    pow_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hw n).le (sq_nonneg _)) _
  have hint : Integrable (fun z : ℤ → ℂ => (∑ n ∈ s, w n * ‖z n‖ ^ 2) ^ k)
      (countableComplexGaussian q) :=
    hBi.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hnn z)]; exact hle z)
  refine ⟨hint, ?_⟩
  refine (integral_mono hint hBi hle).trans (le_of_eq ?_)
  rw [hB, integral_const_mul, integral_finsetSum _ (fun n _ =>
      ((integrable_sqNorm_pow38 q n k).const_mul (q n ^ k)).const_mul (w n / q n))]
  have : ∀ n ∈ s, ∫ z : ℤ → ℂ, (w n / q n) * (q n ^ k * ‖z n‖ ^ (2 * k))
      ∂countableComplexGaussian q = k.factorial * (w n / q n) := by
    intro n _
    rw [integral_const_mul, integral_const_mul, integral_sqNorm_pow38 q hq n k]
    have := (hq n).ne'
    field_simp
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← hS]
  rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
  simp only [Nat.add_sub_cancel_left, pow_succ]
  ring

end MomentsFinite

section MomentsInfinite

variable (w : ℤ → ℝ) [hwf : Fact (∀ n : ℤ, 0 < w n)]
  [MeasurableSpace (WeightedRealHilbert w)] [BorelSpace (WeightedRealHilbert w)]

/-- Target 4 core: every mask `T` of the coefficient sequence has finite even moments of the
realized norm, bounded uniformly in `T` by `k! (Σ_n w_n / q_n)^k`. -/
theorem mask_norm_pow_moment38 (q : ℤ → ℝ) (hq : ∀ n : ℤ, 0 < q n)
    (hsum : Summable (fun n : ℤ => w n / q n)) (T : Set ℤ) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun z : ℤ → ℂ => ‖seqRealization38 w (T.indicator z)‖ ^ (2 * k))
      (countableComplexGaussian q) ∧
    ∫ z : ℤ → ℂ, ‖seqRealization38 w (T.indicator z)‖ ^ (2 * k) ∂countableComplexGaussian q ≤
      k.factorial * (∑' n : ℤ, w n / q n) ^ k := by
  have hw : ∀ n, 0 < w n := hwf.out
  set γ := countableComplexGaussian q with hγ
  set f : (ℤ → ℂ) → ℝ := fun z => ‖seqRealization38 w (T.indicator z)‖ ^ (2 * k) with hf
  have hfm : Measurable f := ((measurable_maskRealization38 w T).norm).pow_const _
  have hf0 : ∀ z, 0 ≤ f z := fun z => by positivity
  set G : ℕ → (ℤ → ℂ) → ℝ := fun N z => (∑ n ∈ symmetricModes N, w n * ‖z n‖ ^ 2) ^ k with hG
  have hGm : ∀ N, Measurable (G N) := fun N => by simp only [hG]; fun_prop
  have hpt : ∀ z, ENNReal.ofReal (f z) ≤ liminf (fun N => ENNReal.ofReal (G N z)) atTop := by
    intro z
    by_cases hz : Summable (fun n : ℤ => w n * ‖T.indicator z n‖ ^ 2)
    · have hs := (hz.hasSum).comp symmetricModes_tendsto
      have hfz : f z = (∑' n : ℤ, w n * ‖T.indicator z n‖ ^ 2) ^ k := by
        simp only [hf, pow_mul, seqRealization_norm_sq38 w _ hz]
      have hT : Tendsto (fun N : ℕ => ENNReal.ofReal
          ((∑ n ∈ symmetricModes N, w n * ‖T.indicator z n‖ ^ 2) ^ k)) atTop
          (𝓝 (ENNReal.ofReal (f z))) := by
        rw [hfz]
        exact (ENNReal.tendsto_ofReal ((hs.pow k)))
      rw [← hT.liminf_eq]
      refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun N => ?_)
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Finset.sum_nonneg fun n _ =>
        mul_nonneg (hw n).le (sq_nonneg _)) (Finset.sum_le_sum fun n _ => ?_) k)
      by_cases h : n ∈ T <;> simp [Set.indicator, h] <;>
        exact mul_nonneg (hw n).le (sq_nonneg _)
    · have : f z = 0 := by
        simp only [hf, seqRealization_of_not_summable38 w _ hz, norm_zero]
        rw [zero_pow (by omega)]
      rw [this]; simp
  have hfin := fun N => finiteEnergy_pow_integral_le38 q hq w hw (symmetricModes N) k hk
  have hS : ∀ N, ∑ n ∈ symmetricModes N, w n / q n ≤ ∑' n : ℤ, w n / q n := fun N =>
    hsum.sum_le_tsum _ (fun n _ => (div_pos (hw n) (hq n)).le)
  have hS0 : 0 ≤ ∑' n : ℤ, w n / q n := tsum_nonneg fun n => (div_pos (hw n) (hq n)).le
  have hbound : ∀ N, ∫⁻ z, ENNReal.ofReal (G N z) ∂γ ≤
      ENNReal.ofReal (k.factorial * (∑' n : ℤ, w n / q n) ^ k) := by
    intro N
    rw [← ofReal_integral_eq_lintegral_ofReal (hfin N).1
      (Filter.Eventually.of_forall fun z => pow_nonneg (Finset.sum_nonneg fun n _ =>
        mul_nonneg (hw n).le (sq_nonneg _)) _)]
    refine ENNReal.ofReal_le_ofReal ((hfin N).2.trans ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Finset.sum_nonneg fun n _ =>
      (div_pos (hw n) (hq n)).le) (hS N) k) (by positivity)
  have hL : ∫⁻ z, ENNReal.ofReal (f z) ∂γ ≤
      ENNReal.ofReal (k.factorial * (∑' n : ℤ, w n / q n) ^ k) := by
    calc ∫⁻ z, ENNReal.ofReal (f z) ∂γ
        ≤ ∫⁻ z, liminf (fun N => ENNReal.ofReal (G N z)) atTop ∂γ := lintegral_mono hpt
      _ ≤ liminf (fun N => ∫⁻ z, ENNReal.ofReal (G N z) ∂γ) atTop :=
          lintegral_liminf_le (fun N => (hGm N).ennreal_ofReal)
      _ ≤ _ := Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hbound).frequently
  have hne : ∫⁻ z, ENNReal.ofReal (f z) ∂γ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL
  have hint : Integrable f γ := by
    have := integrable_toReal_of_lintegral_ne_top hfm.ennreal_ofReal.aemeasurable hne
    simpa [ENNReal.toReal_ofReal (hf0 _)] using this
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL

end MomentsInfinite

section Tail

variable (m : ℕ) (β : ℕ → ℝ)

/-- The Gaussian law `γ_m` on coefficient sequences. -/
def gammaM38 : Measure (ℤ → ℂ) := countableComplexGaussian (finiteHierarchyRate38 m β)

instance gammaM38_probability : IsProbabilityMeasure (gammaM38 m β) := by
  unfold gammaM38; infer_instance

/-- Modes with `|n| > N`. -/
def tailSet38 (N : ℕ) : Set ℤ := {n | (N : ℤ) < |n|}

/-- Modes with `N < |n| ≤ N'`. -/
def truncFinset38 (N N' : ℕ) : Finset ℤ :=
  (Finset.Icc (-(N' : ℤ)) (N' : ℤ)).filter (fun n => (N : ℤ) < |n|)

/-- Realization of `U ~ γ_m` in `H^{m-1}`: the coefficient sequence itself when it lies in
`H^{m-1}`, else `0`. -/
def gaussianRealization38 (z : ℤ → ℂ) : SobolevHilbert ((m - 1 : ℕ) : ℝ) :=
  seqRealization38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) z

/-- `Y_N = (Id − P_N) U`: realization of the coefficients with `|n| > N`. -/
def tailRealization38 (N : ℕ) (z : ℤ → ℂ) : SobolevHilbert ((m - 1 : ℕ) : ℝ) :=
  seqRealization38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) ((tailSet38 N).indicator z)

/-- `Y_{N,N'}`: realization of the coefficients with `N < |n| ≤ N'`. -/
def truncRealization38 (N N' : ℕ) (z : ℤ → ℂ) : SobolevHilbert ((m - 1 : ℕ) : ℝ) :=
  seqRealization38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) ((truncFinset38 N N' : Set ℤ).indicator z)

variable {m β}

theorem measurable_gaussianRealization38 : Measurable (gaussianRealization38 m) :=
  measurable_seqRealization38 _

theorem measurable_tailRealization38 (N : ℕ) : Measurable (tailRealization38 m N) :=
  measurable_maskRealization38 _ _

theorem measurable_truncRealization38 (N N' : ℕ) : Measurable (truncRealization38 m N N') :=
  measurable_maskRealization38 _ _

variable (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m)
include hm hβ h0 hM

/-- Almost surely `U ∈ H^{m-1}` (the series converges). -/
theorem ae_summable38 : ∀ᵐ z ∂gammaM38 m β,
    Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2) :=
  ae_sequenceSummable _ _ (fun n => rate_pos38 m β (by omega) hβ h0 hM n)
    (fun n => (Real.rpow_nonneg (japaneseBracket_pos n).le _))
    (summable_tailRatio38 m β hm hβ h0 hM)

/-- Target 2: the realization agrees with the coefficient sequence almost surely. -/
theorem ae_gaussianRealization_apply38 : ∀ᵐ z ∂gammaM38 m β, ∀ n : ℤ,
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      gaussianRealization38 m z) n = z n := by
  filter_upwards [ae_summable38 hm hβ h0 hM] with z hz n
  exact seqRealization_apply38 _ z hz n

/-- Target 3: `Y_N` has coefficients `z n` for `|n| > N` and `0` otherwise, and
`Y_N = U − P_N U` (with `P_N` the Hilbert projection on `|n| ≤ N`). -/
theorem ae_tailRealization_apply38 (N : ℕ) : ∀ᵐ z ∂gammaM38 m β, ∀ n : ℤ,
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      tailRealization38 m N z) n = if (N : ℤ) < |n| then z n else 0 := by
  filter_upwards [ae_summable38 hm hβ h0 hM] with z hz n
  rw [tailRealization38, seqRealization_apply38 _ _ (summable_mask38 _ _ z hz) n]
  by_cases h : (N : ℤ) < |n| <;> simp [Set.indicator, tailSet38, h]

theorem ae_tailRealization_eq_sub38 (N : ℕ) : ∀ᵐ z ∂gammaM38 m β,
    tailRealization38 m N z = gaussianRealization38 m z -
      weightedRealProjectionContinuous (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) (symmetricModes N)
        (gaussianRealization38 m z) := by
  filter_upwards [ae_summable38 hm hβ h0 hM] with z hz
  apply Subtype.ext
  funext n
  have h1 := seqRealization_apply38 _ _ (summable_mask38 _ (tailSet38 N) z hz) n
  have h2 := weightedRealProjection_apply (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
    (symmetricModes N) (gaussianRealization38 m z) n
  have h3 : (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      gaussianRealization38 m z) n = z n := seqRealization_apply38 _ z hz n
  have h1' : (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      tailRealization38 m N z) n = (tailSet38 N).indicator z n := h1
  change (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      tailRealization38 m N z) n =
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      gaussianRealization38 m z) n -
    (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
      weightedRealProjectionContinuous (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
        (symmetricModes N) (gaussianRealization38 m z)) n
  rw [h2, h3, h1']
  by_cases h : (N : ℤ) < |n|
  · have : n ∉ symmetricModes N := by
      simp only [symmetricModes, Finset.mem_Icc]; rw [lt_abs] at h; omega
    simp [Set.indicator, tailSet38, h, this]
  · have : n ∈ symmetricModes N := by
      simp only [symmetricModes, Finset.mem_Icc]; rw [not_lt, abs_le] at h; omega
    simp [Set.indicator, tailSet38, h, this]

end Tail

section TailMoments

variable {m : ℕ} {β : ℕ → ℝ} (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m)
include hm hβ h0 hM

/-- Every mask of the coefficient sequence (in particular `U`, `Y_N`, `Y_{N,N'}`) has all
natural-power moments of its `H^{m-1}` norm finite, with a bound uniform in the mask. -/
theorem mask_moment38 (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : Set ℤ,
      Integrable (fun z : ℤ → ℂ =>
        ‖seqRealization38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) (T.indicator z)‖ ^ p)
        (gammaM38 m β) ∧
      ∫ z : ℤ → ℂ, ‖seqRealization38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) (T.indicator z)‖ ^ p
        ∂gammaM38 m β ≤ C := by
  have hq : ∀ n : ℤ, 0 < finiteHierarchyRate38 m β n :=
    fun n => rate_pos38 m β (by omega) hβ h0 hM n
  have hsum := summable_tailRatio38 m β hm hβ h0 hM
  have hS0 : 0 ≤ ∑' n : ℤ, sobolevModeWeight ((m - 1 : ℕ) : ℝ) n / finiteHierarchyRate38 m β n :=
    tsum_nonneg fun n => div_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _)
      (hq n).le
  refine ⟨1 + ((p + 1).factorial : ℝ) * (∑' n : ℤ, sobolevModeWeight ((m - 1 : ℕ) : ℝ) n /
    finiteHierarchyRate38 m β n) ^ (p + 1), by positivity, fun T => ?_⟩
  obtain ⟨hi, hb⟩ := mask_norm_pow_moment38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ))
    (finiteHierarchyRate38 m β) hq hsum T (p + 1) (by omega)
  have hγ : gammaM38 m β = countableComplexGaussian (finiteHierarchyRate38 m β) := rfl
  rw [← hγ] at hi hb
  set f : (ℤ → ℂ) → ℝ := fun z =>
    ‖seqRealization38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) (T.indicator z)‖ with hf
  have hfm : Measurable f := (measurable_maskRealization38 _ T).norm
  have hle : ∀ z, f z ^ p ≤ 1 + f z ^ (2 * (p + 1)) := by
    intro z
    have h0' : 0 ≤ f z := norm_nonneg _
    by_cases h1 : f z ≤ 1
    · have : f z ^ p ≤ 1 := pow_le_one₀ h0' h1
      have : 0 ≤ f z ^ (2 * (p + 1)) := by positivity
      linarith
    · push Not at h1
      have : f z ^ p ≤ f z ^ (2 * (p + 1)) := pow_le_pow_right₀ h1.le (by omega)
      linarith
  have hi' : Integrable (fun z => 1 + f z ^ (2 * (p + 1))) (gammaM38 m β) :=
    (integrable_const (1 : ℝ)).add hi
  refine ⟨hi'.mono' (hfm.pow_const p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact hle z
  · calc ∫ z, f z ^ p ∂gammaM38 m β ≤ ∫ z, (1 + f z ^ (2 * (p + 1))) ∂gammaM38 m β :=
          integral_mono (hi'.mono' (hfm.pow_const p).aestronglyMeasurable
            (Filter.Eventually.of_forall fun z => by
              rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact hle z)) hi' hle
      _ = 1 + ∫ z, f z ^ (2 * (p + 1)) ∂gammaM38 m β := by
          rw [integral_add (integrable_const _) hi]; simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]; rfl
      _ ≤ _ := by linarith

/-- Target 4 (`E‖Y_N‖^p < ∞`, uniformly in `N`). -/
theorem tailRealization_moment38 (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      Integrable (fun z : ℤ → ℂ => ‖tailRealization38 m N z‖ ^ p) (gammaM38 m β) ∧
      ∫ z : ℤ → ℂ, ‖tailRealization38 m N z‖ ^ p ∂gammaM38 m β ≤ C := by
  obtain ⟨C, hC, h⟩ := mask_moment38 hm hβ h0 hM p
  exact ⟨C, hC, fun N => h (tailSet38 N)⟩

theorem truncRealization_moment38 (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N N' : ℕ,
      Integrable (fun z : ℤ → ℂ => ‖truncRealization38 m N N' z‖ ^ p) (gammaM38 m β) ∧
      ∫ z : ℤ → ℂ, ‖truncRealization38 m N N' z‖ ^ p ∂gammaM38 m β ≤ C := by
  obtain ⟨C, hC, h⟩ := mask_moment38 hm hβ h0 hM p
  exact ⟨C, hC, fun N N' => h (truncFinset38 N N' : Set ℤ)⟩

theorem gaussianRealization_moment38 (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      Integrable (fun z : ℤ → ℂ => ‖gaussianRealization38 m z‖ ^ p) (gammaM38 m β) ∧
      ∫ z : ℤ → ℂ, ‖gaussianRealization38 m z‖ ^ p ∂gammaM38 m β ≤ C := by
  obtain ⟨C, hC, h⟩ := mask_moment38 hm hβ h0 hM p
  refine ⟨C, hC, ?_⟩
  simpa [gaussianRealization38] using h Set.univ

/-- Target 5: almost surely `Y_{N,N'} → Y_N` in `H^{m-1}` as `N' → ∞`, and
`‖Y_{N,N'}‖ ≤ ‖Y_N‖` for every `N'`. -/
theorem ae_trunc_tendsto38 (N : ℕ) : ∀ᵐ z ∂gammaM38 m β,
    Tendsto (fun N' : ℕ => truncRealization38 m N N' z) atTop (𝓝 (tailRealization38 m N z)) ∧
    ∀ N' : ℕ, ‖truncRealization38 m N N' z‖ ≤ ‖tailRealization38 m N z‖ := by
  filter_upwards [ae_summable38 hm hβ h0 hM] with z hz
  have hz' := summable_mask38 _ (tailSet38 N) z hz
  have heq : ∀ N' : ℕ, truncRealization38 m N N' z =
      weightedProjection (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) (symmetricModes N')
        (tailRealization38 m N z) := by
    intro N'
    have hset : ((truncFinset38 N N' : Finset ℤ) : Set ℤ) =
        tailSet38 N ∩ (symmetricModes N' : Set ℤ) := by
      ext n
      simp only [truncFinset38, symmetricModes, tailSet38, Finset.coe_filter, Finset.mem_Icc,
        Set.mem_ofPred_eq, Set.mem_inter_iff, Finset.mem_coe]
      tauto
    unfold truncRealization38 tailRealization38
    rw [hset]
    exact seqRealization_projection38 _ (tailSet38 N) (symmetricModes N') z hz'
  refine ⟨?_, fun N' => ?_⟩
  · simp only [heq]
    exact weightedProjection_tendsto _ (show WeightedHilbert (sobolevModeWeight
      ((m - 1 : ℕ) : ℝ)) from tailRealization38 m N z)
  · rw [heq]
    exact weightedProjection_norm_le _ _ (show WeightedHilbert (sobolevModeWeight
      ((m - 1 : ℕ) : ℝ)) from tailRealization38 m N z)

end TailMoments

section Law

/-- Law of an injectively enumerated finite coordinate block of `γ`, from
`countableComplexGaussian_map_finiteRestriction`. -/
theorem countableComplexGaussian_map_enum38 (q : ℤ → ℝ) (U : Finset ℤ) (e : Fin U.card ≃ U) :
    (countableComplexGaussian q).map (fun z : ℤ → ℂ => fun k : Fin U.card => z (e k)) =
      cgPi (fun k : Fin U.card => q (e k)) := by
  have h1 := countableComplexGaussian_map_finiteRestriction q U
  have h2 := (measurePreserving_arrowCongr' (fun u : U => complexGaussian (q u.1))
    (fun k : Fin U.card => complexGaussian (q (e k).1)) e.symm (MeasurableEquiv.refl ℂ)
    (fun u => by
      simp only [Equiv.apply_symm_apply]
      exact MeasurePreserving.id _))
  have hcomp : (fun z : ℤ → ℂ => fun k : Fin U.card => z (e k)) =
      (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)) ∘ U.restrict := by
    funext z k; rfl
  have hmap := Measure.map_map (μ := countableComplexGaussian q)
    (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)).measurable
    (Finset.measurable_restrict U)
  rw [hcomp, ← hmap, h1, h2.map_eq]

end Law

section TruncLaw

variable {m : ℕ} {β : ℕ → ℝ}

/-- Injective enumeration `Fin K → ℤ` of the truncation block `N < |n| ≤ N'`. -/
def truncIota38 (N N' : ℕ) (k : Fin (truncFinset38 N N').card) : ℤ :=
  (((truncFinset38 N N').equivFin.symm k : truncFinset38 N N') : ℤ)

theorem truncIota_injective38 (N N' : ℕ) : Function.Injective (truncIota38 N N') := by
  intro a b h
  exact (truncFinset38 N N').equivFin.symm.injective (Subtype.ext h)

theorem truncIota_mem38 (N N' : ℕ) (k : Fin (truncFinset38 N N').card) :
    truncIota38 N N' k ∈ truncFinset38 N N' :=
  ((truncFinset38 N N').equivFin.symm k).2

theorem truncIota_gt38 (N N' : ℕ) (k : Fin (truncFinset38 N N').card) :
    (N : ℤ) < |truncIota38 N N' k| := by
  have := truncIota_mem38 N N' k
  simp only [truncFinset38, Finset.mem_filter] at this
  exact this.2

theorem exists_truncIota_eq38 (N N' : ℕ) (n : ℤ) (hn : n ∈ truncFinset38 N N') :
    ∃ k, truncIota38 N N' k = n :=
  ⟨(truncFinset38 N N').equivFin ⟨n, hn⟩, by simp [truncIota38]⟩

/-- Target 6: the law of the coefficients on `{N < |n| ≤ N'}`, enumerated by `ι`, is
`cgPi (a ∘ ι)`. -/
theorem law_truncBlock38 (N N' : ℕ) :
    (gammaM38 m β).map (fun z : ℤ → ℂ => fun k => z (truncIota38 N N' k)) =
      cgPi (fun k => finiteHierarchyRate38 m β (truncIota38 N N' k)) :=
  countableComplexGaussian_map_enum38 (finiteHierarchyRate38 m β) (truncFinset38 N N')
    (truncFinset38 N N').equivFin.symm

/-- The finitely supported coefficient sequence `Σ_k g_k δ_{ι k}`. -/
def finiteSeq38 {K : ℕ} (ι : Fin K → ℤ) (g : Fin K → ℂ) (n : ℤ) : ℂ :=
  ∑ k, if ι k = n then g k else 0

theorem summable_finiteSeq38 (w : ℤ → ℝ) {K : ℕ} (ι : Fin K → ℤ) (g : Fin K → ℂ)
    (hι : Function.Injective ι) : Summable (fun n : ℤ => w n * ‖finiteSeq38 ι g n‖ ^ 2) := by
  apply summable_of_ne_finset_zero (s := Finset.univ.image ι)
  intro n hn
  have : finiteSeq38 ι g n = 0 := by
    unfold finiteSeq38
    refine Finset.sum_eq_zero fun k _ => if_neg ?_
    intro h; exact hn (Finset.mem_image.2 ⟨k, Finset.mem_univ _, h⟩)
  simp [this]

/-- The Sobolev element with coefficient `g_k` at `ι k`. -/
def finiteElement38 (r : ℝ) {K : ℕ} (ι : Fin K → ℤ) (g : Fin K → ℂ) : SobolevHilbert r :=
  seqRealization38 (sobolevModeWeight r) (finiteSeq38 ι g)

theorem measurable_finiteElement38 (r : ℝ) {K : ℕ} (ι : Fin K → ℤ) :
    Measurable (finiteElement38 r ι) := by
  refine (measurable_seqRealization38 _).comp ?_
  refine measurable_pi_iff.2 fun n => ?_
  unfold finiteSeq38
  refine Finset.measurable_sum _ fun k _ => ?_
  by_cases h : ι k = n
  · simp only [h, ↓reduceIte]; exact measurable_pi_apply k
  · simp only [h, ↓reduceIte]; exact measurable_const

theorem finiteElement_apply38 (r : ℝ) {K : ℕ} (ι : Fin K → ℤ) (g : Fin K → ℂ)
    (hι : Function.Injective ι) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from finiteElement38 r ι g) n =
      finiteSeq38 ι g n :=
  seqRealization_apply38 _ _ (summable_finiteSeq38 _ ι g hι) n

theorem finiteSeq_of_inj38 {K : ℕ} (ι : Fin K → ℤ) (g : Fin K → ℂ)
    (hι : Function.Injective ι) (k : Fin K) : finiteSeq38 ι g (ι k) = g k := by
  unfold finiteSeq38
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj; exact if_neg (fun h => hj (hι h))
  · simp

/-- `Y_{N,N'}` is the finite element built from the restriction `(z (ι k))_k`. -/
theorem truncRealization_eq_finiteElement38 (N N' : ℕ) (z : ℤ → ℂ) :
    truncRealization38 m N N' z = finiteElement38 ((m - 1 : ℕ) : ℝ) (truncIota38 N N')
      (fun k => z (truncIota38 N N' k)) := by
  unfold truncRealization38 finiteElement38
  congr 1
  funext n
  by_cases hn : n ∈ truncFinset38 N N'
  · obtain ⟨k, rfl⟩ := exists_truncIota_eq38 N N' n hn
    rw [finiteSeq_of_inj38 _ _ (truncIota_injective38 N N')]
    simp [Set.indicator, hn]
  · have : finiteSeq38 (truncIota38 N N') (fun k => z (truncIota38 N N' k)) n = 0 := by
      unfold finiteSeq38
      refine Finset.sum_eq_zero fun k _ => if_neg ?_
      intro h; exact hn (h ▸ truncIota_mem38 N N' k)
    rw [this]
    simp [Set.indicator, hn]

end TruncLaw

section Bridge

local instance spatialProb38 : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

variable {K : ℕ}

theorem tailField_periodic38 (ι : Fin K → ℤ) (g : Fin K → ℂ) :
    Function.Periodic (tailField38 ι g) 1 := by
  intro x
  unfold tailField38
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (ι k : ℂ) * ((x + 1 : ℝ) : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * (ι k : ℂ) * (x : ℂ) + (ι k : ℂ) * (2 * Real.pi * Complex.I)
      by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem continuous_tailField38 (ι : Fin K → ℤ) (g : Fin K → ℂ) : Continuous (tailField38 ι g) :=
  (contDiff_tailField38 ι g).continuous

/-- The circle representative of `tailField38 ι g` is `Σ_k g_k e_{ι k}`. -/
theorem lift_tailField38 (ι : Fin K → ℤ) (g : Fin K → ℂ) (t : PhysicalCircle) :
    riccatiSmoothPeriodicLiftContinuousMapRecovery30First (tailField38 ι g)
      (continuous_tailField38 ι g) (tailField_periodic38 ι g) t =
      ∑ k, g k * fourier (ι k) t := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective t
  have hmem := toIocMod_mem_Ioc (zero_lt_one' ℝ) 0 y
  have hk := toIocMod_sub_self (zero_lt_one' ℝ) 0 y
  set y' := toIocMod (zero_lt_one' ℝ) 0 y with hy'
  set k := toIocDiv (zero_lt_one' ℝ) 0 y with hkdef
  have hcoe : ((y' : ℝ) : PhysicalCircle) = (y : PhysicalCircle) := by
    rw [QuotientAddGroup.eq]
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk ⊢
    push_cast at hk
    linarith
  have hper : tailField38 ι g y' = tailField38 ι g y := by
    have : y' = y - k • (1 : ℝ) := by
      simp only [zsmul_eq_mul, mul_one] at hk ⊢; push_cast at hk ⊢; linarith
    rw [this]
    exact (tailField_periodic38 ι g).sub_zsmul_eq k
  rw [← hcoe]
  unfold riccatiSmoothPeriodicLiftContinuousMapRecovery30First
  simp only [ContinuousMap.coe_mk]
  rw [AddCircle.liftIoc_coe_apply (by simpa using hmem), hper]
  rw [hcoe]
  unfold tailField38
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fourier_coe_apply]
  simp

/-- Bridge to F06-B/C1: the physical Fourier coefficient of the smooth field `tailField38 ι g`
is `Σ_k g_k [ι k = n]`, i.e. exactly the coefficient sequence of `finiteElement38 r ι g`. -/
theorem smoothFourier_tailField38 (ι : Fin K → ℤ) (g : Fin K → ℂ)
    (hu : ContDiff ℝ ∞ (tailField38 ι g)) (hper : Function.Periodic (tailField38 ι g) 1)
    (n : ℤ) : smoothFourier38 (tailField38 ι g) hu hper n = finiteSeq38 ι g n := by
  classical
  unfold smoothFourier38 physicalFourier
  rw [fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) spatialMeasure
    (riccatiSmoothPeriodicLiftContinuousMapRecovery30First (tailField38 ι g) hu.continuous hper))]
  have hf : (⇑(riccatiSmoothPeriodicLiftContinuousMapRecovery30First (tailField38 ι g)
      hu.continuous hper) : PhysicalCircle → ℂ) =
      ∑ k, fun t : PhysicalCircle => g k * fourier (ι k) t := by
    funext t
    rw [lift_tailField38 ι g t, Finset.sum_apply]
  rw [hf]
  have hint : ∀ k ∈ (Finset.univ : Finset (Fin K)),
      Integrable (fun t : PhysicalCircle => g k * fourier (ι k) t) spatialMeasure := by
    intro k _
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _)
  have h := congrFun (fourierCoeff.sum Finset.univ
    (fun k : Fin K => fun t : PhysicalCircle => g k * fourier (ι k) t) hint) n
  rw [h]
  simp only [Finset.sum_apply, fourierCoeff.const_mul, fourierCoeff_fourier, finiteSeq38]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : ι k = n
  · subst hk; simp
  · simp [hk, Pi.single_apply, Ne.symm hk]


/-- The `hsource` hypothesis of `localRemainderSobolev38_smooth` (F03) for the finite tail
element `finiteElement38 r ι g` and the smooth field `tailField38 ι g`. -/
theorem finiteElement_hsource38 (r : ℝ) (ι : Fin K → ℤ) (g : Fin K → ℂ)
    (hι : Function.Injective ι) (hu : ContDiff ℝ ∞ (tailField38 ι g))
    (hper : Function.Periodic (tailField38 ι g) 1) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from finiteElement38 r ι g) n =
      smoothFourier38 (tailField38 ι g) hu hper n := by
  rw [finiteElement_apply38 r ι g hι n, smoothFourier_tailField38 ι g hu hper n]


end Bridge

end NlsGge.HierarchyRiccati.Core
