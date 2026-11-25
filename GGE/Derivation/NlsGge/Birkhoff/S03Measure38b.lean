import NlsGge.Birkhoff.S03Measure38
import NlsGge.Spectral.ActualConvexMomentE02_38
import NlsGge.Spectral.ActualGapActionContinuityE02_38
import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.Spectral.ActualSpectralRemainderE02_38
import NlsGge.Weights.SecondDerivative
import NlsGge.Weights.ComplexEntire

/-! # S03, part 2: the spectral remainder of a field (Birkhoff-free)

v2 lines 289-370 (`A:eq:rates`, `A:eq:remainder`, `A:eq:remainderbound`) and the finite-gap
nonnegativity from `A:lem:convex` (S02, `actualConvexMoment_E02_38`).

Conventions: the gap `g_n(u)` is the closed interval `[lower_n, upper_n]` of the project's labelled
gaps (E02/E03; `lower_n = upper_n` for a closed gap, whose integral is `0`),
`I_n(u) = (2/π) ∫_{g_n} v = actualGapActionAllE02_38 u n`, `a_n = W(2πn) = fullWeightRate c n`.
The remainder of v2 `A:eq:remainder` is the series of differences
`R_W(u) = ∑'_n [ (2/π) ∫_{g_n} W(2λ) v dλ - a_n I_n(u) ]`; it is a `tsum` and is used only after its
summability is established (`remainder38_finiteGap`, S03.06).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.SpectralFoundations NlsGge.Weights
open scoped ENNReal

/-! ### The weight `W` -/

section WeightFacts

variable {lower upper : ℝ} {c : ℕ → ℝ}

theorem weight_differentiable38 (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) : Differentiable ℝ (weight c) := fun r =>
  (weight_hasDerivAt lower upper c hlower hbound hupper r).differentiableAt

theorem weight_continuous38 (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) : Continuous (weight c) :=
  (weight_differentiable38 hlower hbound hupper).continuous

theorem weight_contDiff38 (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) : ContDiff ℝ 2 (weight c) := by
  have hd : Differentiable ℂ (complexWeight c) := fun w =>
    (complexWeight_hasDerivAt lower upper c hlower hbound hupper w).differentiableAt
  have h1 : ContDiff ℂ 2 (complexWeight c) := hd.contDiff
  have h2 : ContDiff ℝ 2 (complexWeight c) := h1.restrict_scalars ℝ
  have h3 : ContDiff ℝ 2 (fun r : ℝ => (complexWeight c (r : ℂ)).re) :=
    Complex.reCLM.contDiff.comp (h2.comp Complex.ofRealCLM.contDiff)
  have : weight c = fun r : ℝ => (complexWeight c (r : ℂ)).re :=
    funext fun r => by
      rw [complexWeight_ofReal lower upper c hlower hbound hupper r]
      simp
  rw [this]; exact h3

/-- `W` is convex (its second derivative is a series of nonnegative terms). -/
theorem weight_convexOn38 (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper) : ConvexOn ℝ Set.univ (weight c) := by
  refine convexOn_univ_of_deriv2_nonneg (weight_differentiable38 hlower hbound hupper)
    (fun r => (weight_deriv_hasDerivAt lower upper c hlower hbound hupper r).differentiableAt)
    (fun x => ?_)
  rw [show deriv^[2] (weight c) x = deriv (deriv (weight c)) x from rfl,
    (weight_deriv_hasDerivAt lower upper c hlower hbound hupper x).deriv]
  refine tsum_nonneg (fun j => ?_)
  unfold weightTermSecondDerivative
  have h1 := (coefficient_pos lower c hlower hbound j).le
  have h2 : (0 : ℝ) ≤ x ^ (2 * j - 2) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · obtain ⟨k, hk⟩ : ∃ k, 2 * j - 2 = 2 * k := ⟨j - 1, by omega⟩
      rw [hk, pow_mul]; positivity
  positivity

end WeightFacts

/-! ### Definitions of the remainder (v2 `A:eq:rates`, `A:eq:remainder`) -/

/-- `(2/π) ∫_{g_n(u)} W(2λ) v(λ;u) dλ`, with `g_n(u)` the closed labelled gap. -/
def gapIntegral38 (c : ℕ → ℝ) (u : PhysicalL2) (n : ℤ) : ℝ :=
  (2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
    weight c (2 * x) * actualGapHeightE02_38 u x

/-- The `n`-th summand `(2/π) ∫_{g_n} W(2λ) v dλ - a_n I_n(u)` of v2 `A:eq:remainder`
(`a_n = W(2πn)`, `I_n` the actual gap action). -/
def remainderSummand38 (c : ℕ → ℝ) (u : PhysicalL2) (n : ℤ) : ℝ :=
  gapIntegral38 c u n - fullWeightRate c n * actualGapActionAllE02_38 u n

/-- `R_W(u) = ∑_n [ ... ]`, the sum of differences of v2 `A:eq:remainder`. Used only where the
series is shown summable. -/
def remainder38 (c : ℕ → ℝ) (u : PhysicalL2) : ℝ := ∑' n : ℤ, remainderSummand38 c u n

theorem fullWeightRate_eq38 (c : ℕ → ℝ) (n : ℤ) :
    fullWeightRate c n = weight c (2 * Real.pi * n) := rfl

theorem actualGapAction_nonneg38 (u : PhysicalL2) (n : ℤ) : 0 ≤ actualGapActionAllE02_38 u n :=
  le_trans (by positivity) (actualGapAction_ge_sq_div_four_all_E02_38 u n)

theorem actualGapLower_le_upper38' (u : PhysicalL2) (n : ℤ) :
    actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
  obtain ⟨⟨y, hy⟩, hset⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
  rw [hset] at hy
  exact hy.1.trans hy.2

/-- The summand is `(2/π)∫_{g_n} (W(2λ) - a_n) v dλ` (agrees with `gapRemainderTermE02_38`). -/
theorem remainderSummand38_eq_integral (c : ℕ → ℝ) (hW : Continuous (weight c)) (u : PhysicalL2)
    (n : ℤ) :
    remainderSummand38 c u n = (2 / Real.pi) *
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (weight c (2 * x) - fullWeightRate c n) * actualGapHeightE02_38 u x := by
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have h1 : IntervalIntegrable (fun x => weight c (2 * x) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    ((hW.comp (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => fullWeightRate c n * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (continuous_const.mul hv).intervalIntegrable _ _
  unfold remainderSummand38 gapIntegral38 actualGapActionAllE02_38
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  ring

theorem remainderSummand38_eq_gapRemainderTerm (c : ℕ → ℝ) (hW : Continuous (weight c))
    (u : PhysicalL2) (n : ℤ) :
    remainderSummand38 c u n = gapRemainderTermE02_38 (weight c) u n :=
  remainderSummand38_eq_integral c hW u n

/-- **Pointwise form of v2 `A:eq:remainderbound`.** If `|W(2λ) - a_n| ≤ K` on the gap then the
`n`-th summand is bounded by `K · I_n(u)`. -/
theorem abs_remainderSummand_le38 (c : ℕ → ℝ) (hW : Continuous (weight c)) (u : PhysicalL2)
    (n : ℤ) (K : ℝ)
    (hK : ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      |weight c (2 * l) - fullWeightRate c n| ≤ K) :
    |remainderSummand38 c u n| ≤ K * actualGapActionAllE02_38 u n := by
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hab := actualGapLower_le_upper38' u n
  rw [remainderSummand38_eq_integral c hW u n, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have hg : IntervalIntegrable (fun x => K * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    (continuous_const.mul hv).intervalIntegrable _ _
  have hle := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun x => (weight c (2 * x) - fullWeightRate c n) * actualGapHeightE02_38 u x)
    (g := fun x => K * actualGapHeightE02_38 u x)
    (Filter.Eventually.of_forall fun t ht => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (actualGapHeightE02_38_nonneg u t)]
      exact mul_le_mul_of_nonneg_right (hK t ⟨ht.1.le, ht.2⟩) (actualGapHeightE02_38_nonneg u t))
    hg
  rw [Real.norm_eq_abs] at hle
  unfold actualGapActionAllE02_38
  rw [intervalIntegral.integral_const_mul] at hle
  calc 2 / Real.pi * |∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (weight c (2 * x) - fullWeightRate c n) * actualGapHeightE02_38 u x|
      ≤ 2 / Real.pi * (K * ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        actualGapHeightE02_38 u x) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-! ### Finite-gap fields: `R_W(u) = E_W(u) - ∑ a_n I_n(u) ≥ 0` (S03.07 input; S02) -/

/-- For a field with finitely many open gaps, `E_W(u) = (2/π)∫_ℝ W(2λ) v dλ` is the (finite) sum
of the gap integrals: `v` vanishes off the open gaps, which are pairwise disjoint. -/
theorem sum_gapIntegral_eq_energy38 (c : ℕ → ℝ) (hW : Continuous (weight c)) (u : PhysicalL2)
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    ∑ n ∈ hfin.toFinset, gapIntegral38 c u n =
      (2 / Real.pi) * ∫ l : ℝ, weight c (2 * l) * actualGapHeightE02_38 u l := by
  set F := hfin.toFinset with hF
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hlev : ∀ n : ℤ, ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
    intro n x hx
    have := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    rw [← this] at hx
    exact hx
  set f : ℝ → ℝ := fun l => weight c (2 * l) * actualGapHeightE02_38 u l with hf
  have hfc : Continuous f := (hW.comp (continuous_const.mul continuous_id)).mul hv
  have hpt : ∀ l : ℝ, f l = ∑ n ∈ F, (Set.Ioo (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n)).indicator f l := by
    intro l
    by_cases h0 : actualGapHeightE02_38 u l = 0
    · have : f l = 0 := by simp [hf, h0]
      rw [this]
      symm; apply Finset.sum_eq_zero; intro n _
      apply Set.indicator_apply_eq_zero.mpr; intro _; simp [hf, h0]
    · obtain ⟨n0, hn0⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u l h0
      have hn0F : n0 ∈ F := by
        rw [hF, Set.Finite.mem_toFinset]; exact hn0.1.trans hn0.2
      rw [Finset.sum_eq_single n0]
      · rw [Set.indicator_of_mem hn0]
      · intro m _ hm
        apply Set.indicator_of_notMem
        intro hmem
        have h1 := hlev n0 l ⟨hn0.1.le, hn0.2.le⟩
        have h2 := hlev m l ⟨hmem.1.le, hmem.2.le⟩
        have : (n0 : ℝ) = m := by
          have := h1.symm.trans h2
          exact mul_right_cancel₀ Real.pi_ne_zero this
        exact hm (by exact_mod_cast this.symm)
      · intro h; exact absurd hn0F h
  have hint : ∀ n ∈ F, Integrable ((Set.Ioo (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n)).indicator f) := by
    intro n _
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact hfc.continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have heq : f = fun l => ∑ n ∈ F, (Set.Ioo (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n)).indicator f l := funext hpt
  have hint2 : ∫ l : ℝ, f l = ∑ n ∈ F, ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), f x := by
    have h1 : ∫ l : ℝ, f l = ∫ l : ℝ, ∑ n ∈ F, (Set.Ioo (actualGapLowerAllE02_38 u n)
        (actualGapUpperAllE02_38 u n)).indicator f l := integral_congr_ae
      (Filter.Eventually.of_forall hpt)
    rw [h1, integral_finsetSum _ hint]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hlt : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
      rw [hF, Set.Finite.mem_toFinset] at hn; exact hn
    rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le hlt.le,
      integral_Ioc_eq_integral_Ioo]
  rw [hint2, Finset.mul_sum]
  rfl

/-- **Finite-gap remainder** (v2 `A:eq:rates` with `A:lem:convex`). For `u ∈ H¹` with finitely many
open gaps, the series `R_W(u)` of `A:eq:remainder` is summable, equals
`E_W(u) - ∑_n a_n I_n(u)` with `E_W(u) = (2/π)∫ W(2λ)v(λ) dλ`, and is nonnegative. -/
theorem remainder38_finiteGap (lower upper : ℝ) (c : ℕ → ℝ) (hlower : 0 < lower)
    (hbound : ∀ j : ℕ, lower ≤ c j) (hupper : ∀ j : ℕ, c j ≤ upper) (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    Summable (fun n : ℤ => remainderSummand38 c u n) ∧
    Summable (fun n : ℤ => fullWeightRate c n * actualGapActionAllE02_38 u n) ∧
    remainder38 c u = (2 / Real.pi) * (∫ l : ℝ, weight c (2 * l) * actualGapHeightE02_38 u l) -
      ∑' n : ℤ, fullWeightRate c n * actualGapActionAllE02_38 u n ∧
    0 ≤ remainder38 c u := by
  have hW := weight_continuous38 hlower hbound hupper
  obtain ⟨-, hsumA, hle⟩ := actualConvexMoment_E02_38 u hu hfin (weight c)
    (weight_contDiff38 hlower hbound hupper) (weight_convexOn38 hlower hbound hupper)
  have hsumA' : Summable (fun n : ℤ => fullWeightRate c n * actualGapActionAllE02_38 u n) := hsumA
  have hG0 : ∀ n ∉ hfin.toFinset, gapIntegral38 c u n = 0 := by
    intro n hn
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at hn
    have : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n :=
      le_antisymm (actualGapLower_le_upper38' u n) hn
    unfold gapIntegral38
    rw [this, intervalIntegral.integral_same, mul_zero]
  have hGs : Summable (fun n : ℤ => gapIntegral38 c u n) := summable_of_ne_finset_zero hG0
  have hsumR : Summable (fun n : ℤ => remainderSummand38 c u n) := hGs.sub hsumA'
  have hE := sum_gapIntegral_eq_energy38 c hW u hfin
  have hGt : ∑' n : ℤ, gapIntegral38 c u n = ∑ n ∈ hfin.toFinset, gapIntegral38 c u n :=
    tsum_eq_sum hG0
  have hR : remainder38 c u = (2 / Real.pi) * (∫ l : ℝ, weight c (2 * l) * actualGapHeightE02_38 u l) -
      ∑' n : ℤ, fullWeightRate c n * actualGapActionAllE02_38 u n := by
    unfold remainder38 remainderSummand38
    rw [hGs.tsum_sub hsumA', hGt, hE]
  have hle' : ∑' n : ℤ, fullWeightRate c n * actualGapActionAllE02_38 u n ≤
      (2 / Real.pi) * ∫ l : ℝ, weight c (2 * l) * actualGapHeightE02_38 u l := hle
  refine ⟨hsumR, hsumA', hR, ?_⟩
  rw [hR]
  linarith

end NlsGge.Birkhoff
end
