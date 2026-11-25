import Mathlib

/-!
# Markov and filter-bias step of the barycentric tail lemma

Support module for `values:lem:tail` (R-CB4CC6EE), covering the final
("Finally") step of the printed proof. With the printed rational filter

  `F_{p,R}(t) = (t^2/(t^2+R^2))^p`,

the pointwise facts used are

* `1_{|t|>R} <= 2^p F_{p,R}(t)` (since `F_{p,R} >= 2^{-p}` on `|t| > R`),
* `0 <= F_{p,R}(t) <= |t|^{2p}/R^{2p}` and `0 <= F_{p,R} <= 1`.

Consequently, for probability measures `nu`, `mu` on `R` with `int |t|^{2p} dmu < oo`
and filter bias `|int F dnu - int F dmu| <= D`,

  `nu(|t| > R) <= 2^p ( (int |t|^{2p} dmu) / R^{2p} + D )`.

The bias bound `D = O(1/(N R))` (Cauchy-transform bias plus the partial-fraction and
Cauchy-estimate step of the printed proof) is NOT proved in this module. It is an
explicit input, to be discharged by the later bias module. No other hypothesis is added.
-/

namespace QuantumNLS.ValuesTailMarkov

open MeasureTheory

noncomputable section

/-- The printed rational filter `F_{p,R}(t) = (t^2/(t^2+R^2))^p`. -/
def filterF (p : ℕ) (R t : ℝ) : ℝ := (t ^ 2 / (t ^ 2 + R ^ 2)) ^ p

lemma den_pos {R : ℝ} (hR : 0 < R) (t : ℝ) : 0 < t ^ 2 + R ^ 2 := by
  have h1 : 0 < R ^ 2 := pow_pos hR 2
  have h2 : 0 ≤ t ^ 2 := sq_nonneg t
  linarith

lemma filterF_nonneg (p : ℕ) (R t : ℝ) : 0 ≤ filterF p R t := by
  unfold filterF
  have h : 0 ≤ t ^ 2 / (t ^ 2 + R ^ 2) := div_nonneg (sq_nonneg t) (by positivity)
  exact pow_nonneg h p

lemma filterF_le_one (p : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) : filterF p R t ≤ 1 := by
  unfold filterF
  have h1 : t ^ 2 / (t ^ 2 + R ^ 2) ≤ 1 := by
    rw [div_le_iff₀ (den_pos hR t)]
    have : 0 < R ^ 2 := pow_pos hR 2
    linarith
  calc (t ^ 2 / (t ^ 2 + R ^ 2)) ^ p ≤ 1 ^ p :=
        pow_le_pow_left₀ (div_nonneg (sq_nonneg t) (den_pos hR t).le) h1 p
    _ = 1 := one_pow p

lemma filterF_lower (p : ℕ) {R t : ℝ} (hR : 0 < R) (ht : R < |t|) :
    (1 / 2 : ℝ) ^ p ≤ filterF p R t := by
  unfold filterF
  have hsq : R ^ 2 ≤ t ^ 2 := by
    have h := sq_abs t
    nlinarith [abs_nonneg t]
  have h1 : (1 / 2 : ℝ) ≤ t ^ 2 / (t ^ 2 + R ^ 2) := by
    rw [le_div_iff₀ (den_pos hR t)]
    linarith
  exact pow_le_pow_left₀ (by norm_num) h1 p

lemma filterF_le_moment (p : ℕ) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    filterF p R t ≤ |t| ^ (2 * p) / (R ^ 2) ^ p := by
  have e : |t| ^ (2 * p) = (t ^ 2) ^ p := by rw [pow_mul, sq_abs]
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have h1 : t ^ 2 / (t ^ 2 + R ^ 2) ≤ t ^ 2 / R ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg t) hR2 (by linarith [sq_nonneg t])
  rw [e, ← div_pow]
  unfold filterF
  exact pow_le_pow_left₀ (div_nonneg (sq_nonneg t) (den_pos hR t).le) h1 p

lemma filterF_continuous (p : ℕ) {R : ℝ} (hR : 0 < R) : Continuous (filterF p R) := by
  unfold filterF
  refine Continuous.pow ?_ p
  exact Continuous.div (by fun_prop) (by fun_prop) (fun t => (den_pos hR t).ne')

lemma filterF_integrable (p : ℕ) {R : ℝ} (hR : 0 < R) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (filterF p R) ν := by
  refine Integrable.of_bound (filterF_continuous p hR).aestronglyMeasurable 1
    (ae_of_all _ fun t => ?_)
  rw [Real.norm_of_nonneg (filterF_nonneg p R t)]
  exact filterF_le_one p hR t

/-- Moment step: `int F dmu <= int |t|^{2p} dmu / R^{2p}` for a probability measure `mu`. -/
lemma integral_filter_le {p : ℕ} {R : ℝ} (hR : 0 < R) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hM : Integrable (fun t : ℝ => |t| ^ (2 * p)) μ) :
    ∫ t, filterF p R t ∂μ ≤ (∫ t, |t| ^ (2 * p) ∂μ) / (R ^ 2) ^ p := by
  have e : ∫ t, |t| ^ (2 * p) / (R ^ 2) ^ p ∂μ = (∫ t, |t| ^ (2 * p) ∂μ) / (R ^ 2) ^ p :=
    integral_div _ _
  rw [← e]
  exact integral_mono (filterF_integrable p hR μ) (hM.div_const _)
    (fun t => filterF_le_moment p hR t)

/-- Markov step with the printed filter: `nu(|t| > R) <= 2^p int F dnu`. -/
lemma tail_le_two_pow_mul_filter {p : ℕ} {R : ℝ} (hR : 0 < R) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    ν.real {t : ℝ | R < |t|} ≤ 2 ^ p * ∫ t, filterF p R t ∂ν := by
  have hs : MeasurableSet {t : ℝ | R < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hind : Integrable (Set.indicator {t : ℝ | R < |t|} (1 : ℝ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator hs
  have hpt : ∀ t, Set.indicator {t : ℝ | R < |t|} (1 : ℝ → ℝ) t ≤ 2 ^ p * filterF p R t := by
    intro t
    by_cases h : R < |t|
    · have hF := filterF_lower p hR h
      have h2 : (2 : ℝ) ^ p * (1 / 2) ^ p = 1 := by rw [← mul_pow]; norm_num
      have h3 : (2 : ℝ) ^ p * (1 / 2) ^ p ≤ 2 ^ p * filterF p R t :=
        mul_le_mul_of_nonneg_left hF (by positivity)
      have h4 : Set.indicator {t : ℝ | R < |t|} (1 : ℝ → ℝ) t = 1 := by
        simp [Set.indicator_apply, h]
      rw [h4]
      linarith
    · have h4 : Set.indicator {t : ℝ | R < |t|} (1 : ℝ → ℝ) t = 0 := by
        simp [Set.indicator_apply, h]
      rw [h4]
      exact mul_nonneg (by positivity) (filterF_nonneg p R t)
  calc ν.real {t : ℝ | R < |t|}
      = ∫ t, Set.indicator {t : ℝ | R < |t|} (1 : ℝ → ℝ) t ∂ν :=
        (integral_indicator_one hs).symm
    _ ≤ ∫ t, 2 ^ p * filterF p R t ∂ν :=
        integral_mono hind ((filterF_integrable p hR ν).const_mul _) hpt
    _ = 2 ^ p * ∫ t, filterF p R t ∂ν := integral_const_mul _ _

/-- **Markov and filter-bias step.** For probability measures `nu`, `mu` on `R` with
finite `2p`-th absolute moment under `mu`, and filter bias `|int F dnu - int F dmu| <= D`,
`nu(|t| > R) <= 2^p ( (int |t|^{2p} dmu)/R^{2p} + D )`.
The bias `D` is an input; its `O(1/(N R))` bound is the remaining bias module. -/
theorem tail_le_of_filter_bias {p : ℕ} {R : ℝ} (hR : 0 < R)
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (hM : Integrable (fun t : ℝ => |t| ^ (2 * p)) μ) {D : ℝ}
    (hD : |(∫ t, filterF p R t ∂ν) - ∫ t, filterF p R t ∂μ| ≤ D) :
    ν.real {t : ℝ | R < |t|} ≤
      2 ^ p * ((∫ t, |t| ^ (2 * p) ∂μ) / (R ^ 2) ^ p + D) := by
  have hF_nu_mu : ∫ t, filterF p R t ∂ν ≤ (∫ t, |t| ^ (2 * p) ∂μ) / (R ^ 2) ^ p + D := by
    have h1 := integral_filter_le hR μ hM
    have h2 : (∫ t, filterF p R t ∂ν) - ∫ t, filterF p R t ∂μ ≤ D :=
      le_trans (le_abs_self _) hD
    linarith
  have hp : (0 : ℝ) ≤ 2 ^ p := by positivity
  calc ν.real {t : ℝ | R < |t|} ≤ 2 ^ p * ∫ t, filterF p R t ∂ν :=
        tail_le_two_pow_mul_filter hR ν
    _ ≤ 2 ^ p * ((∫ t, |t| ^ (2 * p) ∂μ) / (R ^ 2) ^ p + D) :=
        mul_le_mul_of_nonneg_left hF_nu_mu hp

end

end QuantumNLS.ValuesTailMarkov

#print axioms QuantumNLS.ValuesTailMarkov.tail_le_of_filter_bias
