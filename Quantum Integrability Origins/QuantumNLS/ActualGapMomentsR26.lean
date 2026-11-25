import QuantumNLS.F03ActualProb

/-! The truncated variance and bounded phase estimate, with the occupation weight retained. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace QuantumNLS.ActualGapMomentsR26
open BornConvergence (TendstoInProbability)
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, DiscreteMeasurableSpace (Ω n)]

def variance (P : ∀ n, Measure (Ω n)) (g weight : ∀ n, Ω n → ℝ)
    (A : ∀ n, Set (Ω n)) (w : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((A n).indicator (fun x => weight n x * |g n x - w| ^ 2) x) ∂P n

def phaseError (P : ∀ n, Measure (Ω n)) (g weight : ∀ n, Ω n → ℝ)
    (B : ∀ n, Set (Ω n)) (w T : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((B n).indicator
    (fun x => weight n x * min 4 (T ^ 2 * |g n x - w| ^ 2)) x) ∂P n

/-- In particular the good-event variance is a finite real expectation. -/
theorem variance_bound (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (g weight : ∀ n, Ω n → ℝ) (A : ∀ n, Set (Ω n)) (w K : ℝ)
    (_hw0 : ∀ n x, 0 ≤ weight n x) (hw1 : ∀ n x, weight n x ≤ 1)
    (hK : ∀ n x, x ∈ A n → |g n x| ≤ K) (n : ℕ) :
    variance P g weight A w n ≤ ENNReal.ofReal ((|K| + |w|) ^ 2) := by
  have hp : ∀ x, (A n).indicator (fun x => weight n x * |g n x - w| ^ 2) x ≤ (|K| + |w|) ^ 2 := by
    intro x
    by_cases hx : x ∈ A n
    · rw [indicator_of_mem hx]
      have hh : |g n x - w| ≤ |K| + |w| := by
        have h1 := abs_sub (g n x) w
        have h2 := (hK n x hx).trans (le_abs_self K)
        linarith
      exact (mul_le_of_le_one_left (sq_nonneg _) (hw1 n x)).trans (pow_le_pow_left₀ (abs_nonneg _) hh 2)
    · rw [indicator_of_notMem hx]; positivity
  refine (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp x)).trans_eq ?_
  simp only [lintegral_const,measure_univ,mul_one]

/-- The phase error is bounded independently of every untruncated gap moment. -/
theorem phase_le_four (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (g weight : ∀ n, Ω n → ℝ) (B : ∀ n, Set (Ω n)) (w T : ℝ)
    (hw0 : ∀ n x, 0 ≤ weight n x) (hw1 : ∀ n x, weight n x ≤ 1) (n : ℕ) :
    phaseError P g weight B w T n ≤ 4 := by
  have hp : ∀ x, (B n).indicator (fun x => weight n x * min 4 (T ^ 2 * |g n x - w| ^ 2)) x ≤ 4 := by
    intro x
    by_cases hx : x ∈ B n
    · rw [indicator_of_mem hx]
      exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (hw0 n x)).trans (by nlinarith [hw1 n x])
    · rw [indicator_of_notMem hx]; norm_num
  refine (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp x)).trans_eq ?_
  simp only [lintegral_const,measure_univ,mul_one,ENNReal.ofReal_ofNat]

/-- Bounded convergence in probability on the good event suffices; no gap moment off it is used. -/
theorem variance_limit (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (g weight : ∀ n, Ω n → ℝ) (A : ∀ n, Set (Ω n)) (w K : ℝ)
    (hw0 : ∀ n x, 0 ≤ weight n x) (hw1 : ∀ n x, weight n x ≤ 1)
    (hK : ∀ n x, x ∈ A n → |g n x| ≤ K)
    (hg : TendstoInProbability P g w) :
    Tendsto (variance P g weight A w) atTop (𝓝 0) := by
  let X : ∀ n, Ω n → ℝ := fun n => (A n).indicator (fun x => weight n x * |g n x - w| ^ 2)
  have hX0 : ∀ n x, 0 ≤ X n x := fun n x => indicator_nonneg (fun x _ => mul_nonneg (hw0 n x) (sq_nonneg _)) x
  have hXle : ∀ n x, X n x ≤ |g n x - w| ^ 2 := by
    intro n x
    by_cases hx : x ∈ A n
    · simp only [X,indicator_of_mem hx]
      exact mul_le_of_le_one_left (sq_nonneg _) (hw1 n x)
    · simp only [X,indicator_of_notMem hx]; positivity
  have hX : TendstoInProbability P X 0 := by
    have hsq : TendstoInProbability P (fun n x => |g n x - w| ^ 2) 0 := by
      have hh := hg.comp_continuousAt (g := fun t : ℝ => |t - w| ^ 2) (by fun_prop)
      simpa using hh
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hsq ε hε)
      (fun _ => bot_le) (fun n => measure_mono fun x hx => ?_)
    simp only [mem_ofPred_eq,Real.dist_eq,sub_zero,abs_of_nonneg (hX0 n x)] at hx ⊢
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hx.trans_le (hXle n x)
  have hb : ∀ n x, X n x ≤ (|K| + |w|) ^ 2 := by
    intro n x
    by_cases hx : x ∈ A n
    · have hh : |g n x - w| ≤ |K| + |w| := by
        have h1 := abs_sub (g n x) w
        have h2 := (hK n x hx).trans (le_abs_self K)
        linarith
      exact (hXle n x).trans (pow_le_pow_left₀ (abs_nonneg _) hh 2)
    · simp only [X,indicator_of_notMem hx]; positivity
  exact F03ActualProb.tendsto_lintegral_of_dom P X (fun _ _ => 0)
    (fun _ => Measurable.of_discrete) (fun _ => measurable_const)
    0 ((|K| + |w|) ^ 2) 0 le_rfl
    (by simpa using hb) (fun _ => integrable_const 0)
    (by simp) hX

/-- Elementary phase truncation. The bound is valid for an arbitrary donor event `B`. -/
theorem phase_bound (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (g weight : ∀ n, Ω n → ℝ) (A B : ∀ n, Set (Ω n)) (w T : ℝ)
    (hw0 : ∀ n x, 0 ≤ weight n x) (hw1 : ∀ n x, weight n x ≤ 1) (n : ℕ) :
    phaseError P g weight B w T n ≤ ENNReal.ofReal (T ^ 2) * variance P g weight A w n +
      4 * P n (A n)ᶜ := by
  have hpoint : ∀ x, ENNReal.ofReal ((B n).indicator
      (fun x => weight n x * min 4 (T ^ 2 * |g n x - w| ^ 2)) x) ≤
      ENNReal.ofReal (T ^ 2) * ENNReal.ofReal ((A n).indicator
        (fun x => weight n x * |g n x - w| ^ 2) x) +
      ((A n)ᶜ).indicator (fun _ => (4 : ℝ≥0∞)) x := by
    intro x
    by_cases hxA : x ∈ A n
    · rw [indicator_of_notMem (show x ∉ (A n)ᶜ from not_not_intro hxA),add_zero,
        indicator_of_mem hxA,← ENNReal.ofReal_mul (sq_nonneg T)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hxB : x ∈ B n
      · rw [indicator_of_mem hxB]
        calc weight n x * min 4 (T ^ 2 * |g n x - w| ^ 2)
            ≤ weight n x * (T ^ 2 * |g n x - w| ^ 2) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) (hw0 n x)
          _ = _ := by ring
      · rw [indicator_of_notMem hxB]
        exact mul_nonneg (sq_nonneg T) (mul_nonneg (hw0 n x) (sq_nonneg _))
    · rw [indicator_of_notMem hxA,ENNReal.ofReal_zero,mul_zero,zero_add,
        indicator_of_mem (show x ∈ (A n)ᶜ from hxA)]
      suffices hh : (B n).indicator (fun x => weight n x * min 4 (T ^ 2 * |g n x - w| ^ 2)) x ≤ (4 : ℝ) by
        exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by norm_num)
      by_cases hxB : x ∈ B n
      · rw [indicator_of_mem hxB]
        calc weight n x * min 4 (T ^ 2 * |g n x - w| ^ 2) ≤ weight n x * 4 :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (hw0 n x)
          _ ≤ 4 := by nlinarith [hw1 n x]
      · rw [indicator_of_notMem hxB]; norm_num
  refine (lintegral_mono hpoint).trans_eq ?_
  rw [lintegral_add_left (Measurable.of_discrete),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator_const MeasurableSet.of_discrete]
  rfl

end QuantumNLS.ActualGapMomentsR26
#print axioms QuantumNLS.ActualGapMomentsR26.variance_limit
#print axioms QuantumNLS.ActualGapMomentsR26.phase_bound
