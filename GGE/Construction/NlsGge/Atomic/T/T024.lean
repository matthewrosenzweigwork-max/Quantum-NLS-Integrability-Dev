import NlsGge.Weights.ComplexEntire
import NlsGge.Measure.FourierGaussian

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology

namespace NlsGge.Atomic.T.T024

def lowerWeightNumerator (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  c (j + 1) / ((j + 1 : ℝ) ^ 4)

def B (c : ℕ → ℝ) (r : ℝ) : ℝ :=
  NlsGge.Weights.weight (lowerWeightNumerator c) r

def BComplex (c : ℕ → ℝ) (z : ℂ) : ℂ :=
  NlsGge.Weights.complexWeight (lowerWeightNumerator c) z

def a (c : ℕ → ℝ) (n : ℤ) : ℝ := NlsGge.Measure.fullWeightRate c n

def b (c : ℕ → ℝ) (n : ℤ) : ℝ := B c (2 * Real.pi * (n : ℝ))

private lemma lowerWeight_cPlus_pos
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) :
    0 < cPlus :=
  hcMinus.trans_le ((hcBounds 0).1.trans (hcBounds 0).2)

private lemma lowerWeightNumerator_nonneg
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (j : ℕ) :
    0 ≤ lowerWeightNumerator c j := by
  unfold lowerWeightNumerator
  exact div_nonneg (le_trans hcMinus.le (hcBounds (j + 1)).1) (by positivity)

private lemma lowerWeightNumerator_le_scaled
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (j : ℕ) :
    lowerWeightNumerator c j ≤ (cPlus / cMinus) * c j := by
  have hcPlus : 0 < cPlus := lowerWeight_cPlus_pos cMinus cPlus c hcMinus hcBounds
  have hden : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 4 :=
    one_le_pow₀ (by exact_mod_cast Nat.le_add_left 1 j)
  have hd : lowerWeightNumerator c j ≤ cPlus := by
    unfold lowerWeightNumerator
    apply (div_le_iff₀ (by positivity : 0 < ((j : ℝ) + 1) ^ 4)).2
    calc
      c (j + 1) ≤ cPlus := (hcBounds (j + 1)).2
      _ ≤ cPlus * ((j : ℝ) + 1) ^ 4 := by
        simpa using mul_le_mul_of_nonneg_left hden hcPlus.le
  have hC : 0 ≤ cPlus / cMinus := div_nonneg hcPlus.le hcMinus.le
  calc
    lowerWeightNumerator c j ≤ cPlus := hd
    _ = (cPlus / cMinus) * cMinus := by field_simp [ne_of_gt hcMinus]
    _ ≤ (cPlus / cMinus) * c j := mul_le_mul_of_nonneg_left (hcBounds j).1 hC

private lemma lowerWeightTerm_nonneg
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus)
    (r : ℝ) (j : ℕ) :
    NlsGge.weightTerm (lowerWeightNumerator c) r j ≥ 0 := by
  have hnum := lowerWeightNumerator_nonneg cMinus cPlus c hcMinus hcBounds j
  unfold NlsGge.weightTerm NlsGge.coefficient
  exact mul_nonneg (div_nonneg hnum (by positivity))
    (Even.pow_nonneg (even_two_mul j) r)

private lemma lowerWeightTerm_le_scaled
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus)
    (r : ℝ) (j : ℕ) :
    NlsGge.weightTerm (lowerWeightNumerator c) r j ≤
      (cPlus / cMinus) * NlsGge.weightTerm c r j := by
  have hcoef := lowerWeightNumerator_le_scaled cMinus cPlus c hcMinus hcBounds j
  have hpower : 0 ≤ r ^ (2 * j) := Even.pow_nonneg (even_two_mul j) r
  have hfact : 0 < (Nat.factorial j : ℝ) ^ 4 := by positivity
  unfold NlsGge.weightTerm NlsGge.coefficient
  calc
    lowerWeightNumerator c j / (Nat.factorial j : ℝ) ^ 4 * r ^ (2 * j) ≤
      ((cPlus / cMinus) * c j / (Nat.factorial j : ℝ) ^ 4) * r ^ (2 * j) :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoef (by positivity)) hpower
    _ = (cPlus / cMinus) *
        (c j / (Nat.factorial j : ℝ) ^ 4 * r ^ (2 * j)) := by ring

private lemma lowerWeightTerm_summable
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (r : ℝ) :
    Summable (NlsGge.weightTerm (lowerWeightNumerator c) r) := by
  have hbase := NlsGge.Weights.weightTerm_summable cMinus cPlus c hcMinus
    (fun j => (hcBounds j).1) (fun j => (hcBounds j).2) r
  apply Summable.of_nonneg_of_le
    (fun j => lowerWeightTerm_nonneg cMinus cPlus c hcMinus hcBounds r j)
    (fun j => lowerWeightTerm_le_scaled cMinus cPlus c hcMinus hcBounds r j)
  exact hbase.mul_left (cPlus / cMinus)

private lemma lowerWeightComplexTerm_norm_le
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus)
    (z : ℂ) (j : ℕ) :
    ‖NlsGge.Weights.complexWeightTerm (lowerWeightNumerator c) z j‖ ≤
      (cPlus / cMinus) * NlsGge.weightTerm c ‖z‖ j := by
  have hnum := lowerWeightNumerator_nonneg cMinus cPlus c hcMinus hcBounds j
  have hcoef : 0 ≤ NlsGge.coefficient (lowerWeightNumerator c) j := by
    unfold NlsGge.coefficient
    exact div_nonneg hnum (by positivity)
  have hcoef_le : NlsGge.coefficient (lowerWeightNumerator c) j ≤
      (cPlus / cMinus) * NlsGge.coefficient c j := by
    unfold NlsGge.coefficient
    calc
      lowerWeightNumerator c j / (Nat.factorial j : ℝ) ^ 4 ≤
          ((cPlus / cMinus) * c j) / (Nat.factorial j : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right
          (lowerWeightNumerator_le_scaled cMinus cPlus c hcMinus hcBounds j)
          (show (0 : ℝ) ≤ (Nat.factorial j : ℝ) ^ 4 by positivity)
      _ = (cPlus / cMinus) * (c j / (Nat.factorial j : ℝ) ^ 4) := by ring
  rw [NlsGge.Weights.complexWeightTerm, NlsGge.weightTerm]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef,
    norm_pow]
  calc
    NlsGge.coefficient (lowerWeightNumerator c) j * ‖z‖ ^ (2 * j) ≤
      ((cPlus / cMinus) * NlsGge.coefficient c j) * ‖z‖ ^ (2 * j) :=
        mul_le_mul_of_nonneg_right hcoef_le (by positivity)
    _ = (cPlus / cMinus) *
        (NlsGge.coefficient c j * ‖z‖ ^ (2 * j)) := by ring

private lemma lowerWeightComplexTerm_summable
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (z : ℂ) :
    Summable (NlsGge.Weights.complexWeightTerm (lowerWeightNumerator c) z) := by
  apply Summable.of_norm
  have hbase := NlsGge.Weights.weightTerm_summable cMinus cPlus c hcMinus
    (fun j => (hcBounds j).1) (fun j => (hcBounds j).2) ‖z‖
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => lowerWeightComplexTerm_norm_le cMinus cPlus c hcMinus hcBounds z j)
  exact hbase.mul_left (cPlus / cMinus)

private lemma lowerWeightComplexDerivative_norm_le
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus)
    (R : ℝ) (hR : 1 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (j : ℕ) :
    ‖NlsGge.Weights.complexWeightTermDerivative (lowerWeightNumerator c) z j‖ ≤
      2 * (cPlus / cMinus) * (j : ℝ) ^ 4 * NlsGge.weightTerm c R j := by
  have hnum := lowerWeightNumerator_nonneg cMinus cPlus c hcMinus hcBounds j
  have hcoef : 0 ≤ NlsGge.coefficient (lowerWeightNumerator c) j := by
    unfold NlsGge.coefficient
    exact div_nonneg hnum (by positivity)
  have hcoef_le : NlsGge.coefficient (lowerWeightNumerator c) j ≤
      (cPlus / cMinus) * NlsGge.coefficient c j := by
    unfold NlsGge.coefficient
    calc
      lowerWeightNumerator c j / (Nat.factorial j : ℝ) ^ 4 ≤
          ((cPlus / cMinus) * c j) / (Nat.factorial j : ℝ) ^ 4 :=
        div_le_div_of_nonneg_right
          (lowerWeightNumerator_le_scaled cMinus cPlus c hcMinus hcBounds j)
          (show (0 : ℝ) ≤ (Nat.factorial j : ℝ) ^ 4 by positivity)
      _ = (cPlus / cMinus) * (c j / (Nat.factorial j : ℝ) ^ 4) := by ring
  have hcoefC : 0 ≤ NlsGge.coefficient c j := by
    unfold NlsGge.coefficient
    exact div_nonneg (le_trans hcMinus.le (hcBounds j).1) (by positivity)
  have hscale : 0 ≤ cPlus / cMinus :=
    div_nonneg (lowerWeight_cPlus_pos cMinus cPlus c hcMinus hcBounds).le hcMinus.le
  have hscaledcoef : 0 ≤ (cPlus / cMinus) * NlsGge.coefficient c j :=
    mul_nonneg hscale hcoefC
  have hjpow : (j : ℝ) ≤ (j : ℝ) ^ (4 : ℕ) := by
    by_cases hj : j = 0
    · simp [hj]
    · apply le_self_pow₀
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
      · norm_num
  have hzpow : ‖z‖ ^ (2 * j - 1) ≤ R ^ (2 * j) :=
    (pow_le_pow_left₀ (norm_nonneg z) hz _).trans
      (pow_le_pow_right₀ hR (Nat.sub_le (2 * j) 1))
  simp only [NlsGge.Weights.complexWeightTermDerivative, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef,
    Complex.norm_natCast, Nat.cast_mul, Nat.cast_ofNat, Complex.norm_two, Real.norm_two]
  calc
    NlsGge.coefficient (lowerWeightNumerator c) j * (2 * (j : ℝ)) *
        ‖z‖ ^ (2 * j - 1) ≤
      NlsGge.coefficient (lowerWeightNumerator c) j * (2 * (j : ℝ)) *
        R ^ (2 * j) := by gcongr
    _ ≤ ((cPlus / cMinus) * NlsGge.coefficient c j) *
        (2 * (j : ℝ)) * R ^ (2 * j) := by gcongr <;> positivity
    _ ≤ ((cPlus / cMinus) * NlsGge.coefficient c j) *
        (2 * (j : ℝ) ^ 4) * R ^ (2 * j) := by gcongr <;> positivity
    _ = 2 * (cPlus / cMinus) * (j : ℝ) ^ 4 *
        NlsGge.weightTerm c R j := by
      unfold NlsGge.weightTerm
      ring

private lemma lowerWeightComplexDerivative_majorant_summable
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (R : ℝ) :
    Summable (fun j : ℕ =>
      2 * (cPlus / cMinus) * (j : ℝ) ^ 4 * NlsGge.weightTerm c R j) := by
  simpa only [mul_assoc] using
    (NlsGge.Weights.fourthMoment_summable cMinus cPlus c hcMinus
      (fun j => (hcBounds j).1) (fun j => (hcBounds j).2) R).mul_left
        (2 * (cPlus / cMinus))

private lemma lowerWeightComplexDerivative_summable
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (z : ℂ) :
    Summable (NlsGge.Weights.complexWeightTermDerivative (lowerWeightNumerator c) z) := by
  apply Summable.of_norm
  let R : ℝ := max 1 ‖z‖
  have hR : 1 ≤ R := le_max_left _ _
  have hzR : ‖z‖ ≤ R := le_max_right _ _
  have hmajor := lowerWeightComplexDerivative_majorant_summable
    cMinus cPlus c hcMinus hcBounds R
  exact hmajor.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => lowerWeightComplexDerivative_norm_le cMinus cPlus c hcMinus hcBounds R hR z hzR j)

private lemma lowerWeightComplex_hasDerivAt
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (z : ℂ) :
    HasDerivAt (BComplex c)
      (∑' j, NlsGge.Weights.complexWeightTermDerivative (lowerWeightNumerator c) z j) z := by
  let R : ℝ := max 1 (‖z‖ + 1)
  have hR : 1 ≤ R := le_max_left _ _
  have hzR : ‖z‖ < R := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  have hz : z ∈ Metric.ball (0 : ℂ) R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hzR
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_self]
    linarith
  unfold BComplex
  apply hasDerivAt_tsum_of_isPreconnected
    (lowerWeightComplexDerivative_majorant_summable cMinus cPlus c hcMinus hcBounds R)
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (fun j w hw => NlsGge.Weights.complexWeightTerm_hasDerivAt
      (lowerWeightNumerator c) w j) _ hzero
    (lowerWeightComplexTerm_summable cMinus cPlus c hcMinus hcBounds 0) hz
  intro j w hw
  have hwR : ‖w‖ ≤ R :=
    (by simpa only [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < R).le
  exact lowerWeightComplexDerivative_norm_le cMinus cPlus c hcMinus hcBounds R hR w hwR j

private lemma lowerWeightComplex_analyticAt
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (z : ℂ) :
    AnalyticAt ℂ (BComplex c) z := by
  have hd : Differentiable ℂ (BComplex c) := fun w =>
    (lowerWeightComplex_hasDerivAt cMinus cPlus c hcMinus hcBounds w).differentiableAt
  exact hd.analyticAt z

private lemma lowerWeightTerm_eq_shift
    (c : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    NlsGge.weightTerm c r (j + 1) = r ^ 2 *
      NlsGge.weightTerm (lowerWeightNumerator c) r j := by
  unfold NlsGge.weightTerm NlsGge.coefficient lowerWeightNumerator
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

private lemma lowerWeight_identity
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (r : ℝ) :
    r ^ 2 * B c r = NlsGge.Weights.weight c r - c 0 := by
  have hsumB := lowerWeightTerm_summable cMinus cPlus c hcMinus hcBounds r
  have hsumW := NlsGge.Weights.weightTerm_summable cMinus cPlus c hcMinus
    (fun j => (hcBounds j).1) (fun j => (hcBounds j).2) r
  have htail : (∑' j : ℕ, NlsGge.weightTerm c r (j + 1)) = r ^ 2 * B c r := by
    calc
      (∑' j : ℕ, NlsGge.weightTerm c r (j + 1)) =
          ∑' j : ℕ, r ^ 2 *
            NlsGge.weightTerm (lowerWeightNumerator c) r j := by
        apply tsum_congr
        intro j
        exact lowerWeightTerm_eq_shift c r j
      _ = r ^ 2 * B c r := by
        rw [hsumB.tsum_mul_left]
        rfl
  have hdecomp : NlsGge.Weights.weight c r = c 0 +
      (∑' j : ℕ, NlsGge.weightTerm c r (j + 1)) := by
    unfold NlsGge.Weights.weight
    rw [hsumW.tsum_eq_zero_add]
    simp [NlsGge.weightTerm, NlsGge.coefficient]
  unfold B at htail ⊢
  rw [← htail, hdecomp]
  ring

private lemma lowerWeight_zero (c : ℕ → ℝ) : B c 0 = c 1 := by
  unfold B NlsGge.Weights.weight
  have hsum : HasSum (NlsGge.weightTerm (lowerWeightNumerator c) 0)
      (NlsGge.weightTerm (lowerWeightNumerator c) 0 0) := by
    apply hasSum_single 0
    intro j hj
    simp [NlsGge.weightTerm, NlsGge.coefficient, lowerWeightNumerator, hj]
  rw [hsum.tsum_eq]
  simp [NlsGge.weightTerm, NlsGge.coefficient, lowerWeightNumerator]

private lemma lowerWeight_pos
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (r : ℝ) :
    0 < B c r := by
  have hsum := lowerWeightTerm_summable cMinus cPlus c hcMinus hcBounds r
  have hfirst : 0 < NlsGge.weightTerm (lowerWeightNumerator c) r 0 := by
    have hc1 : 0 < c 1 := hcMinus.trans_le (hcBounds 1).1
    simpa [NlsGge.weightTerm, NlsGge.coefficient, lowerWeightNumerator] using hc1
  have hle := hsum.le_tsum 0
    (fun j hj => lowerWeightTerm_nonneg cMinus cPlus c hcMinus hcBounds r j)
  unfold B
  exact hfirst.trans_le hle

private lemma lowerWeightComplex_ofReal
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) (r : ℝ) :
    BComplex c (r : ℂ) = (B c r : ℂ) := by
  have hreal := lowerWeightTerm_summable cMinus cPlus c hcMinus hcBounds r
  have hcomplex := lowerWeightComplexTerm_summable cMinus cPlus c hcMinus hcBounds (r : ℂ)
  unfold BComplex B NlsGge.Weights.complexWeight NlsGge.Weights.weight
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro j
  simp [NlsGge.Weights.complexWeightTerm, NlsGge.weightTerm, NlsGge.coefficient]

private lemma lowerWeight_ratio_error
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus)
    (n : ℤ) (hn : n ≠ 0) :
    |((2 * Real.pi * (n : ℝ)) ^ 2 * (b c n / a c n)) - 1| ≤
      (cPlus / cMinus) / (2 * Real.pi * (n : ℝ)) ^ 2 := by
  let r : ℝ := 2 * Real.pi * (n : ℝ)
  have ha : 0 < a c n := by
    dsimp [a]
    exact NlsGge.Measure.fullWeightRate_pos cMinus cPlus c hcMinus
      (fun j => (hcBounds j).1) (fun j => (hcBounds j).2) n
  have hcPlus : 0 < cPlus := lowerWeight_cPlus_pos cMinus cPlus c hcMinus hcBounds
  have hc0 : 0 ≤ c 0 := (hcMinus.trans_le (hcBounds 0).1).le
  have hc0up : c 0 ≤ cPlus := (hcBounds 0).2
  have hr : r ≠ 0 := by
    dsimp [r]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Int.cast_ne_zero.mpr hn)
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hid : r ^ 2 * b c n = a c n - c 0 := by
    dsimp [a, b, r]
    exact lowerWeight_identity cMinus cPlus c hcMinus hcBounds
      (2 * Real.pi * (n : ℝ))
  have haLower : cMinus * r ^ 2 ≤ a c n := by
    have hsum := NlsGge.Weights.weightTerm_summable cMinus cPlus c hcMinus
      (fun j => (hcBounds j).1) (fun j => (hcBounds j).2) r
    have hterm : cMinus * r ^ 2 ≤ NlsGge.weightTerm c r 1 := by
      unfold NlsGge.weightTerm NlsGge.coefficient
      simp only [Nat.factorial_one, Nat.cast_one, one_pow, div_one]
      exact mul_le_mul_of_nonneg_right (hcBounds 1).1 (sq_nonneg r)
    have hsumlower := hsum.sum_le_tsum ({1} : Finset ℕ)
      (fun j hj => NlsGge.Weights.weightTerm_nonneg cMinus c
        hcMinus (fun k => (hcBounds k).1) r j)
    have hsingle : (∑ j ∈ ({1} : Finset ℕ), NlsGge.weightTerm c r j) =
        NlsGge.weightTerm c r 1 := by simp
    dsimp [a, NlsGge.Measure.fullWeightRate]
    exact hterm.trans (hsingle ▸ hsumlower)
  have herror :
      |r ^ 2 * (b c n / a c n) - 1| = c 0 / a c n := by
    have hval : r ^ 2 * (b c n / a c n) - 1 = -(c 0 / a c n) := by
      field_simp [ne_of_gt ha]
      nlinarith [hid]
    rw [hval, abs_neg, abs_of_nonneg (div_nonneg hc0 ha.le)]
  have hquot : c 0 / a c n ≤ (cPlus / cMinus) / r ^ 2 := by
    have hquot' : c 0 / a c n ≤ cPlus / (cMinus * r ^ 2) := by
      apply (div_le_div_iff₀ ha (mul_pos hcMinus hr2)).2
      calc
        c 0 * (cMinus * r ^ 2) ≤ cPlus * (cMinus * r ^ 2) :=
          mul_le_mul_of_nonneg_right hc0up (mul_nonneg hcMinus.le hr2.le)
        _ ≤ cPlus * a c n := mul_le_mul_of_nonneg_left haLower hcPlus.le
    calc
      c 0 / a c n ≤ cPlus / (cMinus * r ^ 2) := hquot'
      _ = (cPlus / cMinus) / r ^ 2 := by field_simp [ne_of_gt hcMinus, ne_of_gt hr2]
  simpa [r] using herror ▸ hquot

private lemma lowerWeight_ratio_tendsto
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) :
    Tendsto
      (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * (b c n / a c n))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 (1 : ℝ)) := by
  let l : Filter ℤ := Filter.comap Int.natAbs Filter.atTop
  have hnat : Tendsto Int.natAbs l Filter.atTop := Filter.tendsto_comap
  have hcast : Tendsto (fun n : ℤ => (Int.natAbs n : ℝ)) l Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have hsq : Tendsto (fun n : ℤ => (Int.natAbs n : ℝ) ^ 2) l Filter.atTop :=
    by simpa only [pow_two] using hcast.atTop_mul_atTop₀ hcast
  have hr2 : Tendsto (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2) l Filter.atTop := by
    have hconst : 0 < (2 * Real.pi) ^ 2 := sq_pos_of_ne_zero (by positivity)
    have hm := hsq.const_mul_atTop hconst
    convert hm using 1
    ext n
    have hn : ((Int.natAbs n : ℝ)) = |(n : ℝ)| := by
      calc
        (Int.natAbs n : ℝ) = ((Int.natAbs n : ℤ) : ℝ) := by simp
        _ = ((|n| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
        _ = |(n : ℝ)| := by rw [Int.cast_abs]
    rw [hn]
    simp only [sq_abs]
    ring
  have hinv : Tendsto (fun n : ℤ => ((2 * Real.pi * (n : ℝ)) ^ 2)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hr2
  have hbound : Tendsto
      (fun n : ℤ => (cPlus / cMinus) * ((2 * Real.pi * (n : ℝ)) ^ 2)⁻¹)
      l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := cPlus / cMinus)).mul hinv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := 0)) hbound
  · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
  · filter_upwards [hnat.eventually (eventually_atTop.2 ⟨1, fun n hn => hn⟩)] with n hn
    have hnne : n ≠ 0 := Int.natAbs_ne_zero.mp
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    have herr := lowerWeight_ratio_error cMinus cPlus c hcMinus hcBounds n hnne
    simpa only [Real.norm_eq_abs, div_eq_mul_inv] using herr

theorem lowerWeight_identity_rates
    (cMinus cPlus : ℝ) (c : ℕ → ℝ)
    (hcMinus : 0 < cMinus)
    (hcBounds : ∀ j : ℕ, cMinus ≤ c j ∧ c j ≤ cPlus) :
    (∀ r : ℝ, r ^ 2 * B c r = NlsGge.Weights.weight c r - c 0) ∧
    B c 0 = c 1 ∧
    (∀ r : ℝ, 0 < B c r) ∧
    (∀ z : ℂ, AnalyticAt ℂ (BComplex c) z) ∧
    (∀ r : ℝ, BComplex c (r : ℂ) = (B c r : ℂ)) ∧
    (∀ n : ℤ, n ≠ 0 →
      |((2 * Real.pi * (n : ℝ)) ^ 2 * (b c n / a c n)) - 1| ≤
        (cPlus / cMinus) / (2 * Real.pi * (n : ℝ)) ^ 2) ∧
    Tendsto
      (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * (b c n / a c n))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 (1 : ℝ)) := by
  exact ⟨
    fun r => lowerWeight_identity cMinus cPlus c hcMinus hcBounds r,
    lowerWeight_zero c,
    fun r => lowerWeight_pos cMinus cPlus c hcMinus hcBounds r,
    fun z => lowerWeightComplex_analyticAt cMinus cPlus c hcMinus hcBounds z,
    fun r => lowerWeightComplex_ofReal cMinus cPlus c hcMinus hcBounds r,
    fun n hn => lowerWeight_ratio_error cMinus cPlus c hcMinus hcBounds n hn,
    lowerWeight_ratio_tendsto cMinus cPlus c hcMinus hcBounds⟩

end NlsGge.Atomic.T.T024
