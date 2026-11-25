import NlsGge.Analysis.IntegerTails

/-! Concrete numerical NEW-F02.05 convolution leaves. No operator realization is asserted. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis

/-- Exact r+s=t indexing, with the resonant r=0 and s=0 terms equal to zero. -/
def convolutionTerm (t r : ℤ) : ℝ := inverseSquare r * inverseSquare (t - r)

def inverseSquareConvolution (t : ℤ) : ℝ := ∑' r : ℤ, convolutionTerm t r

theorem convolutionTerm_nonneg (t r : ℤ) : 0 ≤ convolutionTerm t r :=
  mul_nonneg (inverseSquare_nonneg r) (inverseSquare_nonneg (t - r))

@[simp] theorem convolutionTerm_zero_left (t : ℤ) : convolutionTerm t 0 = 0 := by
  simp [convolutionTerm]

@[simp] theorem convolutionTerm_zero_right (t : ℤ) : convolutionTerm t t = 0 := by
  simp [convolutionTerm]

theorem summable_convolutionTerm (t : ℤ) : Summable (convolutionTerm t) := by
  apply Summable.of_nonneg_of_le (convolutionTerm_nonneg t) _
    (summable_inverseSquare.mul_left inverseSquareTotal)
  intro r
  simpa [convolutionTerm, mul_comm] using
    mul_le_mul_of_nonneg_left (inverseSquare_le_total (t - r)) (inverseSquare_nonneg r)

theorem inverseSquare_mul_self (n : ℤ) : inverseSquare n * inverseSquare n = inverseFourth n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold inverseSquare inverseFourth
    field_simp
    <;> ring

theorem convolutionTerm_at_zero (r : ℤ) : convolutionTerm 0 r = inverseFourth r := by
  simpa [convolutionTerm] using inverseSquare_mul_self r

theorem inverseSquareConvolution_zero : inverseSquareConvolution 0 = inverseFourthTotal := by
  unfold inverseSquareConvolution inverseFourthTotal
  exact tsum_congr convolutionTerm_at_zero



/-- The manuscript larger-index split, expressed by equivalent squared inequalities. -/
theorem largerIndex_square (t r : ℤ) :
    (t : ℝ) ^ 2 ≤ 4 * (r : ℝ) ^ 2 ∨
      (t : ℝ) ^ 2 ≤ 4 * ((t - r : ℤ) : ℝ) ^ 2 := by
  have hcast : (t : ℝ) = (r : ℝ) + ((t - r : ℤ) : ℝ) := by
    push_cast
    ring
  by_contra! h
  rw [hcast] at h
  nlinarith [sq_nonneg ((r : ℝ) - ((t - r : ℤ) : ℝ)), h.1, h.2]

theorem convolutionTerm_le_split (t : ℤ) (ht : t ≠ 0) (r : ℤ) :
    convolutionTerm t r ≤
      (4 / (t : ℝ) ^ 2) * (inverseSquare r + inverseSquare (t - r)) := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have ht2 : 0 < (t : ℝ) ^ 2 := sq_pos_of_ne_zero ht'
  have hc : 0 ≤ 4 / (t : ℝ) ^ 2 := by positivity
  by_cases hr : r = 0
  · rw [hr, convolutionTerm_zero_left]
    exact mul_nonneg hc (add_nonneg (inverseSquare_nonneg _) (inverseSquare_nonneg _))
  by_cases hs : t - r = 0
  · have hr' : r = t := by omega
    rw [hr', convolutionTerm_zero_right]
    exact mul_nonneg hc (add_nonneg (inverseSquare_nonneg _) (inverseSquare_nonneg _))
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hs' : ((t - r : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hs
  rcases largerIndex_square t r with hlarge | hlarge
  · have hb : inverseSquare r ≤ 4 / (t : ℝ) ^ 2 := by
      unfold inverseSquare
      apply (div_le_div_iff₀ (sq_pos_of_ne_zero hr') ht2).2
      nlinarith
    calc
      convolutionTerm t r ≤ (4 / (t : ℝ) ^ 2) * inverseSquare (t - r) :=
        mul_le_mul_of_nonneg_right hb (inverseSquare_nonneg (t - r))
      _ ≤ (4 / (t : ℝ) ^ 2) * (inverseSquare r + inverseSquare (t - r)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        linarith [inverseSquare_nonneg r]
  · have hb : inverseSquare (t - r) ≤ 4 / (t : ℝ) ^ 2 := by
      unfold inverseSquare
      apply (div_le_div_iff₀ (sq_pos_of_ne_zero hs') ht2).2
      nlinarith
    calc
      convolutionTerm t r ≤ inverseSquare r * (4 / (t : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (inverseSquare_nonneg r)
      _ ≤ (4 / (t : ℝ) ^ 2) * (inverseSquare r + inverseSquare (t - r)) := by
        rw [mul_comm (inverseSquare r)]
        apply mul_le_mul_of_nonneg_left _ hc
        linarith [inverseSquare_nonneg (t - r)]

/-- r↦t-r is a bijection of every signed integer index set. -/
def complementaryIndex (t : ℤ) : ℤ ≃ ℤ where
  toFun r := t - r
  invFun r := t - r
  left_inv r := by dsimp; omega
  right_inv r := by dsimp; omega

theorem summable_inverseSquare_shift (t : ℤ) :
    Summable (fun r : ℤ => inverseSquare (t - r)) := by
  exact summable_inverseSquare.comp_injective (complementaryIndex t).injective

theorem tsum_inverseSquare_shift (t : ℤ) :
    (∑' r : ℤ, inverseSquare (t - r)) = inverseSquareTotal :=
  (complementaryIndex t).tsum_eq inverseSquare

theorem inverseSquareConvolution_le_nonzero (t : ℤ) (ht : t ≠ 0) :
    inverseSquareConvolution t ≤ 8 * inverseSquareTotal / (t : ℝ) ^ 2 := by
  have hsum : Summable (fun r : ℤ =>
      (4 / (t : ℝ) ^ 2) * (inverseSquare r + inverseSquare (t - r))) :=
    (summable_inverseSquare.add (summable_inverseSquare_shift t)).mul_left _
  calc
    inverseSquareConvolution t ≤ ∑' r : ℤ,
        (4 / (t : ℝ) ^ 2) * (inverseSquare r + inverseSquare (t - r)) :=
      (summable_convolutionTerm t).tsum_le_tsum (convolutionTerm_le_split t ht) hsum
    _ = (4 / (t : ℝ) ^ 2) * (inverseSquareTotal + inverseSquareTotal) := by
      rw [tsum_mul_left,
        summable_inverseSquare.tsum_add (summable_inverseSquare_shift t),
        tsum_inverseSquare_shift]
      rfl
    _ = 8 * inverseSquareTotal / (t : ℝ) ^ 2 := by ring

theorem one_le_square_of_int_ne_zero (t : ℤ) (ht : t ≠ 0) : 1 ≤ (t : ℝ) ^ 2 := by
  have h : t ≤ -1 ∨ 1 ≤ t := by omega
  rcases h with h | h
  · have h' : (t : ℝ) ≤ -1 := by exact_mod_cast h
    nlinarith
  · have h' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast h
    nlinarith

/-- One explicit, fixed finite constant; independent of t, parity, field and cutoff. -/
def uniformConvolutionConstant : ℝ := 16 * inverseSquareTotal + inverseFourthTotal

theorem uniformConvolutionConstant_nonneg : 0 ≤ uniformConvolutionConstant := by
  unfold uniformConvolutionConstant
  have hA := inverseSquareTotal_nonneg
  have hB := inverseFourthTotal_nonneg
  positivity

/-- The precise source numerical convolution bound, including t=0. -/
theorem inverseSquareConvolution_bound (t : ℤ) :
    inverseSquareConvolution t ≤ uniformConvolutionConstant / (1 + (t : ℝ) ^ 2) := by
  by_cases ht : t = 0
  · subst t
    simp only [inverseSquareConvolution_zero, uniformConvolutionConstant, Int.cast_zero,
      zero_pow (by decide : 2 ≠ 0), add_zero, div_one]
    linarith [inverseSquareTotal_nonneg]
  · have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have ht2 : 0 < (t : ℝ) ^ 2 := sq_pos_of_ne_zero ht'
    have hbr : 0 < 1 + (t : ℝ) ^ 2 := by positivity
    have hlarge := one_le_square_of_int_ne_zero t ht
    calc
      inverseSquareConvolution t ≤ 8 * inverseSquareTotal / (t : ℝ) ^ 2 :=
        inverseSquareConvolution_le_nonzero t ht
      _ ≤ 16 * inverseSquareTotal / (1 + (t : ℝ) ^ 2) := by
        apply (div_le_div_iff₀ ht2 hbr).2
        nlinarith [mul_le_mul_of_nonneg_left hlarge inverseSquareTotal_nonneg]
      _ ≤ uniformConvolutionConstant / (1 + (t : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ hbr.le
        unfold uniformConvolutionConstant
        linarith [inverseFourthTotal_nonneg]



/-- The source conditions r+s=t with r and s nonzero, using s=t-r. -/
def nonresonantIndices (t : ℤ) : Set ℤ := {r | r ≠ 0 ∧ t - r ≠ 0}

def nonresonantTerm (t : ℤ) (r : nonresonantIndices t) : ℝ :=
  1 / ((r.val : ℝ) ^ 2 * ((t - r.val : ℤ) : ℝ) ^ 2)

theorem nonresonantTerm_eq (t : ℤ) (r : nonresonantIndices t) :
    nonresonantTerm t r = convolutionTerm t r.val := by
  simp only [nonresonantTerm, convolutionTerm, inverseSquare, div_mul_div_comm, one_mul]

theorem summable_nonresonantTerm (t : ℤ) : Summable (nonresonantTerm t) := by
  exact ((summable_convolutionTerm t).subtype (nonresonantIndices t)).congr
    (fun r => (nonresonantTerm_eq t r).symm)

theorem tsum_nonresonantTerm (t : ℤ) :
    (∑' r : nonresonantIndices t, nonresonantTerm t r) = inverseSquareConvolution t := by
  have hsupport : Function.support (convolutionTerm t) ⊆ nonresonantIndices t := by
    intro r hr
    change convolutionTerm t r ≠ 0 at hr
    constructor
    · intro hr0
      subst r
      exact hr (convolutionTerm_zero_left t)
    · intro hs0
      have hr0 : r = t := by omega
      subst r
      exact hr (convolutionTerm_zero_right t)
  calc
    (∑' r : nonresonantIndices t, nonresonantTerm t r) =
        ∑' r : nonresonantIndices t, convolutionTerm t r.val :=
      tsum_congr (nonresonantTerm_eq t)
    _ = inverseSquareConvolution t :=
      tsum_subtype_eq_of_support_subset hsupport

/-- Exact nonzero-index version of the source estimate; all signed t including zero. -/
theorem nonresonant_convolution_bound (t : ℤ) :
    (∑' r : nonresonantIndices t, nonresonantTerm t r) ≤
      uniformConvolutionConstant / (1 + (t : ℝ) ^ 2) := by
  rw [tsum_nonresonantTerm]
  exact inverseSquareConvolution_bound t


theorem inverseSquareTotal_pos : 0 < inverseSquareTotal := by
  have h := inverseSquare_le_total 1
  norm_num [inverseSquare] at h
  linarith

theorem uniformConvolutionConstant_pos : 0 < uniformConvolutionConstant := by
  unfold uniformConvolutionConstant
  have hA := inverseSquareTotal_pos
  have hB := inverseFourthTotal_nonneg
  linarith

/-- The uniform constant is chosen before quantifying over all signed t. -/
theorem exists_uniform_convolution_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℤ,
      (∑' r : nonresonantIndices t, nonresonantTerm t r) ≤ C / (1 + (t : ℝ) ^ 2) :=
  ⟨uniformConvolutionConstant, uniformConvolutionConstant_pos, nonresonant_convolution_bound⟩




/-- Squared version of the source bracket product inequality. -/
theorem bracket_square_product (n p : ℤ) :
    1 + (n : ℝ) ^ 2 ≤ 2 * (1 + (p : ℝ) ^ 2) * (1 + ((p - n : ℤ) : ℝ) ^ 2) := by
  have hn : (n : ℝ) = (p : ℝ) - ((p - n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hn]
  nlinarith [sq_nonneg ((p : ℝ) + ((p - n : ℤ) : ℝ)),
    mul_nonneg (sq_nonneg (p : ℝ)) (sq_nonneg ((p - n : ℤ) : ℝ))]

/-- The source nonresonant column denominator bound; no assumption on the sign of n or p. -/
theorem column_square_denominator_bound (n p : ℤ) (hp : p ≠ n) :
    (n : ℝ) ^ 2 ≤ 2 * (1 + (p : ℝ) ^ 2) * ((n - p : ℤ) : ℝ) ^ 2 := by
  have hq : n - p ≠ 0 := by omega
  have hq2 := one_le_square_of_int_ne_zero (n - p) hq
  have hn : (n : ℝ) = (p : ℝ) + ((n - p : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hn]
  nlinarith [sq_nonneg ((p : ℝ) - ((n - p : ℤ) : ℝ)),
    mul_nonneg (sq_nonneg (p : ℝ)) (sub_nonneg.mpr hq2)]

theorem column_square_denominator_ratio (n p : ℤ) (hp : p ≠ n) :
    (n : ℝ) ^ 2 / ((n - p : ℤ) : ℝ) ^ 2 ≤ 2 * (1 + (p : ℝ) ^ 2) := by
  have hq : n - p ≠ 0 := by omega
  have hq' : ((n - p : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hq
  exact (div_le_iff₀ (sq_pos_of_ne_zero hq')).2 (column_square_denominator_bound n p hp)



/-- Move the convolution decay to the external index using the source bracket product. -/
theorem shifted_convolution_weight_bound (n p : ℤ) :
    inverseSquareConvolution (p - n) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) * (1 + (p : ℝ) ^ 2) := by
  have hn : 0 < 1 + (n : ℝ) ^ 2 := by positivity
  have hq : 0 < 1 + ((p - n : ℤ) : ℝ) ^ 2 := by positivity
  calc
    inverseSquareConvolution (p - n) ≤
        uniformConvolutionConstant / (1 + ((p - n : ℤ) : ℝ) ^ 2) :=
      inverseSquareConvolution_bound (p - n)
    _ ≤ (2 * uniformConvolutionConstant * (1 + (p : ℝ) ^ 2)) /
        (1 + (n : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ hq hn).2
      convert mul_le_mul_of_nonneg_left (bracket_square_product n p)
        uniformConvolutionConstant_nonneg using 1 <;> ring
    _ = (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        (1 + (p : ℝ) ^ 2) := by ring

/-- Numerical HS-series term comparison; no Fourier or operator realization is assumed. -/
theorem weighted_convolution_term_bound (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p) (n p : ℤ) :
    a p * inverseSquareConvolution (p - n) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        ((1 + (p : ℝ) ^ 2) * a p) := by
  convert mul_le_mul_of_nonneg_left (shifted_convolution_weight_bound n p) (ha p)
    using 1 <;> ring

theorem summable_weighted_convolution (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * a p)) (n : ℤ) :
    Summable (fun p : ℤ => a p * inverseSquareConvolution (p - n)) := by
  apply Summable.of_nonneg_of_le _ (weighted_convolution_term_bound a ha n)
    (hs.mul_left (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)))
  intro p
  exact mul_nonneg (ha p) (tsum_nonneg (convolutionTerm_nonneg (p - n)))

/-- Actual summability precedes the source weighted-series comparison. -/
theorem weighted_convolution_tsum_bound (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * a p)) (n : ℤ) :
    (∑' p : ℤ, a p * inverseSquareConvolution (p - n)) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        (∑' p : ℤ, (1 + (p : ℝ) ^ 2) * a p) := by
  calc
    (∑' p : ℤ, a p * inverseSquareConvolution (p - n)) ≤
        ∑' p : ℤ, (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
          ((1 + (p : ℝ) ^ 2) * a p) :=
      (summable_weighted_convolution a ha hs n).tsum_le_tsum
        (weighted_convolution_term_bound a ha n) (hs.mul_left _)
    _ = _ := tsum_mul_left



/-- The source column kernel estimate, with the resonant term explicitly zero. -/
theorem column_kernel_weight_bound (n : ℤ) (hn : n ≠ 0) (p : ℤ) :
    inverseSquare (n - p) ≤ (2 / (n : ℝ) ^ 2) * (1 + (p : ℝ) ^ 2) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_ne_zero hn'
  by_cases hp : p = n
  · rw [hp, sub_self, inverseSquare_zero]
    positivity
  have hq : n - p ≠ 0 := by omega
  have hq' : ((n - p : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hq
  calc
    inverseSquare (n - p) ≤ (2 * (1 + (p : ℝ) ^ 2)) / (n : ℝ) ^ 2 := by
      unfold inverseSquare
      apply (div_le_div_iff₀ (sq_pos_of_ne_zero hq') hn2).2
      simpa only [one_mul] using column_square_denominator_bound n p hp
    _ = (2 / (n : ℝ) ^ 2) * (1 + (p : ℝ) ^ 2) := by ring

theorem weighted_column_term_bound (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (n : ℤ) (hn : n ≠ 0) (p : ℤ) :
    a p * inverseSquare (n - p) ≤
      (2 / (n : ℝ) ^ 2) * ((1 + (p : ℝ) ^ 2) * a p) := by
  convert mul_le_mul_of_nonneg_left (column_kernel_weight_bound n hn p) (ha p)
    using 1 <;> ring

theorem summable_weighted_column (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * a p))
    (n : ℤ) (hn : n ≠ 0) : Summable (fun p : ℤ => a p * inverseSquare (n - p)) := by
  apply Summable.of_nonneg_of_le _ (weighted_column_term_bound a ha n hn)
    (hs.mul_left (2 / (n : ℝ) ^ 2))
  intro p
  exact mul_nonneg (ha p) (inverseSquare_nonneg (n - p))

theorem weighted_column_tsum_bound (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * a p)) (n : ℤ) (hn : n ≠ 0) :
    (∑' p : ℤ, a p * inverseSquare (n - p)) ≤
      (2 / (n : ℝ) ^ 2) * (∑' p : ℤ, (1 + (p : ℝ) ^ 2) * a p) := by
  calc
    (∑' p : ℤ, a p * inverseSquare (n - p)) ≤
        ∑' p : ℤ, (2 / (n : ℝ) ^ 2) * ((1 + (p : ℝ) ^ 2) * a p) :=
      (summable_weighted_column a ha hs n hn).tsum_le_tsum
        (weighted_column_term_bound a ha n hn) (hs.mul_left _)
    _ = _ := tsum_mul_left

/-- The literal source p≠n sum agrees with the zero-resonant kernel sum. -/
theorem tsum_weighted_column_nonresonant (a : ℤ → ℝ) (n : ℤ) :
    (∑' p : {p : ℤ // p ≠ n}, a p.val * inverseSquare (n - p.val)) =
      ∑' p : ℤ, a p * inverseSquare (n - p) := by
  have hsupport : Function.support (fun p : ℤ => a p * inverseSquare (n - p)) ⊆
      {p : ℤ | p ≠ n} := by
    intro p hp
    change a p * inverseSquare (n - p) ≠ 0 at hp
    intro hpn
    subst p
    simp at hp
  exact tsum_subtype_eq_of_support_subset hsupport

theorem summable_weighted_column_nonresonant (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * a p)) (n : ℤ) (hn : n ≠ 0) :
    Summable (fun p : {p : ℤ // p ≠ n} => a p.val * inverseSquare (n - p.val)) :=
  (summable_weighted_column a ha hs n hn).subtype {p : ℤ | p ≠ n}

theorem weighted_column_nonresonant_bound (a : ℤ → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hs : Summable (fun p : ℤ => (1 + (p : ℝ) ^ 2) * a p)) (n : ℤ) (hn : n ≠ 0) :
    (∑' p : {p : ℤ // p ≠ n}, a p.val * inverseSquare (n - p.val)) ≤
      (2 / (n : ℝ) ^ 2) * (∑' p : ℤ, (1 + (p : ℝ) ^ 2) * a p) := by
  rw [tsum_weighted_column_nonresonant]
  exact weighted_column_tsum_bound a ha hs n hn


end NlsGge.Analysis
