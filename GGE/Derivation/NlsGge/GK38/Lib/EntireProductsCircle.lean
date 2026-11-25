import NlsGge.GK38.Lib.EntireProductsSine

/-!
# L4a, part 4b: the circle estimate `Σ_m |σ̃_m| / (π |n + 1/2 - |m||) → 0` (book Lemma C.5)

For `‖z‖ = (n + 1/2)π` one has `‖mπ - z‖ ≥ π · circDist n m` with `circDist n m = |n + 1/2 - |m||`.  The book
asks to show `S_n = Σ_m |σ̃_m| / (1 + |m - n|) → 0` ("an easy exercise"); here: split into a finite
part (`circDist ≥ n + 1/2 - M`) and a tail (Cauchy–Schwarz via AM-GM with the uniform bound
`Σ_m circDist(n,m)⁻² ≤ 2 Σ_k (k + 1/2)⁻²`).  (The book writes the denominator as `1 + |m - n|`; for
negative `m` the correct distance is `||m| - n|`, which is what is used.)
-/

set_option autoImplicit false

open Filter Topology

namespace NlsGge.GK38.Lib

noncomputable section

/-- `circDist n m = |n + 1/2 - |m||`, the distance of `|m|` from the circle radius `n + 1/2` (in units
of `π`). -/
def circDist (n : ℕ) (m : ℤ) : ℝ := abs ((n : ℝ) + 1 / 2 - |(m : ℝ)|)

theorem abs_cast_eq (m : ℤ) : |(m : ℝ)| = ((m.natAbs : ℕ) : ℝ) := by simp

theorem half_le_circDist (n : ℕ) (m : ℤ) : 1 / 2 ≤ circDist n m := by
  unfold circDist
  rw [abs_cast_eq]
  have h : ((n : ℤ) - (m.natAbs : ℤ) : ℤ) ≥ 0 ∨ ((n : ℤ) - (m.natAbs : ℤ) : ℤ) ≤ -1 := by omega
  have e : (n : ℝ) + 1 / 2 - ((m.natAbs : ℕ) : ℝ)
      = (((n : ℤ) - (m.natAbs : ℤ) : ℤ) : ℝ) + 1 / 2 := by
    simp only [Int.cast_sub, Int.cast_natCast]; ring
  rw [e]
  rcases h with h | h
  · have : (0 : ℝ) ≤ (((n : ℤ) - (m.natAbs : ℤ) : ℤ) : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : ((((n : ℤ) - (m.natAbs : ℤ) : ℤ)) : ℝ) ≤ -1 := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]; linarith

theorem circDist_pos (n : ℕ) (m : ℤ) : 0 < circDist n m := lt_of_lt_of_le (by norm_num) (half_le_circDist n m)

/-- Lower bound for `‖mπ - z‖` on the circle `‖z‖ = (n + 1/2)π`. -/
theorem pi_mul_dd_le {n : ℕ} {z : ℂ} (hz : ‖z‖ = n * Real.pi + Real.pi / 2) (m : ℤ) :
    Real.pi * circDist n m ≤ ‖(m : ℂ) * (Real.pi : ℂ) - z‖ := by
  have h1 := abs_norm_sub_norm_le ((m : ℂ) * (Real.pi : ℂ)) z
  have h2 : ‖(m : ℂ) * (Real.pi : ℂ)‖ = |(m : ℝ)| * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  rw [h2, hz] at h1
  have : abs (|(m : ℝ)| * Real.pi - (n * Real.pi + Real.pi / 2)) = Real.pi * circDist n m := by
    unfold circDist
    rw [show |(m : ℝ)| * Real.pi - (n * Real.pi + Real.pi / 2)
      = -(Real.pi * ((n : ℝ) + 1 / 2 - |(m : ℝ)|)) by ring, abs_neg, abs_mul,
      abs_of_pos Real.pi_pos]
  linarith

/-! ### The uniform bound `Σ_m circDist(n,m)⁻² ≤ 2 K₀` -/

/-- `h k = (k + 1/2)⁻²`. -/
def halfInvSq (k : ℤ) : ℝ := 1 / ((k : ℝ) + 1 / 2) ^ 2

theorem halfInvSq_nonneg (k : ℤ) : 0 ≤ halfInvSq k := by unfold halfInvSq; positivity

theorem summable_halfInvSq : Summable halfInvSq := by
  have hg : Summable fun k : ℤ => 4 * (1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num)).mul_left 4
  refine Summable.of_norm_bounded_eventually hg ?_
  have : ∀ᶠ k : ℤ in Filter.cofinite, k ≠ 0 := by
    simpa using (Set.finite_singleton (0 : ℤ)).compl_mem_cofinite
  filter_upwards [this] with k hk
  rw [Real.norm_of_nonneg (halfInvSq_nonneg k)]
  unfold halfInvSq
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hk2 : 0 < (k : ℝ) ^ 2 := by positivity
  have h4 : (k : ℝ) ^ 2 / 4 ≤ ((k : ℝ) + 1 / 2) ^ 2 := by
    rcases lt_or_gt_of_ne hk with h | h
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      nlinarith
    · have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
  have hpos : 0 < (k : ℝ) ^ 2 / 4 := by positivity
  calc 1 / ((k : ℝ) + 1 / 2) ^ 2 ≤ 1 / ((k : ℝ) ^ 2 / 4) :=
        one_div_le_one_div_of_le hpos h4
    _ = 4 * (1 / (k : ℝ) ^ 2) := by field_simp

/-- `K₀ = Σ_k (k + 1/2)⁻²`. -/
def halfInvSqSum : ℝ := ∑' k : ℤ, halfInvSq k

theorem halfInvSqSum_nonneg : 0 ≤ halfInvSqSum := tsum_nonneg halfInvSq_nonneg

theorem inv_circDist_sq_le (n : ℕ) (m : ℤ) :
    1 / circDist n m ^ 2 ≤ halfInvSq ((n : ℤ) - m) + halfInvSq ((n : ℤ) + m) := by
  have e : circDist n m ^ 2 = ((n : ℝ) + 1 / 2 - |(m : ℝ)|) ^ 2 := by
    unfold circDist; exact sq_abs _
  rw [e]
  rcases le_or_gt 0 m with h | h
  · have : |(m : ℝ)| = (m : ℝ) := abs_of_nonneg (by exact_mod_cast h)
    rw [this]
    have h1 : halfInvSq ((n : ℤ) - m) = 1 / ((n : ℝ) + 1 / 2 - m) ^ 2 := by
      unfold halfInvSq; push_cast; congr 2; ring
    rw [h1]
    linarith [halfInvSq_nonneg ((n : ℤ) + m)]
  · have : |(m : ℝ)| = -(m : ℝ) := abs_of_neg (by exact_mod_cast h)
    rw [this]
    have h1 : halfInvSq ((n : ℤ) + m) = 1 / ((n : ℝ) + 1 / 2 - -(m : ℝ)) ^ 2 := by
      unfold halfInvSq; push_cast; congr 2; ring
    rw [h1]
    linarith [halfInvSq_nonneg ((n : ℤ) - m)]

theorem summable_inv_circDist_sq (n : ℕ) : Summable fun m : ℤ => 1 / circDist n m ^ 2 := by
  have h1 : Summable fun m : ℤ => halfInvSq ((n : ℤ) - m) :=
    (Equiv.summable_iff (f := halfInvSq) (Equiv.subLeft (n : ℤ))).mpr summable_halfInvSq
  have h2 : Summable fun m : ℤ => halfInvSq ((n : ℤ) + m) :=
    (Equiv.summable_iff (f := halfInvSq) (Equiv.addLeft (n : ℤ))).mpr summable_halfInvSq
  exact (h1.add h2).of_nonneg_of_le (fun m => by have := circDist_pos n m; positivity)
    (inv_circDist_sq_le n)

theorem tsum_inv_circDist_sq_le (n : ℕ) : ∑' m : ℤ, 1 / circDist n m ^ 2 ≤ 2 * halfInvSqSum := by
  have h1 : Summable fun m : ℤ => halfInvSq ((n : ℤ) - m) :=
    (Equiv.summable_iff (f := halfInvSq) (Equiv.subLeft (n : ℤ))).mpr summable_halfInvSq
  have h2 : Summable fun m : ℤ => halfInvSq ((n : ℤ) + m) :=
    (Equiv.summable_iff (f := halfInvSq) (Equiv.addLeft (n : ℤ))).mpr summable_halfInvSq
  have e1 : ∑' m : ℤ, halfInvSq ((n : ℤ) - m) = halfInvSqSum := (Equiv.subLeft (n : ℤ)).tsum_eq halfInvSq
  have e2 : ∑' m : ℤ, halfInvSq ((n : ℤ) + m) = halfInvSqSum := (Equiv.addLeft (n : ℤ)).tsum_eq halfInvSq
  calc ∑' m : ℤ, 1 / circDist n m ^ 2 ≤ ∑' m : ℤ, (halfInvSq ((n : ℤ) - m) + halfInvSq ((n : ℤ) + m)) :=
        (summable_inv_circDist_sq n).tsum_le_tsum (inv_circDist_sq_le n) (h1.add h2)
    _ = 2 * halfInvSqSum := by rw [h1.tsum_add h2, e1, e2]; ring

theorem sum_inv_circDist_sq_le (n : ℕ) (s : Finset ℤ) : ∑ m ∈ s, 1 / circDist n m ^ 2 ≤ 2 * halfInvSqSum :=
  ((summable_inv_circDist_sq n).sum_le_tsum s fun m _ => by
    have := circDist_pos n m; positivity).trans (tsum_inv_circDist_sq_le n)

end

end NlsGge.GK38.Lib
