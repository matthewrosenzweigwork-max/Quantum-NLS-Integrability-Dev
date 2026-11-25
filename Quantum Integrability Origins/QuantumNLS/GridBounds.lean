import Mathlib

/-!
# R-E67FE3C4 item 3 (even part): the half-integer lattice sum and the even-`r` grid bound

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:365-420` (`QG:prop:haar-grid-weights`), its proof, even
case: `Σ_n Π_{j=1}^r |n − k_j − 1/2|^{-1} ≤ 2(2^r−1)ζ(r) ≤ (Real.pi²/3) 2^r` for `r ≥ 2`.

The source uses Hölder with `r` equal exponents. Here the same constant is obtained by the weighted AM–GM
inequality `Π_j x_j ≤ (1/r) Σ_j x_j^r` applied pointwise in `n`, followed by the exact reindexing of each
one-dimensional tail. Both routes give the printed constant `(Real.pi²/3) 2^r`.

Proved here (standard axioms only):
* `odd_sq_partial`, `odd_sq_tsum`: `Σ_{m≥0} (2m+1)^{-2} ≤ Real.pi²/6`;
* `halfTail_nat`, `halfTail_int`: `Σ_{m∈ℤ} (|m+1/2|^r)^{-1} ≤ (Real.pi²/3) 2^r` for `r ≥ 2`;
* `shift_tail`: the same bound for every shifted lattice `n − (a + 1/2)`, `a ∈ ℤ`;
* `even_grid_sum`: `Σ_{n∈ℤ} Π_{j : Fin r} |n − k_j − 1/2|^{-1} ≤ (Real.pi²/3) 2^r` for any `k : Fin r → ℤ`, `r ≥ 2`.

NOT here (item 3, odd part): the residue bound `Σ_j Π_{ℓ≠j}|k_j−k_ℓ|^{-1} ≤ 2^{r−1}/(r−1)!`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace QuantumNLS.GridBounds

/-- Partial sums of the odd-square series are bounded by `Real.pi²/6`. -/
theorem odd_sq_partial (N : ℕ) : ∑ m ∈ range N, (1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hsub : (range N).image (fun m : ℕ => 2 * m + 1) ⊆ range (2 * N) := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    rw [mem_range] at hm ⊢
    omega
  have hinj : Set.InjOn (fun m : ℕ => 2 * m + 1) (range N : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    omega
  have hsum : ∑ m ∈ range N, (1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2 =
      ∑ x ∈ (range N).image (fun m : ℕ => 2 * m + 1), (1 : ℝ) / ((x : ℝ)) ^ 2 := by
    rw [sum_image hinj]
    refine sum_congr rfl fun m _ => ?_
    push_cast
    ring_nf
  rw [hsum]
  have h1 : ∑ x ∈ (range N).image (fun m : ℕ => 2 * m + 1), (1 : ℝ) / ((x : ℝ)) ^ 2 ≤
      ∑ x ∈ range (2 * N), (1 : ℝ) / ((x : ℝ)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
  have h2 : ∑ x ∈ range (2 * N), (1 : ℝ) / ((x : ℝ)) ^ 2 ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum _ (fun x _ => by positivity) hasSum_zeta_two
  linarith

/-- `Σ_{m≥0} (2m+1)^{-2} ≤ Real.pi²/6`. -/
theorem odd_sq_tsum : ∑' m : ℕ, (1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2 ≤ Real.pi ^ 2 / 6 :=
  Real.tsum_le_of_sum_range_le (fun m => by positivity) odd_sq_partial

/-- The nonnegative summand `(|m+1/2|^r)^{-1}` on the nonnegative half-integers, for `r ≥ 2`. -/
theorem halfTail_summand_le (r : ℕ) (hr : 2 ≤ r) (m : ℕ) :
    ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹ ≤ 2 ^ r * ((1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2) := by
  have hx : |(m : ℝ) + 1 / 2| = (2 * (m : ℝ) + 1) / 2 := by
    rw [abs_of_pos (by positivity)]
    ring
  rw [hx]
  have hpos : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpow : (2 * (m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ r := pow_le_pow_right₀ hpos hr
  have hA : (0 : ℝ) < 2 * (m : ℝ) + 1 := by linarith
  rw [div_pow, inv_div]
  have hB : ((2 * (m : ℝ) + 1) ^ r) ⁻¹ ≤ ((2 * (m : ℝ) + 1) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) hpow
  calc (2 : ℝ) ^ r / (2 * (m : ℝ) + 1) ^ r = 2 ^ r * ((2 * (m : ℝ) + 1) ^ r)⁻¹ := by
        rw [div_eq_mul_inv]
    _ ≤ 2 ^ r * (1 / (2 * (m : ℝ) + 1) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [one_div]
        exact hB

/-- The half-integer tail over the nonnegative integers, `Σ_{m≥0} (|m+1/2|^r)^{-1} ≤ 2^r Real.pi²/6`. -/
theorem halfTail_nat_le (r : ℕ) (hr : 2 ≤ r) :
    ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹ ≤ 2 ^ r * (Real.pi ^ 2 / 6) := by
  have hsum2 : Summable (fun m : ℕ => (2 : ℝ) ^ r * ((1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2)) := by
    apply Summable.mul_left
    apply summable_of_sum_range_le (fun m => by positivity) (c := Real.pi ^ 2 / 6) odd_sq_partial
  have hle : ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹ ≤
      ∑' m : ℕ, (2 : ℝ) ^ r * ((1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2) :=
    Summable.tsum_le_tsum (fun m => halfTail_summand_le r hr m)
      (Summable.of_nonneg_of_le (fun m => by positivity) (fun m => halfTail_summand_le r hr m) hsum2)
      hsum2
  rw [tsum_mul_left] at hle
  have : (2 : ℝ) ^ r * ∑' m : ℕ, (1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2 ≤ 2 ^ r * (Real.pi ^ 2 / 6) :=
    mul_le_mul_of_nonneg_left odd_sq_tsum (by positivity)
  linarith

theorem odd_sq_summable : Summable (fun m : ℕ => (1 : ℝ) / ((2 * (m : ℝ) + 1)) ^ 2) :=
  summable_of_sum_range_le (fun m => by positivity) odd_sq_partial

/-- The nonnegative half-integer tail is summable, for `r ≥ 2`. -/
theorem halfTail_nat_summable (r : ℕ) (hr : 2 ≤ r) :
    Summable (fun m : ℕ => ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) :=
  Summable.of_nonneg_of_le (fun m => by positivity) (fun m => halfTail_summand_le r hr m)
    (Summable.mul_left ((2 : ℝ) ^ r) odd_sq_summable)

/-- The half-integer tail on `ℤ`: `Σ_{m∈ℤ} (|m+1/2|^r)^{-1} = 2 Σ_{m≥0} (|m+1/2|^r)^{-1}`. -/
theorem halfTail_int_hasSum (r : ℕ) (hr : 2 ≤ r) :
    HasSum (fun m : ℤ => ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹)
      (2 * ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) := by
  have hA : HasSum (fun n : ℕ => ((|((n : ℤ) : ℝ) + 1 / 2|) ^ r)⁻¹)
      (∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) := by
    simp only [Int.cast_natCast]
    exact (halfTail_nat_summable r hr).hasSum
  have hB : HasSum (fun n : ℕ => ((|((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2|) ^ r)⁻¹)
      (∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) := by
    have e : (fun n : ℕ => ((|((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2|) ^ r)⁻¹) =
        (fun n : ℕ => ((|((n : ℤ) : ℝ) + 1 / 2|) ^ r)⁻¹) := by
      funext n
      have h : |((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2| = |((n : ℤ) : ℝ) + 1 / 2| := by
        rw [abs_eq_abs]
        right
        push_cast
        ring
      rw [h]
    rw [e]
    exact hA
  have h := HasSum.of_nat_of_neg_add_one (f := fun m : ℤ => ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) hA hB
  rw [two_mul]
  exact h

/-- Shifted half-integer tail: for `a ∈ ℤ`, `Σ_{n∈ℤ} (|n-(a+1/2)|^r)^{-1}` has the same value as the
unshifted tail. -/
theorem shift_hasSum (r : ℕ) (hr : 2 ≤ r) (a : ℤ) :
    HasSum (fun n : ℤ => ((|(n : ℝ) - ((a : ℝ) + 1 / 2)|) ^ r)⁻¹)
      (2 * ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) := by
  have h := (Equiv.subRight (a + 1)).hasSum_iff.mpr (halfTail_int_hasSum r hr)
  convert h using 1
  funext n
  simp only [Function.comp_apply, Equiv.subRight_apply]
  have e : |(n : ℝ) - ((a : ℝ) + 1 / 2)| = |(((n - (a + 1) : ℤ)) : ℝ) + 1 / 2| := by
    rw [abs_eq_abs]
    left
    push_cast
    ring
  rw [e]

/-- Weighted AM–GM: `Π_j x_j ≤ (1/r) Σ_j x_j^r` for nonnegative `x_j`. -/
theorem amgm_prod {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (hx : ∀ j, 0 ≤ x j) :
    ∏ j, x j ≤ ∑ j, (r : ℝ)⁻¹ * x j ^ r := by
  have hne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hw : ∀ j ∈ (univ : Finset (Fin r)), (0 : ℝ) ≤ (r : ℝ)⁻¹ := fun j _ => by positivity
  have hw' : ∑ _j : Fin r, (r : ℝ)⁻¹ = 1 := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hne
  have hz : ∀ j ∈ (univ : Finset (Fin r)), (0 : ℝ) ≤ x j ^ r := fun j _ => pow_nonneg (hx j) r
  have key := Real.geom_mean_le_arith_mean_weighted (univ : Finset (Fin r)) (fun _ => (r : ℝ)⁻¹)
    (fun j => x j ^ r) hw hw' hz
  have e : ∀ j, (x j ^ r) ^ ((r : ℝ)⁻¹) = x j := fun j => Real.pow_rpow_inv_natCast (hx j) hr.ne'
  simp only [e] at key
  exact key

/-- Even-`r` grid bound: `Σ_{n∈ℤ} Π_j |n-k_j-1/2|^{-1} ≤ (Real.pi²/3) 2^r` for `r ≥ 2` and any
`k : Fin r → ℤ`, together with summability. -/
theorem even_grid_sum {r : ℕ} (hr : 2 ≤ r) (k : Fin r → ℤ) :
    Summable (fun n : ℤ => ∏ j, (|(n : ℝ) - ((k j : ℝ) + 1 / 2)|)⁻¹) ∧
      ∑' n : ℤ, ∏ j, (|(n : ℝ) - ((k j : ℝ) + 1 / 2)|)⁻¹ ≤ (Real.pi ^ 2 / 3) * 2 ^ r := by
  have hne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hG : HasSum (fun n : ℤ => ∑ j : Fin r, ((|(n : ℝ) - ((k j : ℝ) + 1 / 2)|) ^ r)⁻¹)
      (∑ _j : Fin r, 2 * ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) :=
    hasSum_sum (fun j _ => shift_hasSum r hr (k j))
  have hmaj : HasSum (fun n : ℤ => (r : ℝ)⁻¹ * ∑ j : Fin r, ((|(n : ℝ) - ((k j : ℝ) + 1 / 2)|) ^ r)⁻¹)
      ((r : ℝ)⁻¹ * ∑ _j : Fin r, 2 * ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹) :=
    hG.mul_left _
  have hpt : ∀ n : ℤ, ∏ j, (|(n : ℝ) - ((k j : ℝ) + 1 / 2)|)⁻¹ ≤
      (r : ℝ)⁻¹ * ∑ j : Fin r, ((|(n : ℝ) - ((k j : ℝ) + 1 / 2)|) ^ r)⁻¹ := by
    intro n
    have h := amgm_prod (by omega : 0 < r) (fun j => (|(n : ℝ) - ((k j : ℝ) + 1 / 2)|)⁻¹)
      (fun j => inv_nonneg.mpr (abs_nonneg _))
    simp only [inv_pow] at h
    rw [Finset.mul_sum]
    exact h
  have hP : Summable (fun n : ℤ => ∏ j, (|(n : ℝ) - ((k j : ℝ) + 1 / 2)|)⁻¹) :=
    Summable.of_nonneg_of_le
      (fun n => Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (abs_nonneg _))) hpt hmaj.summable
  refine ⟨hP, ?_⟩
  have hval : (r : ℝ)⁻¹ * ∑ _j : Fin r, 2 * ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹ =
      2 * ∑' m : ℕ, ((|(m : ℝ) + 1 / 2|) ^ r)⁻¹ := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact inv_mul_cancel_left₀ hne _
  have hle := hasSum_le hpt hP.hasSum hmaj
  rw [hval] at hle
  have hS := halfTail_nat_le r hr
  linarith

/-- For a strictly monotone `f : Fin r → ℤ`, index gaps dominate value gaps:
`m ≤ f j - f i` whenever `j = i + m`. -/
theorem strictMono_gap {r : ℕ} (f : Fin r → ℤ) (hf : StrictMono f) :
    ∀ m : ℕ, ∀ i j : Fin r, (j : ℕ) = (i : ℕ) + m → (m : ℤ) ≤ f j - f i := by
  intro m
  induction m with
  | zero =>
    intro i j hij
    have hji : j = i := Fin.ext (by omega)
    subst hji
    simp
  | succ m ih =>
    intro i j hij
    have hlt : (i : ℕ) + m < r := by
      have := j.isLt
      omega
    have h1 : (m : ℤ) ≤ f ⟨(i : ℕ) + m, hlt⟩ - f i := ih i ⟨(i : ℕ) + m, hlt⟩ rfl
    have hlt' : (⟨(i : ℕ) + m, hlt⟩ : Fin r) < j := by
      show (i : ℕ) + m < (j : ℕ)
      omega
    have h2 : f ⟨(i : ℕ) + m, hlt⟩ < f j := hf hlt'
    have h2' : f ⟨(i : ℕ) + m, hlt⟩ + 1 ≤ f j := Int.add_one_le_of_lt h2
    push_cast
    linarith

/-- Gap bound for `i < j` in `Fin r`, in `ℤ`. -/
theorem gap_lt {r : ℕ} (k : Fin r → ℤ) (hk : StrictMono k) (i j : Fin r) (h : i < j) :
    |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ |k i - k j| := by
  have hij : (i : ℕ) < (j : ℕ) := h
  have hm := strictMono_gap k hk ((j : ℕ) - (i : ℕ)) i j (by omega)
  have hlt : k i < k j := hk h
  have e1 : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| = ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by omega)
  have e2 : |k i - k j| = k j - k i := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by omega)
  have e3 : (((j : ℕ) - (i : ℕ) : ℕ) : ℤ) = ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by omega
  rw [e1, e2, ← e3]
  exact hm

/-- Real-valued gap bound: `|i - j| ≤ |k_i - k_j|` for `i ≠ j`. -/
theorem gap_real {r : ℕ} (k : Fin r → ℤ) (hk : StrictMono k) (i j : Fin r) (hij : i ≠ j) :
    |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ |((k i : ℤ) : ℝ) - ((k j : ℤ) : ℝ)| := by
  have hZ : |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| ≤ |k i - k j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact gap_lt k hk i j h
    · rw [abs_sub_comm (((i : ℕ) : ℤ)), abs_sub_comm (k i)]
      exact gap_lt k hk j i h
  have h2 : ((|((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| : ℤ) : ℝ) ≤ ((|k i - k j| : ℤ) : ℝ) :=
    Int.cast_le.mpr hZ
  push_cast at h2
  exact h2

/-- `|j-k|^{-1} = ((j-1-k)+1)^{-1}` for `k < j` (reflected factor). -/
theorem abs_inv_eq_reflect (j k : ℕ) (hk : k < j) :
    |(j : ℝ) - (k : ℝ)|⁻¹ = (((j - 1 - k) + 1 : ℕ) : ℝ)⁻¹ := by
  have hcast : (j - 1 - k) + 1 = j - k := by omega
  have hkR : (k : ℝ) < (j : ℝ) := by exact_mod_cast hk
  have hpos : (0 : ℝ) < (j : ℝ) - (k : ℝ) := by linarith
  rw [hcast, Nat.cast_sub hk.le, abs_of_pos hpos]

/-- `∏_{t<m} (t+1)^{-1} = (m!)^{-1}` in `ℝ`. -/
theorem prod_inv_succ_range (m : ℕ) :
    ∏ t ∈ range m, (((t + 1 : ℕ)) : ℝ)⁻¹ = ((m.factorial : ℕ) : ℝ)⁻¹ := by
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

/-- Left half of the residue product: `∏_{k<j} |j-k|^{-1} = (j!)^{-1}`. -/
theorem prod_left_range (j : ℕ) :
    ∏ k ∈ range j, (if k = j then (1 : ℝ) else |(j : ℝ) - (k : ℝ)|⁻¹) = ((j.factorial : ℕ) : ℝ)⁻¹ := by
  have E1 : ∏ k ∈ range j, (if k = j then (1 : ℝ) else |(j : ℝ) - (k : ℝ)|⁻¹) =
      ∏ k ∈ range j, (|(j : ℝ) - (k : ℝ)|⁻¹) :=
    Finset.prod_congr rfl (fun k hk => if_neg (show ¬ k = j from (Finset.mem_range.mp hk).ne))
  have E2 : ∏ k ∈ range j, (|(j : ℝ) - (k : ℝ)|⁻¹) =
      ∏ k ∈ range j, ((((j - 1 - k) + 1 : ℕ)) : ℝ)⁻¹ :=
    Finset.prod_congr rfl (fun k hk => abs_inv_eq_reflect j k (Finset.mem_range.mp hk))
  have R : ∏ k ∈ range j, ((((j - 1 - k) + 1 : ℕ)) : ℝ)⁻¹ =
      ∏ k ∈ range j, (((k + 1 : ℕ)) : ℝ)⁻¹ :=
    Finset.prod_range_reflect (fun k : ℕ => (((k + 1 : ℕ)) : ℝ)⁻¹) j
  rw [E1, E2, R]
  exact prod_inv_succ_range j

/-- Residue product over `ℕ`: `∏_{m<r, m≠j} |j-m|^{-1} = 1/(j! (r-1-j)!)` for `j < r`. -/
theorem prod_residue_range (r j : ℕ) (hj : j < r) :
    ∏ m ∈ range r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹) =
      (((j.factorial : ℕ) : ℝ) * (((r - 1 - j).factorial : ℕ) : ℝ))⁻¹ := by
  have hB : ∏ k ∈ Ico (j + 1) r, (if k = j then (1 : ℝ) else |(j : ℝ) - (k : ℝ)|⁻¹) =
      (((r - 1 - j).factorial : ℕ) : ℝ)⁻¹ := by
    have E1 : ∏ k ∈ Ico (j + 1) r, (if k = j then (1 : ℝ) else |(j : ℝ) - (k : ℝ)|⁻¹) =
        ∏ k ∈ Ico (j + 1) r, (|(j : ℝ) - (k : ℝ)|⁻¹) :=
      Finset.prod_congr rfl (fun k hk => by
        have hkj : ¬ k = j := by
          have := (Finset.mem_Ico.mp hk).1
          omega
        exact if_neg hkj)
    have E2 : ∏ k ∈ Ico (j + 1) r, (|(j : ℝ) - (k : ℝ)|⁻¹) =
        ∏ t ∈ range (r - (j + 1)), (|(j : ℝ) - ((j + 1 + t : ℕ) : ℝ)|⁻¹) :=
      Finset.prod_Ico_eq_prod_range (fun k : ℕ => |(j : ℝ) - (k : ℝ)|⁻¹) (j + 1) r
    have hr' : r - (j + 1) = r - 1 - j := by omega
    have hterm : ∀ t : ℕ, |(j : ℝ) - ((j + 1 + t : ℕ) : ℝ)|⁻¹ = (((t + 1 : ℕ)) : ℝ)⁻¹ := by
      intro t
      have e : (j : ℝ) - ((j + 1 + t : ℕ) : ℝ) = -(((t + 1 : ℕ)) : ℝ) := by
        push_cast
        ring
      rw [e, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    have E3 : ∏ t ∈ range (r - (j + 1)), (|(j : ℝ) - ((j + 1 + t : ℕ) : ℝ)|⁻¹) =
        ∏ t ∈ range (r - (j + 1)), (((t + 1 : ℕ)) : ℝ)⁻¹ :=
      Finset.prod_congr rfl (fun t _ => hterm t)
    rw [E1, E2, E3, hr']
    exact prod_inv_succ_range _
  have hsplit : (∏ m ∈ range j, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹)) *
      (∏ m ∈ Ico j r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹)) =
      ∏ m ∈ range r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹) :=
    Finset.prod_range_mul_prod_Ico _ hj.le
  have hsplit2 : ∏ m ∈ Ico j r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹) =
      (if j = j then (1 : ℝ) else |(j : ℝ) - (j : ℝ)|⁻¹) *
        ∏ m ∈ Ico (j + 1) r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹) :=
    Finset.prod_eq_prod_Ico_succ_bot hj _
  rw [← hsplit, hsplit2, if_pos (rfl : j = j), one_mul, prod_left_range j, hB, mul_inv]

/-- Odd-`r` residue bound: for strictly increasing `k : Fin r → ℤ` and `r ≥ 1`,
`Σ_j Π_{ℓ≠j} |k_j - k_ℓ|^{-1} ≤ 2^{r-1}/(r-1)!`. -/
theorem residue_sum_le {r : ℕ} (hr : 1 ≤ r) (k : Fin r → ℤ) (hk : StrictMono k) :
    ∑ j : Fin r, ∏ ℓ ∈ Finset.univ.erase j, (|((k j : ℤ) : ℝ) - ((k ℓ : ℤ) : ℝ)|)⁻¹ ≤
      (2 : ℝ) ^ (r - 1) / (((r - 1).factorial : ℕ) : ℝ) := by
  have hle : ∀ j : Fin r, ∏ ℓ ∈ Finset.univ.erase j, (|((k j : ℤ) : ℝ) - ((k ℓ : ℤ) : ℝ)|)⁻¹ ≤
      ∏ ℓ ∈ Finset.univ.erase j, (|((j : ℕ) : ℝ) - ((ℓ : ℕ) : ℝ)|)⁻¹ := by
    intro j
    apply Finset.prod_le_prod₀
    · intro ℓ _
      exact inv_nonneg.mpr (abs_nonneg _)
    · intro ℓ hℓ
      have hne : j ≠ ℓ := (Finset.ne_of_mem_erase hℓ).symm
      have hgap := gap_real k hk j ℓ hne
      have hpos : 0 < |((j : ℕ) : ℝ) - ((ℓ : ℕ) : ℝ)| := by
        apply abs_pos.mpr
        intro h0
        apply hne
        apply Fin.ext
        have h1 : ((j : ℕ) : ℝ) = ((ℓ : ℕ) : ℝ) := sub_eq_zero.mp h0
        exact_mod_cast h1
      exact inv_anti₀ hpos hgap
  have hconv : ∀ j : Fin r, ∏ ℓ ∈ Finset.univ.erase j, (|((j : ℕ) : ℝ) - ((ℓ : ℕ) : ℝ)|)⁻¹ =
      ∏ ℓ : Fin r, (if (ℓ : ℕ) = (j : ℕ) then (1 : ℝ) else |((j : ℕ) : ℝ) - ((ℓ : ℕ) : ℝ)|⁻¹) := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [eq_self_iff_true, if_true, one_mul]
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    have hne : (ℓ : ℕ) ≠ (j : ℕ) := fun h => (Finset.ne_of_mem_erase hℓ) (Fin.ext h)
    simp only [if_neg hne]
  have hF : ∀ j : Fin r, ∏ ℓ ∈ Finset.univ.erase j, (|((k j : ℤ) : ℝ) - ((k ℓ : ℤ) : ℝ)|)⁻¹ ≤
      ∏ m ∈ range r, (if m = (j : ℕ) then (1 : ℝ) else |((j : ℕ) : ℝ) - (m : ℝ)|⁻¹) := by
    intro j
    exact (hle j).trans (le_of_eq ((hconv j).trans
      (Fin.prod_univ_eq_prod_range
        (fun m : ℕ => if m = (j : ℕ) then (1 : ℝ) else |((j : ℕ) : ℝ) - (m : ℝ)|⁻¹) r)))
  have hsumF : ∑ j : Fin r, ∏ ℓ ∈ Finset.univ.erase j, (|((k j : ℤ) : ℝ) - ((k ℓ : ℤ) : ℝ)|)⁻¹ ≤
      ∑ j ∈ range r, ∏ m ∈ range r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹) :=
    (Finset.sum_le_sum (fun j _ => hF j)).trans
      (le_of_eq (Fin.sum_univ_eq_sum_range
        (fun j : ℕ => ∏ m ∈ range r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹)) r))
  have hterm : ∀ j ∈ range r, ∏ m ∈ range r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹) =
      (((r - 1).choose j : ℕ) : ℝ) * (((r - 1).factorial : ℕ) : ℝ)⁻¹ := by
    intro j hj
    have hjr : j < r := Finset.mem_range.mp hj
    rw [prod_residue_range r j hjr]
    have hC : (((r - 1).choose j : ℕ) : ℝ) * ((j.factorial : ℕ) : ℝ) *
        (((r - 1 - j).factorial : ℕ) : ℝ) = (((r - 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (show j ≤ r - 1 by omega)
    have hC0 : (((r - 1).choose j : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (show j ≤ r - 1 by omega)).ne'
    have hj0 : ((j.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hm0 : (((r - 1 - j).factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← hC]
    field_simp
  have hsumC : ∑ j ∈ range r, (((r - 1).choose j : ℕ) : ℝ) = (2 : ℝ) ^ (r - 1) := by
    have h := Nat.sum_range_choose (r - 1)
    have hr' : r - 1 + 1 = r := by omega
    rw [hr'] at h
    exact_mod_cast h
  have hsum_eq : ∑ j ∈ range r, ∏ m ∈ range r, (if m = j then (1 : ℝ) else |(j : ℝ) - (m : ℝ)|⁻¹) =
      (2 : ℝ) ^ (r - 1) / (((r - 1).factorial : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hsumC, div_eq_mul_inv]
  exact hsumF.trans (le_of_eq hsum_eq)

end QuantumNLS.GridBounds

#print axioms QuantumNLS.GridBounds.even_grid_sum
#print axioms QuantumNLS.GridBounds.residue_sum_le

#print axioms QuantumNLS.GridBounds.odd_sq_tsum
#print axioms QuantumNLS.GridBounds.halfTail_nat_le
