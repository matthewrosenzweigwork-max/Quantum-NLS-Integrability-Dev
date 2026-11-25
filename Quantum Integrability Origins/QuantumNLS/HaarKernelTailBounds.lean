import QuantumNLS.GridStrongSum

/-!
# R-3B18A493 QG:prop:haar-kernel-tail, Part 1: explicit tail bounds

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:433-446` (`QG:prop:haar-kernel-tail`).

Proved here (on top of the frozen GridEigen, GridBounds, HilbertDiagOp and GridStrongSum modules):
* `strong_coeff`: for any strong limit `T` of the symmetric partial sums, `⟪B_k, T v⟫ = μ_k(t) ⟪B_k, v⟫`;
* `odd_tail_vanish` (odd `r`, i.e. `n` even): if `|k_j| ≤ R` for all `j` and `t_m = 0` for `|m| ≤ R`, then
  `T_r(t) B_k = 0`;
* `even_tail_eigen_bound` (even `r`, i.e. `n` odd): if `|k_j + 1/2| ≤ M` for all `j` and `R > 2M+1`, then the
  eigenvalue `μ_k(t)` of `T_r(t)` on `B_k` satisfies
  `|μ_k(t)| ≤ 2^{r+2}/(r! ω^r (r−1)) (R−1)^{1−r}` for every `t` with `‖t‖_∞ ≤ 1` and `t_m = 0` for `|m| ≤ R`.

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology Finset
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym
open QuantumNLS.GridEigen QuantumNLS.GridBounds QuantumNLS.HilbertDiagOp QuantumNLS.GridStrongSum
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer

namespace QuantumNLS.HaarKernelTailBounds

variable (L : ℝ) [Fact (0 < L)]

/-- Coefficients of a strong limit of the symmetric partial sums are the diagonal entries `μ_k(t)`. -/
theorem strong_coeff (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (T : Hn L n →L[ℂ] Hn L n)
    (hT : ∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v)))
    (k : Idx (n + 1)) (v : Hn L n) :
    ⟪physBasis L n k, T v⟫_ℂ = muGrid L n t k * ⟪physBasis L n k, v⟫_ℂ := by
  have h1 : Tendsto (fun N => ⟪physBasis L n k, partialSum L n t N v⟫_ℂ) atTop
      (𝓝 ⟪physBasis L n k, T v⟫_ℂ) :=
    Tendsto.inner tendsto_const_nhds (hT v)
  have h2 : Tendsto (fun N => ⟪physBasis L n k, partialSum L n t N v⟫_ℂ) atTop
      (𝓝 (muGrid L n t k * ⟪physBasis L n k, v⟫_ℂ)) := by
    have hc := (tendsto_Icc_sum _ (summable_mul_grid L n t ht k)).mul_const ⟪physBasis L n k, v⟫_ℂ
    refine hc.congr (fun N => ?_)
    exact (inner_partialSum L n t N k v).symm
  exact tendsto_nhds_unique h1 h2

/-- **Odd `r` (`n` even): vanishing on a basis vector.** -/
theorem odd_tail_vanish (n : ℕ) (hn : Even n) (R : ℕ) (k : Idx (n + 1))
    (hk : ∀ j : Fin (n + 1), |k.1 j| ≤ (R : ℤ))
    (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (ht0 : ∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0)
    (T : Hn L n →L[ℂ] Hn L n)
    (hT : ∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) :
    T (physBasis L n k) = 0 := by
  have hterm : ∀ m : ℤ, t m * lamTilde L n k (gridPt L m) = 0 := by
    intro m
    by_cases hm : |m| ≤ (R : ℤ)
    · rw [ht0 m hm, zero_mul]
    · rw [lamTilde_grid_odd_zero L hn k m, mul_zero]
      intro i hi
      apply hm
      rw [← hi]
      exact hk i
  have hμ : muGrid L n t k = 0 := by
    unfold muGrid
    simp only [hterm, tsum_zero]
  have hcoef : ∀ j, ⟪physBasis L n j, T (physBasis L n k)⟫_ℂ = 0 := by
    intro j
    rw [strong_coeff L n t ht T hT j (physBasis L n k)]
    by_cases hjk : j = k
    · rw [hjk, hμ, zero_mul]
    · rw [(physBasis L n).orthonormal.inner_eq_zero hjk, mul_zero]
  have hsum := parseval_hasSum (physBasis L n) (T (physBasis L n k))
  have hz : (fun j => ‖⟪physBasis L n j, T (physBasis L n k)⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
    funext j
    rw [hcoef j]
    simp
  rw [hz] at hsum
  have h0 : ‖T (physBasis L n k)‖ ^ 2 = 0 := hsum.unique hasSum_zero
  have h1 : ‖T (physBasis L n k)‖ = 0 := (pow_eq_zero_iff two_ne_zero).mp h0
  exact norm_eq_zero.mp h1

/-! ### Real-variable tail estimates -/

/-- Weighted one-sided tail `1/j^{n+1}` for `j > R` (nat index). -/
def Fn (n R j : ℕ) : ℝ := if R < j then 1 / ((j : ℝ)) ^ (n + 1) else 0

theorem Fn_nonneg (n R j : ℕ) : 0 ≤ Fn n R j := by
  unfold Fn
  split_ifs <;> positivity

/-- The telescoping step: `1/(x+1)^{s+1} ≤ (1/s)(1/x^s − 1/(x+1)^s)` for `x ≥ 1`, `s ≥ 1`. -/
theorem step_ineq (x : ℝ) (hx : 1 ≤ x) (s : ℕ) (hs : 1 ≤ s) :
    1 / (x + 1) ^ (s + 1) ≤ (1 / (s : ℝ)) * (1 / x ^ s - 1 / (x + 1) ^ s) := by
  have hx0 : 0 < x := by linarith
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have ha : 0 < 1 / x := by positivity
  have hB : 1 + (s : ℝ) * (1 / x) ≤ (1 + 1 / x) ^ s := one_add_mul_le_pow (by linarith) s
  have hinv : (1 / x) * x = 1 := by field_simp
  have hxs : (x + 1) ^ s = x ^ s * (1 + 1 / x) ^ s := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hPpos : 0 < (1 + 1 / x) ^ s := by positivity
  have hxsp : 0 < x ^ s := by positivity
  have key : (s : ℝ) ≤ ((1 + 1 / x) ^ s - 1) * (x + 1) := by
    have h1 : (s : ℝ) * (1 / x) ≤ (1 + 1 / x) ^ s - 1 := by linarith
    have h2 : (s : ℝ) * (1 / x) * (x + 1) = s + s * (1 / x) := by
      linear_combination (s : ℝ) * hinv
    have h3 : (s : ℝ) * (1 / x) * (x + 1) ≤ ((1 + 1 / x) ^ s - 1) * (x + 1) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h4 : (0 : ℝ) ≤ (s : ℝ) * (1 / x) := by positivity
    linarith
  rw [pow_succ, hxs]
  set P := (1 + 1 / x) ^ s with hP
  have hrhs : (1 / (s : ℝ)) * (1 / x ^ s - 1 / (x ^ s * P)) = (P - 1) / ((s : ℝ) * x ^ s * P) := by
    field_simp
  rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg hxsp.le hPpos.le) (sub_nonneg.2 key)]

/-- Partial sums of `Fn` over `range (N+R+1)` telescope. -/
theorem Fn_partial (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (N : ℕ) :
    ∑ j ∈ range (N + R + 1), Fn n R j ≤
      (1 / (n : ℝ)) * (1 / (R : ℝ) ^ n - 1 / ((N : ℝ) + R) ^ n) := by
  induction N with
  | zero =>
    have h0 : ∑ j ∈ range (0 + R + 1), Fn n R j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjR : j ≤ R := by
        have := Finset.mem_range.mp hj
        omega
      unfold Fn
      rw [if_neg (by omega)]
    rw [h0]
    simp
  | succ N ih =>
    have e : N + 1 + R + 1 = (N + R + 1) + 1 := by ring
    rw [e, Finset.sum_range_succ]
    have hxR : (1 : ℝ) ≤ (N : ℝ) + R := by
      have : (1 : ℝ) ≤ R := by exact_mod_cast hR
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith
    have hstep := step_ineq ((N : ℝ) + R) hxR n hn
    have hterm : Fn n R (N + R + 1) = 1 / (((N : ℝ) + R) + 1) ^ (n + 1) := by
      unfold Fn
      rw [if_pos (by omega)]
      push_cast
      ring
    rw [hterm]
    push_cast
    have e2 : (N : ℝ) + 1 + R = (N : ℝ) + R + 1 := by ring
    rw [e2]
    linarith [ih, hstep]

/-- Partial-sum bound for `Fn`. -/
theorem Fn_part_le (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (N : ℕ) :
    ∑ j ∈ range N, Fn n R j ≤ (1 / (n : ℝ)) * (1 / (R : ℝ) ^ n) := by
  have hX : (0 : ℝ) ≤ 1 / ((N : ℝ) + R) ^ n := by positivity
  have hle : ∑ j ∈ range N, Fn n R j ≤ ∑ j ∈ range (N + R + 1), Fn n R j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => Fn_nonneg n R j)
  have hc : (1 / (n : ℝ)) * (1 / (R : ℝ) ^ n - 1 / ((N : ℝ) + R) ^ n) ≤
      (1 / (n : ℝ)) * (1 / (R : ℝ) ^ n) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  exact hle.trans ((Fn_partial n R hn hR N).trans hc)

theorem Fn_summable (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) : Summable (fun j => Fn n R j) :=
  summable_of_sum_range_le (fun j => Fn_nonneg n R j) (fun N => Fn_part_le n R hn hR N)

/-- Shifted partial sums: `Σ_{j<N} Fn(j+1) ≤ Σ_{j<N+1} Fn j`, since `Fn 0 = 0`. -/
theorem Fn_shift_part_le (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (N : ℕ) :
    ∑ j ∈ range N, Fn n R (j + 1) ≤ (1 / (n : ℝ)) * (1 / (R : ℝ) ^ n) := by
  have h0 : Fn n R 0 = 0 := by
    unfold Fn
    rw [if_neg (Nat.not_lt_zero _)]
  have hs := Finset.sum_range_succ' (Fn n R) N
  rw [h0, add_zero] at hs
  rw [← hs]
  exact Fn_part_le n R hn hR (N + 1)

theorem Fn_shift_summable (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) :
    Summable (fun j => Fn n R (j + 1)) :=
  summable_of_sum_range_le (fun j => Fn_nonneg n R (j + 1)) (fun N => Fn_shift_part_le n R hn hR N)

/-- Two-sided tail weight on `ℤ`: `1/|m|^{n+1}` for `|m| > R`, zero otherwise. -/
def tailW (n R : ℕ) (m : ℤ) : ℝ := if (R : ℤ) < |m| then 1 / (|(m : ℝ)|) ^ (n + 1) else 0

theorem tailW_nat (n R j : ℕ) : tailW n R (j : ℤ) = Fn n R j := by
  unfold tailW Fn
  simp only [Int.cast_natCast, Nat.abs_cast, Nat.cast_lt]

theorem tailW_neg (n R j : ℕ) : tailW n R (-((j : ℤ) + 1)) = Fn n R (j + 1) := by
  unfold tailW Fn
  have e : (-((j : ℤ) + 1)) = -(((j + 1 : ℕ)) : ℤ) := by push_cast; ring
  rw [e, abs_neg]
  simp only [Nat.abs_cast, Nat.cast_lt, Int.cast_neg, Int.cast_natCast]
  rw [abs_neg, Nat.abs_cast]

theorem tailW_summable (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) : Summable (tailW n R) := by
  have hA : Summable (fun j : ℕ => tailW n R (j : ℤ)) := by
    simp only [tailW_nat]
    exact Fn_summable n R hn hR
  have hB : Summable (fun j : ℕ => tailW n R (-((j : ℤ) + 1))) := by
    simp only [tailW_neg]
    exact Fn_shift_summable n R hn hR
  exact Summable.of_nat_of_neg_add_one hA hB

theorem tailW_tsum_le (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) :
    ∑' m : ℤ, tailW n R m ≤ 2 * ((1 / (n : ℝ)) * (1 / (R : ℝ) ^ n)) := by
  have hA : Summable (fun j : ℕ => tailW n R (j : ℤ)) := by
    simp only [tailW_nat]
    exact Fn_summable n R hn hR
  have hB : Summable (fun j : ℕ => tailW n R (-((j : ℤ) + 1))) := by
    simp only [tailW_neg]
    exact Fn_shift_summable n R hn hR
  have hH := HasSum.of_nat_of_neg_add_one hA.hasSum hB.hasSum
  rw [hH.tsum_eq]
  simp only [tailW_nat, tailW_neg]
  have h1 := Real.tsum_le_of_sum_range_le (fun j => Fn_nonneg n R j) (Fn_part_le n R hn hR)
  have h2 := Real.tsum_le_of_sum_range_le (fun j => Fn_nonneg n R (j + 1))
    (Fn_shift_part_le n R hn hR)
  linarith

/-- Pointwise comparison of the lattice eigenvalue modulus with the tail weight. -/
theorem lam_le_tailW (n : ℕ) (hn : Odd n) (k : Idx (n + 1)) (M : ℝ)
    (hM : ∀ j : Fin (n + 1), |(k.1 j : ℝ) + 1 / 2| ≤ M) (R : ℕ) (hR : 2 * M + 1 < (R : ℝ))
    (m : ℤ) :
    (if (R : ℤ) < |m| then ‖lamTilde L n k (gridPt L m)‖ else 0) ≤
      2 ^ (n + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1)) * tailW n R m := by
  have hL : (0 : ℝ) < L := Fact.out
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ⟨0, by omega⟩)
  unfold tailW
  by_cases h : (R : ℤ) < |m|
  · rw [if_pos h, if_pos h]
    have hR' : (R : ℝ) < |(m : ℝ)| := by
      have h' : ((R : ℤ) : ℝ) < ((|m| : ℤ) : ℝ) := by exact_mod_cast h
      rw [Int.cast_abs] at h'
      exact_mod_cast h'
    have hM2 : 2 * M < |(m : ℝ)| := by linarith
    have hmpos : 0 < |(m : ℝ)| / 2 := by linarith
    have hfac : ∀ j : Fin (n + 1), |(m : ℝ) - ((k.1 j : ℝ) + 1 / 2)|⁻¹ ≤ 2 / |(m : ℝ)| := by
      intro j
      have hA := hM j
      have h1 : |(m : ℝ)| - |(k.1 j : ℝ) + 1 / 2| ≤ |(m : ℝ) - ((k.1 j : ℝ) + 1 / 2)| :=
        abs_sub_abs_le_abs_sub _ _
      have h2 : |(m : ℝ)| / 2 ≤ |(m : ℝ) - ((k.1 j : ℝ) + 1 / 2)| := by linarith
      have h3 := inv_anti₀ hmpos h2
      rw [inv_div] at h3
      exact h3
    have hprod : ∏ j, |(m : ℝ) - ((k.1 j : ℝ) + 1 / 2)|⁻¹ ≤ (2 / |(m : ℝ)|) ^ (n + 1) := by
      calc ∏ j, |(m : ℝ) - ((k.1 j : ℝ) + 1 / 2)|⁻¹
          ≤ ∏ _j : Fin (n + 1), (2 / |(m : ℝ)|) :=
            Finset.prod_le_prod₀ (fun j _ => inv_nonneg.mpr (abs_nonneg _))
              (fun j _ => hfac j)
        _ = (2 / |(m : ℝ)|) ^ (n + 1) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [lam_norm_even L hn k m]
    have hcoef : (0 : ℝ) ≤ 2 / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1)) := by
      apply div_nonneg (by norm_num)
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by positivity) hL.le) _)
    calc 2 / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1)) *
          ∏ j, |(m : ℝ) - ((k.1 j : ℝ) + 1 / 2)|⁻¹
        ≤ 2 / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1)) *
            (2 / |(m : ℝ)|) ^ (n + 1) := mul_le_mul_of_nonneg_left hprod hcoef
      _ = 2 ^ (n + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1)) *
            (1 / (|(m : ℝ)|) ^ (n + 1)) := by
          rw [div_pow]
          ring
  · simp [h]

/-- **Even `r` (`n` odd): the eigenvalue tail bound.** For `|k_j+1/2| ≤ M` and `R > 2M+1`, the eigenvalue
`μ_k(t)` of `T_r(t)` on `B_k`, for `‖t‖_∞ ≤ 1` and `t_m = 0` for `|m| ≤ R`, satisfies
`|μ_k(t)| ≤ 2^{r+2}/(r! ω^r (r−1)) (R−1)^{1−r}` with `r = n+1`, `ω = 2π/L`. -/
theorem even_tail_eigen_bound (n : ℕ) (hn : Odd n) (k : Idx (n + 1)) (M : ℝ)
    (hM : ∀ j : Fin (n + 1), |(k.1 j : ℝ) + 1 / 2| ≤ M) (R : ℕ) (hR : 2 * M + 1 < (R : ℝ))
    (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (ht0 : ∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) :
    ‖muGrid L n t k‖ ≤
      2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) * (n : ℝ)) *
        ((R : ℝ) - 1) ^ (1 - ((n + 1 : ℕ) : ℤ)) := by
  have hL : (0 : ℝ) < L := Fact.out
  have hn1 : 1 ≤ n := by
    obtain ⟨j, hj⟩ := hn
    omega
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ⟨0, by omega⟩)
  have hR1 : (1 : ℝ) < R := by linarith
  have hRnat : 2 ≤ R := by
    have : 1 < R := by exact_mod_cast hR1
    omega
  have hR2 : (2 : ℝ) ≤ R := by exact_mod_cast hRnat
  have hRpos : (0 : ℝ) < (R : ℝ) - 1 := by linarith
  have hR1' : 1 ≤ R := by omega
  set c : ℝ := 2 ^ (n + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact div_nonneg (by positivity)
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by positivity) hL.le) _))
  have hsum1 : Summable (fun m : ℤ =>
      if (R : ℤ) < |m| then ‖lamTilde L n k (gridPt L m)‖ else 0) :=
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
      (fun m => by split_ifs <;> simp [norm_nonneg])
      (grid_bound L n k).1
  have hbound1 : ‖muGrid L n t k‖ ≤
      ∑' m : ℤ, (if (R : ℤ) < |m| then ‖lamTilde L n k (gridPt L m)‖ else 0) := by
    unfold muGrid
    refine (norm_tsum_le_tsum_norm (summable_norm_mul_grid L n t ht k)).trans ?_
    refine Summable.tsum_le_tsum (fun m => ?_) (summable_norm_mul_grid L n t ht k) hsum1
    by_cases h : (R : ℤ) < |m|
    · rw [if_pos h]
      exact norm_mul_grid_le L n t ht k m
    · rw [if_neg h, ht0 m (not_lt.mp h), zero_mul, norm_zero]
  have hbound2 : ∑' m : ℤ, (if (R : ℤ) < |m| then ‖lamTilde L n k (gridPt L m)‖ else 0) ≤
      ∑' m : ℤ, c * tailW n R m :=
    Summable.tsum_le_tsum (fun m => lam_le_tailW L n hn k M hM R hR m) hsum1
      ((tailW_summable n R hn1 hR1').mul_left c)
  have hbound3 : ∑' m : ℤ, c * tailW n R m = c * ∑' m : ℤ, tailW n R m := tsum_mul_left
  have hbound4 : c * ∑' m : ℤ, tailW n R m ≤ c * (2 * ((1 / (n : ℝ)) * (1 / (R : ℝ) ^ n))) :=
    mul_le_mul_of_nonneg_left (tailW_tsum_le n R hn1 hR1') hc0
  have hK0 : (0 : ℝ) ≤ 2 ^ (n + 1 + 2) /
      (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) * (n : ℝ)) := by
    apply div_nonneg (by positivity)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (div_nonneg (by positivity) hL.le) _)) (Nat.cast_nonneg _)
  have halg : c * (2 * ((1 / (n : ℝ)) * (1 / (R : ℝ) ^ n))) =
      2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) * (n : ℝ)) *
        (1 / (R : ℝ) ^ n) := by
    rw [hc]
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    field_simp
    ring
  have hzp : ((R : ℝ) - 1) ^ (1 - ((n + 1 : ℕ) : ℤ)) = 1 / ((R : ℝ) - 1) ^ n := by
    rw [show (1 - ((n + 1 : ℕ) : ℤ)) = -(n : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      one_div]
  have hRn : 1 / (R : ℝ) ^ n ≤ 1 / ((R : ℝ) - 1) ^ n := by
    apply one_div_le_one_div_of_le (pow_pos hRpos n)
    exact pow_le_pow_left₀ hRpos.le (by linarith) n
  calc ‖muGrid L n t k‖
      ≤ ∑' m : ℤ, (if (R : ℤ) < |m| then ‖lamTilde L n k (gridPt L m)‖ else 0) := hbound1
    _ ≤ ∑' m : ℤ, c * tailW n R m := hbound2
    _ = c * ∑' m : ℤ, tailW n R m := hbound3
    _ ≤ c * (2 * ((1 / (n : ℝ)) * (1 / (R : ℝ) ^ n))) := hbound4
    _ = 2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) * (n : ℝ)) *
        (1 / (R : ℝ) ^ n) := halg
    _ ≤ 2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) * (n : ℝ)) *
        (1 / ((R : ℝ) - 1) ^ n) := mul_le_mul_of_nonneg_left hRn hK0
    _ = 2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) * (n : ℝ)) *
        ((R : ℝ) - 1) ^ (1 - ((n + 1 : ℕ) : ℤ)) := by rw [hzp]

end QuantumNLS.HaarKernelTailBounds

#print axioms QuantumNLS.HaarKernelTailBounds.strong_coeff
#print axioms QuantumNLS.HaarKernelTailBounds.odd_tail_vanish
#print axioms QuantumNLS.HaarKernelTailBounds.tailW_tsum_le
#print axioms QuantumNLS.HaarKernelTailBounds.even_tail_eigen_bound
