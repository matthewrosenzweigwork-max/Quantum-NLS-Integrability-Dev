import NlsGge.GK38.Lib.EntireProductsC34c

/-!
# L4c part 2b, module d: Lemma C.3, the `ℓ²` bounds for the elementary terms

The exceptional set `E` (`c ‖a_m‖ > 1/2`), the sums `Σ_n e_n²` (finite part, book: "clearly
`1 + ℓ²_n`") and `Σ_n B_n²` (the book's `‖B‖_{ℓ²} ≤ ‖B‖_{ℓ¹}` and the double sum
`Σ_m |α_m|² Σ_{n≠m} c̃²/|m-n|² ≤ 4 c̃² Σ|α_m|²`, where the book's `4` is `π²/3 ≈ 3.3 ≤ 4`, here
`K₀ = invSqSum`), all for finite windows `T` of `n`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- The exceptional set: finite, of cardinality at most `4 c² K`, and `c ‖a_m‖ ≤ 1/2` off it. -/
theorem exists_exc_set {a : ℤ → ℂ} (ha : Summable fun m => ‖a m‖ ^ 2) {c K : ℝ} (hc : 0 < c)
    (haK : ∑' m, ‖a m‖ ^ 2 ≤ K) :
    ∃ E : Finset ℤ, (∀ m, m ∉ E → c * ‖a m‖ ≤ 1 / 2) ∧ (E.card : ℝ) ≤ 4 * c ^ 2 * K ∧
      ∑ m ∈ E, ‖a m‖ ^ 2 ≤ K := by
  have hpos : 0 < 1 / (4 * c ^ 2) := by positivity
  have hev := ha.tendsto_cofinite_zero.eventually (gt_mem_nhds hpos)
  have hfin : {m : ℤ | ¬ ‖a m‖ ^ 2 < 1 / (4 * c ^ 2)}.Finite := Filter.eventually_cofinite.mp hev
  refine ⟨hfin.toFinset, fun m hm => ?_, ?_, ?_⟩
  · have h1 : ‖a m‖ ^ 2 < 1 / (4 * c ^ 2) := by
      by_contra h
      exact hm (by simpa using h)
    have h2 : (c * ‖a m‖) ^ 2 < (1 / 2) ^ 2 := by
      calc (c * ‖a m‖) ^ 2 = c ^ 2 * ‖a m‖ ^ 2 := by ring
        _ < c ^ 2 * (1 / (4 * c ^ 2)) := by gcongr
        _ = (1 / 2) ^ 2 := by field_simp; norm_num
    exact (le_abs_self _).trans (abs_lt_of_sq_lt_sq h2 (by norm_num)).le
  · have hsum : ∑ m ∈ hfin.toFinset, ‖a m‖ ^ 2 ≤ K :=
      (ha.sum_le_tsum _ fun _ _ => sq_nonneg _).trans haK
    have hlow : ∀ m ∈ hfin.toFinset, 1 / (4 * c ^ 2) ≤ ‖a m‖ ^ 2 := fun m hm => by
      have := (Set.Finite.mem_toFinset hfin).mp hm
      simpa using this
    have h1 : (hfin.toFinset.card : ℝ) * (1 / (4 * c ^ 2)) ≤ ∑ m ∈ hfin.toFinset, ‖a m‖ ^ 2 := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ hlow
    have h2 : (hfin.toFinset.card : ℝ) ≤ 4 * c ^ 2 * (∑ m ∈ hfin.toFinset, ‖a m‖ ^ 2) := by
      rw [mul_one_div, div_le_iff₀ (by positivity)] at h1
      linarith
    calc (hfin.toFinset.card : ℝ) ≤ 4 * c ^ 2 * (∑ m ∈ hfin.toFinset, ‖a m‖ ^ 2) := h2
      _ ≤ 4 * c ^ 2 * K := by gcongr
  · exact (ha.sum_le_tsum _ fun _ _ => sq_nonneg _).trans haK

/-- `Σ_{n ∈ T} e_n² ≤ |E| c² (Σ_{m∈E} ‖a_m‖²) K₀`. -/
theorem sum_c3eX_sq_le (c : ℝ) (σ ρ : ℤ → ℂ) (E T : Finset ℤ) :
    ∑ n ∈ T, c3eX c σ ρ E n ^ 2 ≤ E.card * (c ^ 2 * (∑ m ∈ E, ‖σ m - ρ m‖ ^ 2) * invSqSum) := by
  have h1 : ∀ n, c3eX c σ ρ E n ^ 2 ≤ E.card * ∑ m ∈ E, c ^ 2 * (‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2) := by
    intro n
    unfold c3eX
    refine (sq_sum_le_card_mul_sum_sq (s := E)).trans ?_
    refine le_of_eq ?_
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  calc ∑ n ∈ T, c3eX c σ ρ E n ^ 2
      ≤ ∑ n ∈ T, (E.card : ℝ) * ∑ m ∈ E, c ^ 2 * (‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2) :=
        Finset.sum_le_sum fun n _ => h1 n
    _ = E.card * ∑ m ∈ E, c ^ 2 * ‖σ m - ρ m‖ ^ 2 * ∑ n ∈ T, c3w n m ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
    _ ≤ E.card * ∑ m ∈ E, c ^ 2 * ‖σ m - ρ m‖ ^ 2 * invSqSum := by
        gcongr with m hm
        exact sum_c3w_sq_le m T
    _ = E.card * (c ^ 2 * (∑ m ∈ E, ‖σ m - ρ m‖ ^ 2) * invSqSum) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem c3B_nonneg (c : ℝ) (σ ρ : ℤ → ℂ) (n : ℤ) : 0 ≤ c3B c σ ρ n := by
  unfold c3B
  exact mul_nonneg (sq_nonneg _) (tsum_nonneg fun m => by have := c3w_nonneg n m; positivity)

theorem summable_c3B_term {σ ρ : ℤ → ℂ} (ha : Summable fun m => ‖σ m - ρ m‖ ^ 2) (n : ℤ) :
    Summable fun m => ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 :=
  ha.of_nonneg_of_le (fun m => by have := c3w_nonneg n m; positivity) (fun m => by
    have := c3w_le_one n m
    have h0 := c3w_nonneg n m
    calc ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 ≤ ‖σ m - ρ m‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
      _ = _ := mul_one _)

theorem c3B_le {c K : ℝ} {σ ρ : ℤ → ℂ} (ha : Summable fun m => ‖σ m - ρ m‖ ^ 2)
    (haK : ∑' m, ‖σ m - ρ m‖ ^ 2 ≤ K) (n : ℤ) : c3B c σ ρ n ≤ c ^ 2 * K := by
  unfold c3B
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  refine ((summable_c3B_term ha n).tsum_le_tsum (fun m => ?_) ha).trans haK
  have := c3w_le_one n m
  have h0 := c3w_nonneg n m
  calc ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 ≤ ‖σ m - ρ m‖ ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg _)
    _ = _ := mul_one _

/-- `Σ_{n∈T} B_n ≤ c² K K₀`. -/
theorem sum_c3B_le {c K : ℝ} {σ ρ : ℤ → ℂ} (ha : Summable fun m => ‖σ m - ρ m‖ ^ 2)
    (haK : ∑' m, ‖σ m - ρ m‖ ^ 2 ≤ K) (T : Finset ℤ) :
    ∑ n ∈ T, c3B c σ ρ n ≤ c ^ 2 * K * invSqSum := by
  have hs := fun n => summable_c3B_term ha n
  have h1 : ∑ n ∈ T, ∑' m, ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2
      = ∑' m, ∑ n ∈ T, ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 :=
    (Summable.tsum_finsetSum fun n _ => hs n).symm
  have hsum : Summable fun m => ∑ n ∈ T, ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 :=
    summable_sum fun n _ => hs n
  have hb : Summable fun m => ‖σ m - ρ m‖ ^ 2 * invSqSum := ha.mul_right _
  have h2 : ∑' m, ∑ n ∈ T, ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 ≤ ∑' m, ‖σ m - ρ m‖ ^ 2 * invSqSum := by
    refine hsum.tsum_le_tsum (fun m => ?_) hb
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_c3w_sq_le m T) (sq_nonneg _)
  calc ∑ n ∈ T, c3B c σ ρ n = c ^ 2 * ∑ n ∈ T, ∑' m, ‖σ m - ρ m‖ ^ 2 * c3w n m ^ 2 := by
        unfold c3B; rw [Finset.mul_sum]
    _ ≤ c ^ 2 * (∑' m, ‖σ m - ρ m‖ ^ 2 * invSqSum) := by
        rw [h1]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ ≤ c ^ 2 * (K * invSqSum) := by
        rw [tsum_mul_right]
        gcongr
        exact invSqSum_nonneg
    _ = c ^ 2 * K * invSqSum := by ring

/-- `Σ_{n∈T} B_n² ≤ (c² K)² K₀`. -/
theorem sum_c3B_sq_le {c K : ℝ} {σ ρ : ℤ → ℂ} (ha : Summable fun m => ‖σ m - ρ m‖ ^ 2)
    (haK : ∑' m, ‖σ m - ρ m‖ ^ 2 ≤ K) (T : Finset ℤ) :
    ∑ n ∈ T, c3B c σ ρ n ^ 2 ≤ (c ^ 2 * K) ^ 2 * invSqSum := by
  have hK : 0 ≤ c ^ 2 * K :=
    (c3B_nonneg c σ ρ 0).trans (c3B_le ha haK 0)
  calc ∑ n ∈ T, c3B c σ ρ n ^ 2 ≤ ∑ n ∈ T, (c ^ 2 * K) * c3B c σ ρ n := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [sq]
        exact mul_le_mul (c3B_le ha haK n) le_rfl (c3B_nonneg c σ ρ n) hK |>.trans_eq (by ring)
    _ = (c ^ 2 * K) * ∑ n ∈ T, c3B c σ ρ n := by rw [Finset.mul_sum]
    _ ≤ (c ^ 2 * K) * (c ^ 2 * K * invSqSum) := mul_le_mul_of_nonneg_left (sum_c3B_le ha haK T) hK
    _ = (c ^ 2 * K) ^ 2 * invSqSum := by ring

end

end NlsGge.GK38.Lib
