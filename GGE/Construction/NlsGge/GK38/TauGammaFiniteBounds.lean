import NlsGge.GK38.TauGammaValueBounds

/-! Finite coordinate continuity and summable tail bounds meet on one neighborhood. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem finite_continuous_seq_bound38 (a : PotPair → ℤ → ℂ) (S : Finset ℤ) (φ₀ : PotPair)
    (ha : ∀ n ∈ S, ContinuousAt (fun φ => a φ n) φ₀) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ φ ∈ V, ∀ n ∈ S, ‖a φ n‖ ≤ B := by
  let B := ∑ n ∈ S, (‖a φ₀ n‖ + 1)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => by positivity)
  have h : ∀ᶠ φ in 𝓝 φ₀, ∀ n ∈ S, ‖a φ n‖ < ‖a φ₀ n‖ + 1 := by
    apply (Filter.eventually_all_finset S).mpr
    intro n hn
    exact (ha n hn).norm.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨{φ | ∀ n ∈ S, ‖a φ n‖ < ‖a φ₀ n‖ + 1}, Filter.eventually_iff.mp h, B, hB, ?_⟩
  intro φ hφ n hn
  exact (hφ n hn).le.trans (Finset.single_le_sum (f := fun m => ‖a φ₀ m‖ + 1) (fun m _ => by positivity) hn)

theorem finite_tail_square_sum38 (a : ℤ → ℂ) (S : Finset ℤ) (F K B D : ℝ)
    (hF : 0 ≤ F) (hK : 0 ≤ K) (b d : ℤ → ℝ) (hb : ∀ n, 0 ≤ b n) (hd : ∀ n, 0 ≤ d n)
    (hbs : Summable (fun n => b n ^ 2)) (hds : Summable (fun n => d n ^ 2))
    (hbB : (∑' n : ℤ, b n ^ 2) ≤ B) (hdD : (∑' n : ℤ, d n ^ 2) ≤ D)
    (hfinite : ∀ n ∈ S, ‖a n‖ ≤ F) (htail : ∀ n, n ∉ S → ‖a n‖ ≤ b n + K * d n) :
    Summable (fun n => ‖a n‖ ^ 2) ∧
      (∑' n : ℤ, ‖a n‖ ^ 2) ≤ (S.card : ℝ) * F ^ 2 + 2 * B + 2 * K ^ 2 * D := by
  classical
  have hp (n : ℤ) : ‖a n‖ ^ 2 ≤ (if n ∈ S then F ^ 2 else 0) + 2 * b n ^ 2 + 2 * K ^ 2 * d n ^ 2 := by
    by_cases hn : n ∈ S
    · rw [ite_eq_left hn]
      have h := pow_le_pow_left₀ (norm_nonneg _) (hfinite n hn) 2
      nlinarith [sq_nonneg (b n), mul_nonneg (sq_nonneg K) (sq_nonneg (d n))]
    · rw [ite_eq_right hn, zero_add]
      have h := pow_le_pow_left₀ (norm_nonneg _) (htail n hn) 2
      nlinarith [sq_nonneg (b n - K * d n)]
  have hsum (T : Finset ℤ) : ∑ n ∈ T, ‖a n‖ ^ 2 ≤ (S.card : ℝ) * F ^ 2 + 2 * B + 2 * K ^ 2 * D := by
    have hcen : (∑ n ∈ T, if n ∈ S then F ^ 2 else 0) ≤ (S.card : ℝ) * F ^ 2 := by
      rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((T ∩ S).card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : T ∩ S ⊆ S)
      exact mul_le_mul_of_nonneg_right hcard (sq_nonneg F)
    have hbSum := (hbs.sum_le_tsum T (fun n _ => sq_nonneg _)).trans hbB
    have hdSum := (hds.sum_le_tsum T (fun n _ => sq_nonneg _)).trans hdD
    calc
      _ ≤ ∑ n ∈ T, ((if n ∈ S then F ^ 2 else 0) + 2 * b n ^ 2 + 2 * K ^ 2 * d n ^ 2) :=
        Finset.sum_le_sum (fun n _ => hp n)
      _ = (∑ n ∈ T, if n ∈ S then F ^ 2 else 0) + 2 * (∑ n ∈ T, b n ^ 2) +
          2 * K ^ 2 * (∑ n ∈ T, d n ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := add_le_add (add_le_add hcen (mul_le_mul_of_nonneg_left hbSum (by norm_num)))
        (mul_le_mul_of_nonneg_left hdSum (by positivity))
  exact ⟨summable_of_sum_le (fun n => sq_nonneg _) hsum,
    Real.tsum_le_of_sum_le (fun n => sq_nonneg _) hsum⟩

end
end NlsGge.GK38
