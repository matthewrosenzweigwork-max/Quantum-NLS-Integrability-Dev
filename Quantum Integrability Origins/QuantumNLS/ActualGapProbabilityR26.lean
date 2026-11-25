import Mathlib
import QuantumNLS.BornConvergence

/-! Elementary sequential-to-probabilistic passage used for CC:F04:actual-gap.
No cut, monodromy, or uniqueness contract occurs here. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace QuantumNLS.ActualGapProbabilityR26
open BornConvergence (TendstoInProbability)

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, Nonempty (Ω n)]

/-- A deterministic typical array can be selected from convergence in probability. -/
theorem select_sequence (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (e : ∀ n, Ω n → ℝ) (he0 : ∀ n x, 0 ≤ e n x)
    (he : TendstoInProbability P e 0) :
    ∃ x : ∀ n, Ω n, Tendsto (fun n => e n (x n)) atTop (𝓝 0) := by
  classical
  let s (n : ℕ) : Set ℝ := range (e n)
  have hne : ∀ n, (s n).Nonempty := fun n => range_nonempty _
  have hb : ∀ n, BddBelow (s n) := fun n => ⟨0, by rintro _ ⟨x,rfl⟩; exact he0 n x⟩
  have hchoose : ∀ n, ∃ x, e n x < sInf (s n) + 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨y, ⟨x, rfl⟩, hy⟩ := exists_lt_of_csInf_lt (hne n)
      (show sInf (s n) < sInf (s n) + 1 / ((n : ℝ) + 1) by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
    exact ⟨x,hy⟩
  choose x hx using hchoose
  refine ⟨x, ?_⟩
  have hinf : Tendsto (fun n => sInf (s n)) atTop (𝓝 (0 : ℝ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hp := (he (ε / 2) (half_pos hε)).eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))
    filter_upwards [hp] with n hn
    have hex : ∃ y, e n y ≤ ε / 2 := by
      by_contra h
      push Not at h
      have hset : {y | ε / 2 < dist (e n y) 0} = univ := by
        ext y
        simp [abs_of_nonneg (he0 n y), (h y)]
      rw [hset, measure_univ] at hn
      exact (lt_irrefl _ hn)
    obtain ⟨y,hy⟩ := hex
    have hnon : 0 ≤ sInf (s n) := le_csInf (hne n) (by rintro _ ⟨z,rfl⟩; exact he0 n z)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon]
    exact lt_of_le_of_lt ((csInf_le (hb n) (mem_range_self y)).trans hy) (half_lt_self hε)
  have hh : Tendsto (fun n => sInf (s n) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa using hinf.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact squeeze_zero (fun n => he0 n _) (fun n => (hx n).le) hh

/-- Full-sequence deterministic stability implies local uniform stability.
The padding uses a typical array, so no subsequence hypothesis is assumed. -/
theorem local_uniform (e g : ∀ n, Ω n → ℝ) (w : ℝ)
    (he0 : ∀ n x, 0 ≤ e n x) (x₀ : ∀ n, Ω n)
    (h₀ : Tendsto (fun n => e n (x₀ n)) atTop (𝓝 0))
    (hseq : ∀ x : ∀ n, Ω n, Tendsto (fun n => e n (x n)) atTop (𝓝 0) →
      Tendsto (fun n => g n (x n)) atTop (𝓝 w))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x, e n x < δ → |g n x - w| < ε := by
  classical
  by_contra h
  push Not at h
  have hf : ∀ j : ℕ, ∃ᶠ n : ℕ in atTop,
      ∃ x, e n x < 1 / ((j : ℝ) + 1) ∧ ε ≤ |g n x - w| := by
    intro j
    rw [frequently_atTop]
    intro N
    exact h _ (by positivity) N
  obtain ⟨f, hfm, hfx⟩ := extraction_forall_of_frequently hf
  choose x hx hg using hfx
  let z : ∀ n, Ω n := fun n => if hn : ∃ j, f j = n then
    (hn.choose_spec ▸ x hn.choose) else x₀ n
  have hz : ∀ j, z (f j) = x j := by
    intro j
    dsimp only [z]
    rw [dite_eq_left ⟨j,rfl⟩]
    have hi : (Exists.choose (show ∃ k, f k = f j from ⟨j,rfl⟩)) = j :=
      hfm.injective (Exists.choose_spec (show ∃ k, f k = f j from ⟨j,rfl⟩))
    have hc : ∀ (k j : ℕ) (h : f k = f j), k = j → h ▸ x k = x j := by
      intro k j h hk
      subst k
      rfl
    exact hc _ j _ hi
  have hez : Tendsto (fun n => e n (z n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨J,hJ⟩ := eventually_atTop.1
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hη))
    obtain ⟨K,hK⟩ := eventually_atTop.1 (h₀.eventually (gt_mem_nhds hη))
    filter_upwards [eventually_ge_atTop (max K (f J))] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n _)]
    by_cases hex : ∃ j, f j = n
    · obtain ⟨j,rfl⟩ := hex
      rw [hz]
      have hj : J ≤ j := hfm.le_iff_le.1 ((le_max_right K (f J)).trans hn)
      exact (hx j).trans (hJ j hj)
    · simpa only [z, dite_eq_right hex] using hK n ((le_max_left K (f J)).trans hn)
  have ht := (hseq z hez).comp hfm.tendsto_atTop
  obtain ⟨j,hj⟩ := (ht.eventually (Metric.ball_mem_nhds w hε)).exists
  change dist (g (f j) (z (f j))) w < ε at hj
  rw [Real.dist_eq, hz] at hj
  exact (not_lt_of_ge (hg j)) hj

/-- The varying original law is retained throughout this passage. -/
theorem in_probability (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (e g : ∀ n, Ω n → ℝ) (w : ℝ) (he0 : ∀ n x, 0 ≤ e n x)
    (he : TendstoInProbability P e 0)
    (hseq : ∀ x : ∀ n, Ω n, Tendsto (fun n => e n (x n)) atTop (𝓝 0) →
      Tendsto (fun n => g n (x n)) atTop (𝓝 w)) : TendstoInProbability P g w := by
  obtain ⟨x₀,h₀⟩ := select_sequence P e he0 he
  intro ε hε
  obtain ⟨δ,hδ,N,hN⟩ := local_uniform e g w he0 x₀ h₀ hseq (half_pos hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (he (δ / 2) (half_pos hδ))
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  apply measure_mono
  intro x hx
  simp only [mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (he0 n x)] at hx ⊢
  by_contra hh
  have hh' : e n x < δ := lt_of_le_of_lt (not_lt.1 hh) (half_lt_self hδ)
  have := hN n hn x hh'
  linarith

end QuantumNLS.ActualGapProbabilityR26
#print axioms QuantumNLS.ActualGapProbabilityR26.in_probability
