import Mathlib

/-! R-EF8C2837 item (iv): a slow diagonal retains every particle number n+1.
This avoids applying a consecutive-particle theorem to an unsupported subsequence.
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.REF88SDiagonal

/-- Given an error tending to zero for each fixed approximation, one can let the
approximation index tend to infinity slowly while the particle index remains n. -/
theorem slow_diagonal (e : ℕ → ℕ → ℝ)
    (he : ∀ j, Tendsto (e j) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, Monotone k ∧ Tendsto k atTop atTop ∧
      Tendsto (fun n => e (k n) n) atTop (𝓝 0) := by
  classical
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N, |e j n| < 1 / ((j : ℝ) + 1) := by
    intro j
    have h := (he j).eventually (Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < 1 / ((j : ℝ) + 1)))
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using eventually_atTop.1 h
  choose N hN using hN
  let C : ℕ → ℕ := fun j => max j (N j)
  let k : ℕ → ℕ := fun n => Nat.findGreatest (fun j => C j ≤ n) n
  have hmono : Monotone k := by
    intro n m hnm
    exact Nat.findGreatest_mono (fun j hj => hj.trans hnm) hnm
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (C j)] with n hn
    exact Nat.le_findGreatest ((le_max_left j (N j)).trans hn) hn
  have hgood : ∀ᶠ n : ℕ in atTop, |e (k n) n| ≤ 1 / (((k n : ℕ) : ℝ) + 1) := by
    filter_upwards [eventually_ge_atTop (C 0)] with n hn
    have hC : C (k n) ≤ n := Nat.findGreatest_spec (P := fun j => C j ≤ n) (Nat.zero_le n) hn
    exact (hN (k n) n ((le_max_right (k n) (N (k n))).trans hC)).le
  have hlim : Tendsto (fun n => 1 / (((k n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  exact ⟨k,hmono,hk,(tendsto_zero_iff_abs_tendsto_zero _).2
    (squeeze_zero' (Eventually.of_forall fun n => abs_nonneg _) hgood hlim)⟩

#print axioms slow_diagonal
end QuantumNLS.REF88SDiagonal
