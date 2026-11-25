import QuantumNLS.AuditWeightedSeriesR49a

/-! R-115CAA16: countable diagonal selection. The selected level tends
to infinity along ALL particle numbers; this is not merely a subsequence.
This module supplies the quantifier step for a single common packet.
Physical good events and their finite spectral projections remain to be
instantiated separately. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.AuditWeightedDiagonalR49a
open QuantumNLS.AuditWeightedSeriesR49a

/-- Countably many eventual requirements admit one slowly increasing
level that satisfies its level requirement at every sufficiently large N. -/
theorem slow_diagonal (Q : ℕ → ℕ → Prop) (hQ : ∀ k, ∀ᶠ N in atTop, Q k N) :
    ∃ level : ℕ → ℕ, Tendsto level atTop atTop ∧ ∀ᶠ N in atTop, Q (level N) N := by
  classical
  have hm : ∀ k, ∃ m : ℕ, ∀ N ≥ m, Q k N := fun k => eventually_atTop.1 (hQ k)
  choose m hm using hm
  let S := fun N => (Finset.range (N+1)).filter (fun k => m k ≤ N)
  let level := fun N => if h : (S N).Nonempty then (S N).max' h else 0
  have hmem {N k : ℕ} (hk : k ≤ N) (hmk : m k ≤ N) : k ∈ S N := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hmk⟩
  have hmax {N k : ℕ} (hk : k ∈ S N) : k ≤ level N := by
    have hnon : (S N).Nonempty := ⟨k,hk⟩
    simp only [level, dite_eq_left hnon]
    exact Finset.le_max' _ _ hk
  refine ⟨level, tendsto_atTop.2 (fun k => ?_), ?_⟩
  · filter_upwards [eventually_ge_atTop (max k (m k))] with N hN
    exact hmax (hmem ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN))
  · filter_upwards [eventually_ge_atTop (m 0)] with N hN
    have hnon : (S N).Nonempty := ⟨0,hmem (Nat.zero_le _) hN⟩
    have hmember : level N ∈ S N := by
      simp only [level, dite_eq_left hnon]
      exact Finset.max'_mem _ hnon
    exact hm _ N (Finset.mem_filter.mp hmember).2

/-- A single selected family can impose every fixed requirement before
choosing the order. This is the common-sequence support quantifier. -/
theorem all_fixed_requirements {Ω : ℕ → Type*}
    (E : ℕ → (N : ℕ) → Set (Ω N)) (level : ℕ → ℕ)
    (hlevel : Tendsto level atTop atTop)
    (nested : ∀ k l, k ≤ l → ∀ N, E l N ⊆ E k N)
    (F : (N : ℕ) → Set (Ω N)) (hF : ∀ᶠ N in atTop, F N ⊆ E (level N) N) :
    ∀ k, ∀ᶠ N in atTop, F N ⊆ E k N := by
  intro k
  filter_upwards [hF, hlevel.eventually (eventually_ge_atTop k)] with N hFN hk
  exact hFN.trans (nested k (level N) hk N)

theorem weight_mono {p q : ℝ} (hpq : p ≤ q) (n : ℤ) : weight p n ≤ weight q n := by
  unfold weight
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (n : ℝ)]) (by linarith)

/-- Integer weight orders suffice for EVERY fixed real nonnegative order.
Summability at the larger order is explicit, rather than relying on a
possibly divergent real `tsum`. -/
theorem weighted_error_mono (a A : ℤ → ℝ) {p q : ℝ} (hpq : p ≤ q)
    (hq : Summable (fun n => weight q n * |a n-A n|)) :
    (∑' n, weight p n * |a n-A n|) ≤ ∑' n, weight q n * |a n-A n| := by
  have hle : ∀ n, weight p n * |a n-A n| ≤ weight q n * |a n-A n| :=
    fun n => mul_le_mul_of_nonneg_right (weight_mono hpq n) (abs_nonneg _)
  have hp := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (weight_pos p n).le (abs_nonneg _)) hle hq
  exact hp.tsum_le_tsum hle hq

/-- The sequence/set binder precedes the weight-order binder, preserving
the printed common-packet quantifiers. No physical convergence hypothesis
is discharged by this general order-reduction lemma. -/
theorem real_orders_of_integer_orders {Ω : ℕ → Type*}
    (F : (N : ℕ) → Set (Ω N)) (a : (N : ℕ) → Ω N → ℤ → ℝ) (A : ℤ → ℝ)
    (hs : ∀ (k N : ℕ) (x : Ω N), Summable (fun n => weight (k : ℝ) n * |a N x n-A n|))
    (h : ∀ k : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ x ∈ F N,
      (∑' n, weight (k : ℝ) n * |a N x n-A n|) ≤ ε) :
    ∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ x ∈ F N,
      (∑' n, weight p n * |a N x n-A n|) ≤ ε := by
  intro p _ ε hε
  obtain ⟨k,hk⟩ := exists_nat_ge p
  filter_upwards [h k ε hε] with N hN
  intro x hx
  exact (weighted_error_mono (a N x) A hk (hs k N x)).trans (hN x hx)

end QuantumNLS.AuditWeightedDiagonalR49a

#print axioms QuantumNLS.AuditWeightedDiagonalR49a.slow_diagonal

#print axioms QuantumNLS.AuditWeightedDiagonalR49a.all_fixed_requirements

#print axioms QuantumNLS.AuditWeightedDiagonalR49a.weight_mono

#print axioms QuantumNLS.AuditWeightedDiagonalR49a.weighted_error_mono

#print axioms QuantumNLS.AuditWeightedDiagonalR49a.real_orders_of_integer_orders

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedDiagonalR49a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedDiagonalR49a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round49 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
