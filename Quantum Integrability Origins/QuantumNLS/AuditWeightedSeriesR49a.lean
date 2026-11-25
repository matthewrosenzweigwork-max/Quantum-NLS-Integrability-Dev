import Mathlib

/-! R-115CAA16, deterministic weighted-series step. The weight is the EXACT
printed `(1+n²)^(p/2)`. All moment bounds below are explicit analytical
hypotheses of intermediate lemmas; no Born moment bound is asserted here. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.AuditWeightedSeriesR49a

def weight (p : ℝ) (n : ℤ) : ℝ := (1 + (n : ℝ)^2)^(p/2)

theorem weight_pos (p : ℝ) (n : ℤ) : 0 < weight p n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem weight_add_two (p : ℝ) (n : ℤ) :
    weight (p+2) n = weight p n * (1+(n : ℝ)^2) := by
  unfold weight
  rw [show (p+2)/2 = p/2+1 by ring, Real.rpow_add (by positivity), Real.rpow_one]

theorem summable_inverse_square : Summable (fun n : ℤ => (1+(n : ℝ)^2)⁻¹) := by
  apply Summable.of_norm_bounded_eventually
    ((Real.summable_one_div_int_pow (p := 2)).2 (by omega))
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_of_nonneg (by positivity), one_div]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact inv_anti₀ (sq_pos_of_ne_zero hn0) (by linarith)

/-- A bounded moment two orders above the desired weight supplies a
summable pointwise majorant. This is a deterministic sequence criterion. -/
theorem weighted_l1_of_pointwise (a : ℕ → ℤ → ℝ) (A : ℤ → ℝ)
    (p C : ℝ) (ha : ∀ k n, 0 ≤ a k n) (hA : ∀ n, 0 ≤ A n)
    (hC : ∀ k n, weight (p+2) n * a k n ≤ C)
    (hpt : ∀ n, Tendsto (fun k => a k n) atTop (𝓝 (A n))) :
    Tendsto (fun k => ∑' n, weight p n * |a k n-A n|) atTop (𝓝 0) := by
  have hAlim : ∀ n, weight (p+2) n * A n ≤ C := by
    intro n
    exact le_of_tendsto ((hpt n).const_mul _) (Eventually.of_forall fun k => hC k n)
  have hbound : ∀ k n, weight p n * |a k n-A n| ≤
      (2*C) * (1+(n : ℝ)^2)⁻¹ := by
    intro k n
    have hr : 0 < 1+(n : ℝ)^2 := by positivity
    have h1 := hC k n
    have h2 := hAlim n
    rw [weight_add_two] at h1 h2
    rw [← div_eq_mul_inv, le_div_iff₀ hr]
    have h3 : |a k n-A n| ≤ a k n+A n := by
      rw [abs_le]; constructor <;> linarith [ha k n, hA n]
    have h4 := mul_le_mul_of_nonneg_left h3 (weight_pos p n).le
    nlinarith
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun k n => weight p n * |a k n-A n|) (g := fun _ => (0 : ℝ))
    (bound := fun n => (2*C) * (1+(n : ℝ)^2)⁻¹)
    (summable_inverse_square.mul_left (2*C))
    (fun n => by simpa using (((hpt n).sub_const (A n)).abs.const_mul (weight p n)))
    (Eventually.of_forall fun k n => by
      rw [Real.norm_of_nonneg (mul_nonneg (weight_pos p n).le (abs_nonneg _))]
      exact hbound k n)
  simpa using ht

/-- The stronger moment may instead be bounded as a series. Summability
is explicit, preventing a divergent real `tsum` from masquerading as zero. -/
theorem weighted_l1_of_bounded_moment (a : ℕ → ℤ → ℝ) (A : ℤ → ℝ)
    (p C : ℝ) (ha : ∀ k n, 0 ≤ a k n) (hA : ∀ n, 0 ≤ A n)
    (hs : ∀ k, Summable (fun n => weight (p+2) n * a k n))
    (hC : ∀ k, (∑' n, weight (p+2) n * a k n) ≤ C)
    (hpt : ∀ n, Tendsto (fun k => a k n) atTop (𝓝 (A n))) :
    Tendsto (fun k => ∑' n, weight p n * |a k n-A n|) atTop (𝓝 0) := by
  apply weighted_l1_of_pointwise a A p C ha hA ?_ hpt
  intro k n
  exact ((hs k).le_tsum n (fun j _ =>
    mul_nonneg (weight_pos (p+2) j).le (ha k j))).trans (hC k)

end QuantumNLS.AuditWeightedSeriesR49a

#print axioms QuantumNLS.AuditWeightedSeriesR49a.weight

#print axioms QuantumNLS.AuditWeightedSeriesR49a.weight_pos

#print axioms QuantumNLS.AuditWeightedSeriesR49a.weight_add_two

#print axioms QuantumNLS.AuditWeightedSeriesR49a.summable_inverse_square

#print axioms QuantumNLS.AuditWeightedSeriesR49a.weighted_l1_of_pointwise

#print axioms QuantumNLS.AuditWeightedSeriesR49a.weighted_l1_of_bounded_moment

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedSeriesR49a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedSeriesR49a." then
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
