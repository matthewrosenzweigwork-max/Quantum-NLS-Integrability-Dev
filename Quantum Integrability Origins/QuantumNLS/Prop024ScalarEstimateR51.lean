import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Scalar estimates used by the PROP-024 entire Wick remainder argument.

These lemmas isolate the factorial splitting and the sharp geometric ratio
from the operator-valued Weyl translation and maximal-domain argument. -/
noncomputable section
set_option autoImplicit false
namespace QuantumNLS.Prop024ScalarEstimateR51

/-- The binomial coefficient is bounded by the number of all subsets. -/
lemma choose_le_two_pow_real (n k : ℕ) :
    (Nat.choose n k : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast Nat.choose_le_two_pow n k

/-- The exact factorial identity behind the source's split-factorial estimate. -/
lemma choose_factorial_product_le (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k : ℝ) ^ 2 * (k.factorial : ℝ) * ((n-k).factorial : ℝ) ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) := by
  have hfactNat := Nat.choose_mul_factorial_mul_factorial hk
  have hfact : (Nat.choose n k : ℝ) * (k.factorial : ℝ) * ((n-k).factorial : ℝ) =
      (n.factorial : ℝ) := by
    exact_mod_cast hfactNat
  have hchoose := choose_le_two_pow_real n k
  calc
    _ = (Nat.choose n k : ℝ) *
        ((Nat.choose n k : ℝ) * (k.factorial : ℝ) * ((n-k).factorial : ℝ)) := by ring
    _ = (Nat.choose n k : ℝ) * (n.factorial : ℝ) := by rw [hfact]
    _ ≤ (2 : ℝ) ^ n * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_right hchoose (Nat.cast_nonneg _)

/-- The square-root ratio appearing after splitting the factorial. -/
def wickRatio (A Q N : ℝ) : ℝ :=
  Real.sqrt (2*A) * Real.sqrt (32 * Real.exp 1 * Q / N)

/-- The printed cutoff makes the geometric ratio at most one half. -/
theorem wickRatio_le_half (A Q N : ℝ) (hA : 0 < A) (hQ : 1 ≤ Q)
    (hN : 256 * Real.exp 1 * A * Q ≤ N) : wickRatio A Q N ≤ 1/2 := by
  have hNpos : 0 < N := by
    have he : 0 < Real.exp 1 := Real.exp_pos _
    have hlow : 0 < 256 * Real.exp 1 * A * Q := by positivity
    exact lt_of_lt_of_le hlow hN
  have hA0 : 0 ≤ 2*A := by positivity
  have hB0 : 0 ≤ 32 * Real.exp 1 * Q / N := by positivity
  have hsA : Real.sqrt (2*A) ^ 2 = 2*A := Real.sq_sqrt hA0
  have hsB : Real.sqrt (32 * Real.exp 1 * Q / N) ^ 2 =
      32 * Real.exp 1 * Q / N := Real.sq_sqrt hB0
  have hsq : (wickRatio A Q N) ^ 2 ≤ (1/2 : ℝ) ^ 2 := by
    rw [wickRatio, mul_pow, hsA, hsB]
    have hdiv : 64 * Real.exp 1 * A * Q / N ≤ (1/4 : ℝ) := by
      rw [div_le_iff₀ hNpos]
      nlinarith [hN]
    calc
      (2*A) * (32 * Real.exp 1 * Q / N) =
          64 * Real.exp 1 * A * Q / N := by ring
      _ ≤ (1/2 : ℝ)^2 := by
        rw [show (1/2 : ℝ)^2 = 1/4 by norm_num]
        exact hdiv
  have hr0 : 0 ≤ wickRatio A Q N := by
    dsimp [wickRatio]
    positivity
  nlinarith [sq_nonneg (wickRatio A Q N - 1/2)]

/-- The cubic geometric tail in the source proof is at most twice its first term. -/
theorem cubic_geometric_tail (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1/2) :
    ∑' j : ℕ, r ^ (j+3) ≤ 2 * r^3 := by
  have hr1 : r < 1 := by linarith
  have hsum : (∑' j : ℕ, r ^ (j+3)) = r^3 * (∑' j : ℕ, r^j) := by
    rw [show (fun j : ℕ => r ^ (j+3)) = (fun j => r^3 * r^j) by
      funext j
      rw [pow_add]
      ring, tsum_mul_left]
  rw [hsum, tsum_geometric_of_lt_one hr0 hr1]
  have hden : 0 < 1-r := by linarith
  have hinv : (1-r)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hden]
    nlinarith
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hinv (pow_nonneg hr0 3)

end QuantumNLS.Prop024ScalarEstimateR51

#print axioms QuantumNLS.Prop024ScalarEstimateR51.choose_factorial_product_le
#print axioms QuantumNLS.Prop024ScalarEstimateR51.wickRatio_le_half
#print axioms QuantumNLS.Prop024ScalarEstimateR51.cubic_geometric_tail

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024ScalarEstimateR51." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024ScalarEstimateR51." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"PROP-024 scalar audit PASS: {roots} own constants; {seen.size} transitive constants; standard axioms only."
