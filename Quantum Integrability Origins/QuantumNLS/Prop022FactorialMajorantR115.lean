import QuantumNLS.Prop022TensorCompressionR115

/-! Absolute summation of the exact report factorial majorants, at every
fixed polynomial rank weight. No coefficient regularity is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace QuantumNLS.Prop022FactorialMajorantR115

lemma factorial_le_sqrt_double (m : ℕ) :
    (m.factorial : ℝ) ≤ Real.sqrt ((2*m).factorial : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  have h := Nat.le_of_dvd (Nat.factorial_pos (m+m))
    (Nat.factorial_mul_factorial_dvd_factorial_add m m)
  have hc : (m.factorial : ℝ) * (m.factorial : ℝ) ≤ ((m+m).factorial : ℝ) := by exact_mod_cast h
  simpa [two_mul, sq] using hc

def weight (q : ℕ) (A : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ q * A ^ m / Real.sqrt ((2*m).factorial : ℝ)

lemma weight_bound (q : ℕ) (A : ℝ) (hA : 0 ≤ A) (m : ℕ) :
    weight q A m ≤ (A * 2 ^ q) ^ m / (m.factorial : ℝ) := by
  have hp : (m : ℝ) ^ q ≤ (2 ^ q : ℝ) ^ m := by
    have hm : (m : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast (show m < 2^m from Nat.lt_two_pow_self).le
    calc
      _ ≤ ((2 : ℝ) ^ m) ^ q := pow_le_pow_left₀ (Nat.cast_nonneg m) hm q
      _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  unfold weight
  calc
    _ ≤ ((2 ^ q : ℝ) ^ m * A ^ m) / (m.factorial : ℝ) := by
      apply div_le_div₀ (by positivity) (by gcongr) (by positivity) (factorial_le_sqrt_double m)
    _ = _ := by rw [mul_pow]; ring

lemma weight_summable (q : ℕ) (A : ℝ) (hA : 0 ≤ A) : Summable (weight q A) :=
  Summable.of_nonneg_of_le (fun m => by unfold weight; positivity)
    (weight_bound q A hA) (Real.summable_pow_div_factorial (A * 2 ^ q))

/-- The number-block majorant printed in Q7B:eq:pair (m=r+1). -/
def numberMajorant (A : ℝ) : ℝ := ∑' r, weight 2 A (r+1)

/-- The pair-block majorant C_A printed in Q7B:eq:Q (m=r+2). -/
def pairWeight (A : ℝ) (r : ℕ) : ℝ :=
  (((r+2 : ℕ) : ℝ) * ((r+1 : ℕ) : ℝ)) * A^(r+2) /
    Real.sqrt ((2*(r+2)).factorial : ℝ)

def pairMajorant (A : ℝ) : ℝ := ∑' r, pairWeight A r

lemma pairWeight_le (A : ℝ) (hA : 0 ≤ A) (r : ℕ) :
    pairWeight A r ≤ weight 2 A (r+2) := by
  unfold pairWeight weight
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hA _)
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

lemma number_summable (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun r => weight 2 A (r+1)) :=
  (summable_nat_add_iff 1).mpr (weight_summable 2 A hA)

lemma pair_summable (A : ℝ) (hA : 0 ≤ A) : Summable (pairWeight A) :=
  Summable.of_nonneg_of_le (fun r => by unfold pairWeight; positivity)
    (pairWeight_le A hA) ((summable_nat_add_iff 2).mpr (weight_summable 2 A hA))

lemma numberMajorant_nonneg (A : ℝ) (hA : 0 ≤ A) : 0 ≤ numberMajorant A :=
  tsum_nonneg (fun r => by unfold weight; positivity)

lemma pairMajorant_nonneg (A : ℝ) (hA : 0 ≤ A) : 0 ≤ pairMajorant A :=
  tsum_nonneg (fun r => by unfold pairWeight; positivity)

end QuantumNLS.Prop022FactorialMajorantR115
#print axioms QuantumNLS.Prop022FactorialMajorantR115.weight_summable
#print axioms QuantumNLS.Prop022FactorialMajorantR115.pair_summable

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022FactorialMajorantR115." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022FactorialMajorantR115." then
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
  Lean.logInfo m!"R115 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
