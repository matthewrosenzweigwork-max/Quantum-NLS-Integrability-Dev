import QuantumNLS.AuditWeightedShellR50a

/-! Uniform expectations of the bounded shell majorants. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedShellMeanR50a
open QuantumNLS.RootEvent QuantumNLS.AuditWeightedShellR50a

def invSquare (i : ℕ) : ℝ := 1/((i : ℝ)+1)^2

theorem summable_invSquare : Summable invSquare := by
  unfold invSquare
  have h := (summable_nat_add_iff 1).2
    ((Real.summable_one_div_nat_pow (p := 2)).2 (by omega))
  simpa only [Nat.cast_add, Nat.cast_one] using h

theorem shell_main_bound (b i : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    shellWeight b (R+i)/(R+i)^(2*(2*b+2)) ≤ 5^b*invSquare i := by
  have hs : 1 ≤ R+(i : ℝ) := by linarith [show (0 : ℝ) ≤ (i : ℝ) by positivity]
  have hs0 : 0 < R+(i : ℝ) := by linarith
  have hi : (i : ℝ)+1 ≤ R+i := by linarith
  have hpow := pow_le_pow_right₀ hs (show 2*b+2 ≤ 2*(2*b+2) by omega)
  have hp := mul_le_mul (shellWeight_bound b hs)
    (pow_le_pow_left₀ (by positivity : 0 ≤ (i : ℝ)+1) hi 2)
    (sq_nonneg _) (by positivity : 0 ≤ (5 : ℝ)^b*(R+i)^(2*b))
  unfold invSquare
  rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (pow_pos hs0 _) (by positivity)]
  apply hp.trans
  rw [mul_assoc, ← pow_add]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem shell_bias_bound (b i K : ℕ) {R : ℝ} (hR : 1 ≤ R) (hi : i ≤ K) :
    shellWeight b (R+i)/(R+i) ≤ 5^b*(R+K+1)^(2*b) := by
  have hs : 1 ≤ R+(i : ℝ) := by linarith [show (0 : ℝ) ≤ (i : ℝ) by positivity]
  have hi' : (i : ℝ) ≤ K := by exact_mod_cast hi
  have h1 : shellWeight b (R+i)/(R+i) ≤ shellWeight b (R+i) := by
    exact div_le_self (shellWeight_nonneg _ _) hs
  exact h1.trans ((shellWeight_bound b hs).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity)))

/-- Every term of the finite sum is integrable and the error is explicit. -/
theorem mean_shell_bound {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 0 < N) (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → Fin N → ℝ) (hq : Measurable q)
    (b K : ℕ) {R C D : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (htail : ∀ i : ℕ, (∫ ω, tailFraction q (R+i) ω ∂P) ≤
      C/(R+i)^(2*(2*b+2)) + D/((N : ℝ)*(R+i))) :
    (∫ ω, shellMajorant q b K R ω ∂P) ≤
      (1+R^2)^b + 5^b*C*(∑' i, invSquare i) +
      (5^b*D)*((R+K+1)^(2*b+1)/(N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  simp only [shellMajorant]
  rw [integral_add (integrable_const _)
    (integrable_finsetSum _ fun _i _ => (integrable_tailFraction P q hq _).const_mul _),
    integral_const, integral_finsetSum _ (fun _i _ => (integrable_tailFraction P q hq _).const_mul _)]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,integral_const_mul]
  have hterm (i : ℕ) (hi : i ∈ Finset.range (K+1)) :
      shellWeight b (R+i) * (∫ ω, tailFraction q (R+i) ω ∂P) ≤
      5^b*C*invSquare i + (5^b*D/(N : ℝ))*(R+K+1)^(2*b) := by
    apply (mul_le_mul_of_nonneg_left (htail i) (shellWeight_nonneg _ _)).trans
    rw [mul_add]
    apply add_le_add
    · convert mul_le_mul_of_nonneg_left (shell_main_bound b i hR) hC using 1 <;> ring
    · have h := mul_le_mul_of_nonneg_left
        (shell_bias_bound b i K hR (by have := Finset.mem_range.mp hi; omega))
        (div_nonneg hD hNr.le)
      convert h using 1 <;> field_simp
  have hsum := Finset.sum_le_sum hterm
  have hmain : ∑ i ∈ Finset.range (K+1), 5^b*C*invSquare i ≤
      5^b*C*(∑' i, invSquare i) := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact summable_invSquare.sum_le_tsum _ (fun _ _ => by unfold invSquare; positivity)
  have hbias : (∑ _i ∈ Finset.range (K+1),
        (5^b*D/(N : ℝ))*(R+K+1)^(2*b)) ≤
      (5^b*D)*((R+K+1)^(2*b+1)/(N : ℝ)) := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hk : ((K+1 : ℕ) : ℝ) ≤ R+K+1 := by push_cast; linarith
    have h := mul_le_mul_of_nonneg_right hk
      (show 0 ≤ (5^b*D/(N : ℝ))*(R+K+1)^(2*b) by positivity)
    convert h using 1
    rw [pow_succ]
    ring
  rw [Finset.sum_add_distrib] at hsum
  linarith

end QuantumNLS.AuditWeightedShellMeanR50a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedShellMeanR50a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedShellMeanR50a." then
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
  Lean.logInfo m!"Round50 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
