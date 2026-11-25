import Mathlib.Analysis.SpecialFunctions.Stirling

/-! PROP-021, exact-number extraction: the source coefficient and the
N^(1/4) loss, with a numerical constant independent of every model parameter.
The coefficient is expressed as a square root of its Poisson probability;
the displayed source exponential/power formula is proved equal below. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QuantumNLS.Prop021CoefficientR128

/-- The probability of the N sector in a coherent state of mean N. -/
def poissonDiagonal (n : ℕ) : ℝ :=
  Real.exp (-(n:ℝ)) * (n:ℝ)^n / (n.factorial:ℝ)

/-- Positive coherent-sector amplitude. -/
def coherentCoefficient (n : ℕ) : ℝ := Real.sqrt (poissonDiagonal n)

lemma poisson_eq (n : ℕ) :
    poissonDiagonal n = ((n:ℝ)/Real.exp 1)^n / (n.factorial:ℝ) := by
  unfold poissonDiagonal
  rw [div_pow,Real.exp_neg,← Real.exp_nat_mul]
  congr 1
  simp only [mul_one,div_eq_mul_inv,mul_comm]

lemma coefficient_pos {n : ℕ} (hn : 1 ≤ n) : 0 < coherentCoefficient n := by
  unfold coherentCoefficient
  rw [poisson_eq]
  have hp : (0:ℝ) < n := by exact_mod_cast hn
  apply Real.sqrt_pos.2
  positivity

/-- The exact printed coefficient, using sqrt(N^N) for N^(N/2). -/
theorem coefficient_source_formula (n : ℕ) :
    coherentCoefficient n =
      Real.exp (-(n:ℝ)/2) * Real.sqrt ((n:ℝ)^n) / Real.sqrt (n.factorial:ℝ) := by
  have he : Real.sqrt (Real.exp (-(n:ℝ))) = Real.exp (-(n:ℝ)/2) := by
    apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_nonneg _) (Real.exp_nonneg _)).2
    rw [← Real.exp_add]
    congr 1
    ring
  unfold coherentCoefficient poissonDiagonal
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (Real.exp_nonneg _),he]

/-- Literal real-power version of the source amplitude. -/
theorem coefficient_printed_formula (n : ℕ) :
    coherentCoefficient n = Real.exp (-(n:ℝ)/2) *
      Real.rpow (n:ℝ) ((n:ℝ)/2) / Real.sqrt (n.factorial:ℝ) := by
  rw [coefficient_source_formula,Real.sqrt_eq_rpow,
    ← Real.rpow_natCast_mul (by positivity : (0:ℝ) ≤ n)]
  congr 2
  congr 1
  ring

/-- A global upper Stirling inequality, derived from monotonicity at N=1. -/
theorem factorial_upper {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial:ℝ) ≤ Real.exp 1 * Real.sqrt (n:ℝ) * ((n:ℝ)/Real.exp 1)^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := Stirling.stirlingSeq'_antitone (show 0 ≤ k by omega)
  simp only [Function.comp_apply,Stirling.stirlingSeq_one] at h
  change Stirling.stirlingSeq (k+1) ≤ Real.exp 1 / Real.sqrt 2 at h
  unfold Stirling.stirlingSeq at h
  have hden : 0 < Real.sqrt (2 * ((k+1:ℕ):ℝ)) *
      (((k+1:ℕ):ℝ)/Real.exp 1)^(k+1) := by positivity
  have hh := (div_le_iff₀ hden).1 h
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  have hs : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  calc
    _ ≤ _ := hh
    _ = _ := by field_simp

/-- The amplification from exact-number projection costs only N^(1/4).
`sqrt(sqrt N)` is the positive fourth root, including in dimension infinity. -/
theorem coefficient_inverse_bound {n : ℕ} (hn : 1 ≤ n) :
    (coherentCoefficient n)⁻¹ ≤
      Real.sqrt (Real.exp 1) * Real.sqrt (Real.sqrt (n:ℝ)) := by
  have hp : (0:ℝ) < n := by exact_mod_cast hn
  have hc := coefficient_pos hn
  have hpow : 0 < ((n:ℝ)/Real.exp 1)^n := by positivity
  have hfac : 0 < (n.factorial:ℝ) := by positivity
  have he : (coherentCoefficient n)^2 =
      ((n:ℝ)/Real.exp 1)^n/(n.factorial:ℝ) := by
    unfold coherentCoefficient
    rw [poisson_eq,Real.sq_sqrt (by positivity)]
  have hs : ((coherentCoefficient n)⁻¹)^2 =
      (n.factorial:ℝ)/((n:ℝ)/Real.exp 1)^n := by
    rw [inv_pow,he,inv_div]
  have hu := (div_le_iff₀ hpow).2 (factorial_upper hn)
  have hr : (Real.sqrt (Real.exp 1) * Real.sqrt (Real.sqrt (n:ℝ)))^2 =
      Real.exp 1 * Real.sqrt (n:ℝ) := by
    rw [mul_pow,Real.sq_sqrt (Real.exp_nonneg _),Real.sq_sqrt (Real.sqrt_nonneg _)]
  have ha : 0 ≤ (coherentCoefficient n)⁻¹ := inv_nonneg.2 hc.le
  have hb : 0 ≤ Real.sqrt (Real.exp 1) * Real.sqrt (Real.sqrt (n:ℝ)) := by positivity
  nlinarith

/-- The fourth root notation equals the source real power. -/
theorem fourthRoot_eq_rpow (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = Real.rpow x (1/4:ℝ) := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_mul hx]
  norm_num
end QuantumNLS.Prop021CoefficientR128
#print axioms QuantumNLS.Prop021CoefficientR128.coefficient_source_formula
#print axioms QuantumNLS.Prop021CoefficientR128.coefficient_inverse_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021CoefficientR128"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R128 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
