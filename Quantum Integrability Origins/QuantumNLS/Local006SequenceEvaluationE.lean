import QuantumNLS.Local006SequenceAlgebraE

/-! Exact matrix evaluation of the LOCAL-006 mixed sequence operations.
This binds the sequence multiplication and the convergent binomial series to
their ordinary two-by-two matrix formulas. Source S/K identification and the
collective analytic chart are separate obligations. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
open scoped ENNReal NNReal BigOperators Matrix.Norms.Elementwise

namespace QuantumNLS.Local006.SequenceEvaluationE
open QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.LocalSpectral

def matrix (x : Mixed) (n : ℤ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = 0 then (if j = 0 then x.1.1 n else x.2.1 n)
    else (if j = 0 then x.2.2 n else x.1.2 n)

def evalMatrix (n : ℤ) : Mixed →L[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => matrix x n
      map_add' := fun x y => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, matrix, lp.coeFn_add]
      map_smul' := fun c x => by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply, matrix, lp.coeFn_smul] }
    1 (fun x => by
      rw [one_mul]
      obtain ⟨h00, h11, h01, h10⟩ := component_bounds x
      change ‖matrix x n‖ ≤ ‖x‖
      apply (Matrix.norm_le_iff (norm_nonneg x)).2
      intro i j
      fin_cases i <;> fin_cases j
      · exact (lp.norm_apply_le_norm (by simp) x.1.1 n).trans h00
      · exact (lp.norm_apply_le_norm (by norm_num) x.2.1 n).trans h01
      · exact (lp.norm_apply_le_norm (by norm_num) x.2.2 n).trans h10
      · exact (lp.norm_apply_le_norm (by simp) x.1.2 n).trans h11)

@[simp] lemma evalMatrix_apply (n : ℤ) (x : Mixed) : evalMatrix n x = matrix x n := rfl

theorem matrix_mul (x y : Mixed) (n : ℤ) :
    matrix (mul x y) n = matrix x n * matrix y n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, mul, Matrix.mul_apply, Fin.sum_univ_two, lp.coeFn_add] <;> ring

theorem matrix_unit (n : ℤ) : matrix unit n = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrix, unit]

theorem matrix_power (x : Mixed) (n : ℤ) (k : ℕ) :
    matrix (power x k) n = matrix x n ^ k := by
  induction k with
  | zero => exact matrix_unit n
  | succ k ih =>
    simp only [power, matrix_mul, ih, pow_succ']

/-- Evaluating the Banach-valued inverse square root gives the genuine,
absolutely convergent matrix binomial series, in every frequency. -/
theorem matrix_inverse_sqrt_hasSum (x : Mixed) (hx : 2 * ‖x‖ < 1) (n : ℤ) :
    HasSum (fun k : ℕ => (invSqrtCoeff k : ℂ) • matrix x n ^ k)
      (matrix (inverseSqrt x) n) := by
  have h := (evalMatrix n).hasSum (inverse_sqrt_hasSum x hx)
  simpa only [map_smul, RingHom.id_apply, evalMatrix_apply, matrix_power] using h

/-- Exact lower-left entry of the normalized product is a full l2 sequence.
The input membership is explicit: the eventual source theorem must construct
these mixed sequences, rather than assume them. -/
theorem normalized_lower_left (s k : Mixed) (hs : 2 * ‖s‖ < 1) :
    ∃ b : Seq2,
      (∀ n : ℤ, HasSum (fun j : ℕ => (invSqrtCoeff j : ℂ) • matrix s n ^ j)
        (matrix (inverseSqrt s) n)) ∧
      ∀ n : ℤ, b n =
        (matrix (inverseSqrt s) n * matrix k n * matrix (inverseSqrt s) n) 1 0 := by
  refine ⟨(mul (mul (inverseSqrt s) k) (inverseSqrt s)).2.2,
    matrix_inverse_sqrt_hasSum s hs, fun n => ?_⟩
  change matrix (mul (mul (inverseSqrt s) k) (inverseSqrt s)) n 1 0 = _
  rw [matrix_mul, matrix_mul]

end QuantumNLS.Local006.SequenceEvaluationE

#print axioms QuantumNLS.Local006.SequenceEvaluationE.matrix_mul
#print axioms QuantumNLS.Local006.SequenceEvaluationE.matrix_inverse_sqrt_hasSum
#print axioms QuantumNLS.Local006.SequenceEvaluationE.normalized_lower_left

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.SequenceEvaluationE." ||
        n.toString.startsWith "_private.QuantumNLS.Local006SequenceEvaluationE" then
      pending := pending.push n
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
  Lean.logInfo m!"Local006SequenceEvaluationE audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
