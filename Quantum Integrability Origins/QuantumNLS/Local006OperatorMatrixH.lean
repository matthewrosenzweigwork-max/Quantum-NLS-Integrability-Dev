import QuantumNLS.Local006SourceBindingH
import QuantumNLS.Local006CollectiveF

/-! Exact matrix transport of the frozen free compression, including its
constant terms. All source matrices retain the ordered free basis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Metric
open scoped BigOperators ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace QuantumNLS.Local006.OperatorMatrixH
open QuantumNLS.LocalSpectral QuantumNLS.Local005 QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceBindingH QuantumNLS.ResetFreeResolventLOCAL001
  QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

abbrev basisVec (j : Fin 2) : E2 := EuclideanSpace.single j (1 : ℂ)

def opMatrix : (E2 →L[ℂ] E2) →L[ℂ] Mat :=
  LinearMap.mkContinuous
    { toFun := fun T i j => T (basisVec j) i
      map_add' := fun T S => by ext i j; rfl
      map_smul' := fun c T => by ext i j; rfl }
    1 (fun T => by
      rw [one_mul]
      apply (Matrix.norm_le_iff (norm_nonneg T)).2
      intro i j
      exact (PiLp.norm_apply_le (T (basisVec j)) i).trans
        (by simpa only [basisVec, EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] using T.le_opNorm (basisVec j)))

@[simp] lemma opMatrix_apply (T : E2 →L[ℂ] E2) (i j : Fin 2) :
    opMatrix T i j = T (basisVec j) i := rfl

lemma basis_decompose (v : E2) : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
  ext i
  fin_cases i <;> simp [basisVec]

lemma opMatrix_mul (T S : E2 →L[ℂ] E2) : opMatrix (T * S) = opMatrix T * opMatrix S := by
  ext i j
  change T (S (basisVec j)) i = _
  rw [basis_decompose (S (basisVec j)), map_add, map_smul, map_smul]
  simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[simp] lemma opMatrix_one : opMatrix (1 : E2 →L[ℂ] E2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [basisVec]

lemma opMatrix_pow (T : E2 →L[ℂ] E2) (k : ℕ) : opMatrix (T ^ k) = opMatrix T ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, opMatrix_mul, ih, pow_succ]

variable {L r κ : ℝ} [Fact (0 < L)]

lemma compression_entry (n : ℤ) (A : Op L) (i j : Fin 2) :
    opMatrix ((embed L n).adjoint ∘L A ∘L embed L n) i j = entryFunctional n i j A := by
  rw [opMatrix_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    QuantumNLS.Local003First.adjE_apply]
  have he : embed L n (basisVec j) = chi L n j := by
    rw [embed_apply]
    fin_cases j <;> simp [basisVec]
  rw [he]
  rfl

lemma sourceWord_zero_entry (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (n : ℤ) (i j : Fin 2) :
    entryFunctional n i j (sourceWord hL hκ hr hs kind u n 0) =
      match kind with | .projection => (if i = j then 1 else 0 : ℂ) | .moment => 0 := by
  change entryFunctional n i j (freeProj L κ n r *
    contourJ hr n (weight kind n (freeContour (κ := κ) hL hr hs n)) * freeProj L κ n r) = _
  rw [compressed_contour_entry hL hr hs n i j]
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    (∮ z in C(center L n, r), scalarExtend
      (functionalContour n (entryFunctional n i j) (weight kind n (freeContour (κ := κ) hL hr hs n))) z) = _
  have hf (z : ℂ) (hz : z ∈ sphere (center L n) r) :
      entryFunctional n i j (free L κ n z) =
        (z - center L n)⁻¹ * (if i = j then 1 else 0 : ℂ) := by
    change ⟪chi L n i, free L κ n z (chi L n j)⟫_ℂ = _
    rw [free_inner_zero hL hr hs n (mem_sphere_iff_norm.mp hz), inner_chi hL]
    rfl
  cases kind with
  | projection =>
    have he : (∮ z in C(center L n, r), scalarExtend
        (functionalContour n (entryFunctional n i j) (weight WordKind.projection n
          (freeContour (κ := κ) hL hr hs n))) z) =
        ∮ z in C(center L n, r), (z - center L n)⁻¹ • (if i = j then 1 else 0 : ℂ) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      rw [scalarExtend_apply _ hz]
      exact hf z hz
    rw [he, circleIntegral.integral_smul_const,
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr), smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_mul]
  | moment =>
    have he : (∮ z in C(center L n, r), scalarExtend
        (functionalContour n (entryFunctional n i j) (weight WordKind.moment n
          (freeContour (κ := κ) hL hr hs n))) z) =
        ∮ z in C(center L n, r), (if i = j then 1 else 0 : ℂ) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      rw [scalarExtend_apply _ hz]
      change entryFunctional n i j ((z - center L n) • free L κ n z) = _
      rw [map_smul, smul_eq_mul, hf z hz, ← mul_assoc, mul_inv_cancel₀]
      · simp
      · apply norm_pos_iff.mp
        rw [mem_sphere_iff_norm.mp hz]
        exact hr
    have hc : (∮ _z in C(center L n, r), (if i = j then 1 else 0 : ℂ)) = 0 :=
      Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
        continuousOn_const (fun _ _ => differentiableAt_const _)
    rw [he, hc, mul_zero]

lemma sourceCompressed_projection_entry (hL : 0 < L) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (n : ℤ) (i j : Fin 2) :
    entryFunctional n i j (sourceCompressed (κ := κ) (r := r) .projection u n) =
      opMatrix (compressionMatrix L κ (u : ℝ → ℂ) n r) i j := by
  unfold sourceCompressed compression
  rw [entry_free_compression hL hr hs]
  exact (compression_entry n _ i j).symm

lemma sourceCompressed_moment_entry (hL : 0 < L) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (n : ℤ) (i j : Fin 2) :
    entryFunctional n i j (sourceCompressed (κ := κ) (r := r) .moment u n) =
      opMatrix (QuantumNLS.Local006.CompressionE.momentMatrix L κ (u : ℝ → ℂ) n r) i j := by
  unfold sourceCompressed
  rw [entry_free_compression hL hr hs]
  exact (compression_entry n _ i j).symm

end QuantumNLS.Local006.OperatorMatrixH
#print axioms QuantumNLS.Local006.OperatorMatrixH.sourceWord_zero_entry
#print axioms QuantumNLS.Local006.OperatorMatrixH.sourceCompressed_projection_entry

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.OperatorMatrixH." ||
        n.toString.startsWith "_private.QuantumNLS.Local006OperatorMatrixH" then
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
  Lean.logInfo m!"Local006OperatorMatrixH audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
