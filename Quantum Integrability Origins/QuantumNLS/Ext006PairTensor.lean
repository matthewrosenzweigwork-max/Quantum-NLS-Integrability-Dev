import QuantumNLS.Ext006Blocks

/-!
FIN-CORE-BD-02: construct the completed two-particle tensor of a symmetric HS
operator, with its exact norm and flip symmetry. Author: sol_multi, round 2.
This supplies the pair tensor from the operator; it does not supply convergence
of its Fock pair-creation exponential.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006PairTensor
open TraceClass TensorCarrier
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual matrix coefficients are square summable, by Parseval. -/
lemma matrix_hsSq (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H) :
    (∑' p : ι × ι, ENNReal.ofReal (‖inner ℂ (b p.1) (K (b p.2))‖^2)) = hsSq b K := by
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [tsum_ofReal_norm_inner_sq, hsSq]

/-- Constructed completed coefficient vector, with no finite-rank assumption. -/
def matrixVector (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H) (hK : hsSq b K ≠ ⊤) :
    lp (fun _ : ι × ι => ℂ) 2 :=
  ⟨fun p => inner ℂ (b p.1) (K (b p.2)), by
    apply memℓp_gen
    have hfin : (∑' p : ι × ι, ENNReal.ofReal (‖inner ℂ (b p.1) (K (b p.2))‖^2)) ≠ ⊤ := by
      rwa [matrix_hsSq]
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofNat,
      Real.rpow_two] using ENNReal.summable_toReal hfin⟩

/-- The completed pair tensor whose coefficients are the operator matrix. -/
def pairTensor (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H) (hK : hsSq b K ≠ ⊤) :
    HilbertTensor ℂ H H :=
  (htmulBasis b b).repr.symm (matrixVector b K hK)

lemma pairTensor_coefficient (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hK : hsSq b K ≠ ⊤) (i j : ι) :
    inner ℂ (htmul (b i) (b j)) (pairTensor b K hK) = inner ℂ (b i) (K (b j)) := by
  rw [← htmulBasis_apply b b (i,j), ← HilbertBasis.repr_apply_apply,
    pairTensor, LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma pairTensor_norm_sq (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H) (hK : hsSq b K ≠ ⊤) :
    ‖pairTensor b K hK‖^2 = (hsSq b K).toReal := by
  have h := tsum_ofReal_norm_inner_sq (htmulBasis b b) (pairTensor b K hK)
  simp only [htmulBasis_apply, pairTensor_coefficient, matrix_hsSq] at h
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ht.symm

/-- Matrix symmetry produces genuine symmetry of the completed tensor. -/
lemma pairTensor_flip (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H) (hK : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    htcommIsometry ℂ H H (pairTensor b K hK) = pairTensor b K hK := by
  apply (htmulBasis b b).repr.injective
  apply lp.ext
  funext p
  rcases p with ⟨i,j⟩
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  simp only [htmulBasis_apply]
  have h := (htcommIsometry ℂ H H).inner_map_map (htmul (b j) (b i)) (pairTensor b K hK)
  rw [htcommIsometry_htmul] at h
  rw [h, pairTensor_coefficient, pairTensor_coefficient]
  exact hSym j i

/-- Operator-to-pair-tensor support for every symmetric HS strict contraction.
The operator norm is irrelevant to this construction; it enters only at the
still-open analytic exponential convergence step. -/
theorem «FIN-CORE-BD-02-pair-tensor» (b : HilbertBasis ι ℂ H) (K : H →L[ℂ] H)
    (hK : hsSq b K ≠ ⊤)
    (hSym : ∀ i j, inner ℂ (b i) (K (b j)) = inner ℂ (b j) (K (b i))) :
    ∃ v : HilbertTensor ℂ H H,
      (∀ i j, inner ℂ (htmul (b i) (b j)) v = inner ℂ (b i) (K (b j))) ∧
      ‖v‖^2 = (hsSq b K).toReal ∧ htcommIsometry ℂ H H v = v :=
  ⟨pairTensor b K hK, pairTensor_coefficient b K hK, pairTensor_norm_sq b K hK,
    pairTensor_flip b K hK hSym⟩

end QuantumNLS.Ext006PairTensor

#print axioms QuantumNLS.Ext006PairTensor.matrix_hsSq
#print axioms QuantumNLS.Ext006PairTensor.pairTensor_coefficient
#print axioms QuantumNLS.Ext006PairTensor.pairTensor_norm_sq
#print axioms QuantumNLS.Ext006PairTensor.pairTensor_flip
#print axioms QuantumNLS.Ext006PairTensor.«FIN-CORE-BD-02-pair-tensor»

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PairTensor." then
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
  Lean.logInfo m!"Ext006PairTensor audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
