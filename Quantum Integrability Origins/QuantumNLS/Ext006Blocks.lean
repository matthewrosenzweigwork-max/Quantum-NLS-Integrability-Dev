import QuantumNLS.Ext025B6HilbertSchmidtCompletion
import Mathlib.Tactic.Module

/-!
EXT-006 / FIN-CORE-BD-01: the physical-complex-structure block estimates
used in PROP-022, fluctuations.tex:124-134. Author: sol_multi.
These are genuine projections of the supplied bounded real-linear map,
not a change of complex structure. The implementer existence/uniqueness
theorem itself is OPEN and is not postulated in this module.
-/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext006Blocks
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The fixed physical complex structure. -/
def J : E →L[ℝ] E :=
  (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ

@[simp] theorem J_apply (x : E) : J x = Complex.I • x := rfl

@[simp] theorem J_sq (x : E) : J (J x) = -x := by
  simp only [J_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

@[simp] theorem J_norm (x : E) : ‖J x‖ = ‖x‖ := by
  simp only [J_apply, norm_smul, Complex.norm_I, one_mul]

/-- (S-iSi)/2, still carried as a bounded real-linear map. -/
def complexPart (S : E →L[ℝ] E) : E →L[ℝ] E :=
  (1/2 : ℝ) • (S - J ∘L S ∘L J)

/-- (S+iSi)/2, still carried as a bounded real-linear map. -/
def antilinearPart (S : E →L[ℝ] E) : E →L[ℝ] E :=
  (1/2 : ℝ) • (S + J ∘L S ∘L J)

theorem complexPart_apply (S : E →L[ℝ] E) (x : E) :
    complexPart S x = (1/2 : ℝ) • (S x - J (S (J x))) := rfl

theorem antilinearPart_apply (S : E →L[ℝ] E) (x : E) :
    antilinearPart S x = (1/2 : ℝ) • (S x + J (S (J x))) := rfl

theorem parts_sum (S : E →L[ℝ] E) : complexPart S + antilinearPart S = S := by
  ext x
  simp only [add_apply, complexPart_apply, antilinearPart_apply]
  module

theorem complexPart_commutes_J (S : E →L[ℝ] E) (x : E) :
    complexPart S (J x) = J (complexPart S x) := by
  simp only [complexPart_apply, J_sq, map_neg, map_smul, map_sub]
  module

theorem antilinearPart_anticommutes_J (S : E →L[ℝ] E) (x : E) :
    antilinearPart S (J x) = -J (antilinearPart S x) := by
  simp only [antilinearPart_apply, J_sq, map_neg, map_smul, map_add]
  module

theorem complexPart_norm (S : E →L[ℝ] E) : ‖complexPart S‖ ≤ ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [complexPart_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  have htri := norm_sub_le (S x) (J (S (J x)))
  rw [J_norm] at htri
  have h1 := S.le_opNorm x
  have h2 := S.le_opNorm (J x)
  rw [J_norm] at h2
  nlinarith

theorem antilinearPart_norm (S : E →L[ℝ] E) : ‖antilinearPart S‖ ≤ ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [antilinearPart_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
  have htri := norm_add_le (S x) (J (S (J x)))
  rw [J_norm] at htri
  have h1 := S.le_opNorm x
  have h2 := S.le_opNorm (J x)
  rw [J_norm] at h2
  nlinarith

/-- Exact block projection and both bounds used by PROP-022.
This wrapper supplies no implementer or time-dependent propagator. -/
theorem «PROP-022-block-wrapper» (S : E →L[ℝ] E) :
    complexPart S + antilinearPart S = S ∧
    ‖complexPart S‖ ≤ ‖S‖ ∧ ‖antilinearPart S‖ ≤ ‖S‖ :=
  ⟨parts_sum S, complexPart_norm S, antilinearPart_norm S⟩

section HilbertSchmidt
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The source HS condition ensures finite Tr(beta* beta), using the actual
basis-independent trace-ideal definitions, without a number-expectation premise. -/
theorem beta_adjoint_beta_traceClass (b : HilbertBasis ι ℂ H)
    (β : H →L[ℂ] H) (hβ : TraceClass.hsSq b β ≠ ⊤) :
    TraceClass.IsTraceClass (β.adjoint ∘L β) ∧
      TraceClass.posTrace (β.adjoint ∘L β) = TraceClass.hsSq b β := by
  have hp := ContinuousLinearMap.isPositive_adjoint_comp_self β
  have ht : TraceClass.posTrace (β.adjoint ∘L β) = TraceClass.hsSq b β := by
    rw [TraceClass.posTrace_eq b hp, TraceClass.traceIn_adjoint_comp_self]
  refine ⟨?_, ht⟩
  rw [TraceClass.IsTraceClass, TraceClass.traceNorm_of_isPositive hp, ht]
  exact lt_top_iff_ne_top.mpr hβ

end HilbertSchmidt
end QuantumNLS.Ext006Blocks

#print axioms QuantumNLS.Ext006Blocks.parts_sum
#print axioms QuantumNLS.Ext006Blocks.complexPart_commutes_J
#print axioms QuantumNLS.Ext006Blocks.antilinearPart_anticommutes_J
#print axioms QuantumNLS.Ext006Blocks.«PROP-022-block-wrapper»
#print axioms QuantumNLS.Ext006Blocks.beta_adjoint_beta_traceClass

-- COMPLETE NAMESPACE AUDIT
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006Blocks." then
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
  Lean.logInfo m!"Ext006Blocks audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
