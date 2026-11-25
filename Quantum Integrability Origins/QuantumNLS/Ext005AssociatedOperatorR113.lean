import QuantumNLS.Ext005OperatorFormR113

/-! The operator recovered from the completed energy form is exactly A.
This checks the operator/form correspondence directly using self-adjointness,
without postulating a spectral square root or its domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory UniformSpace
namespace QuantumNLS.Ext005AssociatedOperatorR113
open Ext005OperatorFormR113
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The completed form is represented by an ambient vector precisely on D(A). -/
theorem represented_iff (S : PositiveOperator H) (u : FormDomain S) (y : H) :
    (∀ v : FormDomain S, ⟪inclusion S v, y⟫_ℂ = ⟪v, u⟫_ℂ) ↔
    ∃ x : S.op.domain, inclusion S u = (x : H) ∧ S.op x = y := by
  constructor
  · intro h
    have hp (w : S.op.domain) : ⟪y, (w : H)⟫_ℂ = ⟪inclusion S u, S.op w⟫_ℂ := by
      let v : Core S := w
      have hv := h (v : FormDomain S)
      rw [inclusion_coe] at hv
      have hc := congrArg (starRingEnd ℂ) hv
      have hc' : ⟪y, coreVal S v⟫_ℂ = ⟪u, (v : FormDomain S)⟫_ℂ := by
        simpa only [inner_conj_symm] using hc
      exact hc'.trans (inclusion_pair S u v).symm
    have hx : inclusion S u ∈ S.op.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨y, hp⟩
    have hEq := LinearPMap.isSelfAdjoint_def.mp S.selfAdjoint
    have hxA : inclusion S u ∈ S.op.domain := by simpa only [hEq] using hx
    refine ⟨⟨inclusion S u, hxA⟩, rfl, ?_⟩
    apply S.selfAdjoint.dense_domain.eq_of_inner_left ℂ
    intro w hw
    exact (operator_symmetric S ⟨inclusion S u, hxA⟩ ⟨w, hw⟩).trans (hp ⟨w, hw⟩).symm
  · rintro ⟨x, hxu, hxy⟩ v
    have hu : u = ((show Core S from x) : FormDomain S) :=
      inclusion_injective S (hxu.trans (inclusion_coe S x).symm)
    rw [hu, ← hxy]
    exact inclusion_pair S v x

/-- The source antidual scale of the constructed Q(A). -/
abbrev FormAntidual (S : PositiveOperator H) := Ext005AntidualR113.Antidual (FormDomain S)

/-- H -> Q(A)* is the actual antilinear test pairing. -/
def ambientAntidual (S : PositiveOperator H) (x : H) : FormAntidual S :=
  innerSLFlip ℂ ((inclusion S).adjoint x)

lemma ambientAntidual_apply (S : PositiveOperator H) (x : H) (v : FormDomain S) :
    ambientAntidual S x v = ⟪inclusion S v, x⟫_ℂ :=
  (inclusion S).adjoint_inner_right v x

lemma ambientAntidual_injective (S : PositiveOperator H) :
    Function.Injective (ambientAntidual S) := by
  intro x y h
  apply (inclusion_dense S).eq_of_inner_left ℂ
  intro v
  have hv := congrArg (fun f : FormAntidual S => f v) h
  rw [ambientAntidual_apply, ambientAntidual_apply] at hv
  simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) hv

end QuantumNLS.Ext005AssociatedOperatorR113
#print axioms QuantumNLS.Ext005AssociatedOperatorR113.represented_iff
#print axioms QuantumNLS.Ext005AssociatedOperatorR113.ambientAntidual_injective

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005AssociatedOperatorR113." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005AssociatedOperatorR113." then
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
  Lean.logInfo m!"R113 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
