import QuantumNLS.Ext005ComparisonFormR35b

/-! Identify the already constructed physical cutoff with the actual
negative-real resolvent of A. Operator-domain membership follows from
self-adjointness and the completion pairing, not a spectral-domain axiom.
This supplies a concrete step toward the unresolved source resolvent bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter
namespace QuantumNLS.Ext005PhysicalResolventR35b
open Ext005OperatorFormR113 Ext005GramResolventR112 Ext005ComplexGramR34b
open Ext005SourceHypothesesR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
variable (A : PositiveOperator H)
local instance (priority := 10000) : InnerProductSpace ℝ (FormDomain A) :=
  InnerProductSpace.rclikeToReal ℂ (FormDomain A)

def physicalCutoffC (e : ℝ) (he : 0 < e) : H →L[ℂ] H :=
  (inclusion A).comp ((inverseC (inclusion A) e he).comp (inclusion A).adjoint)

/-- The complex and real adjoints agree on the underlying real vectors. -/
lemma inclusion_adjoint_real (x : H) :
    ((inclusion A).restrictScalars ℝ).adjoint x = (inclusion A).adjoint x := by
  apply ext_inner_right ℝ
  intro v
  exact (((inclusion A).restrictScalars ℝ).adjoint_inner_left v x).trans
    (congrArg Complex.re ((inclusion A).adjoint_inner_left v x)).symm

lemma physicalCutoffC_eq (e : ℝ) (he : 0 < e) (x : H) :
    physicalCutoffC A e he x = physicalCutoff ((inclusion A).restrictScalars ℝ) e he x := by
  change inclusion A (inverse ((inclusion A).restrictScalars ℝ) e he ((inclusion A).adjoint x)) = _
  rw [← inclusion_adjoint_real]
  rfl

/-- A concrete operator-domain and resolvent identity for the constructed
cutoff. Both membership and A's action are conclusions. -/
theorem physicalCutoffC_domain (e : ℝ) (he : 0 < e) (x : H) :
    ∃ hx : physicalCutoffC A e he x ∈ A.op.domain,
      A.op ⟨physicalCutoffC A e he x, hx⟩ = e⁻¹ • (x - physicalCutoffC A e he x) := by
  let i := inclusion A
  let u := inverseC i e he (i.adjoint x)
  have hpert : gram (i.restrictScalars ℝ) u + e • u = i.adjoint x :=
    perturbed_inverse (i.restrictScalars ℝ) e he (i.adjoint x)
  have hpair (v : Core A) : ⟪e⁻¹ • (x - i u), coreVal A v⟫_ℂ =
      ⟪i u, A.op v⟫_ℂ := by
    rw [inclusion_pair]
    have h := congrArg (fun w : FormDomain A => ⟪w, (v : FormDomain A)⟫_ℂ) hpert
    rw [inner_add_left, inner_smul_left_eq_smul, gram_complex_pair,
      ContinuousLinearMap.adjoint_inner_left, inclusion_coe] at h
    rw [inner_smul_left_eq_smul, inner_sub_left]
    have hh : ⟪x, coreVal A v⟫_ℂ - ⟪i u, coreVal A v⟫_ℂ = e • ⟪u, (v : FormDomain A)⟫_ℂ := by
      exact eq_sub_of_add_eq' h |>.symm
    rw [hh, smul_smul, inv_mul_cancel₀ he.ne', one_smul]
  have hm : i u ∈ A.op.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨e⁻¹ • (x - i u), hpair⟩
  have hself := LinearPMap.isSelfAdjoint_def.mp A.selfAdjoint
  have hmA : i u ∈ A.op.domain := by simpa only [hself] using hm
  have ha' : A.op ⟨i u, hmA⟩ = e⁻¹ • (x - i u) := by
    apply A.selfAdjoint.dense_domain.eq_of_inner_left ℂ
    intro v hv
    exact (operator_symmetric A ⟨i u, hmA⟩ ⟨v, hv⟩).trans (hpair ⟨v, hv⟩).symm
  exact ⟨hmA, ha'⟩

lemma inclusion_adjoint_operator (v : Core A) :
    (inclusion A).adjoint (A.op v) = (v : FormDomain A) := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, inclusion_pair]

set_option backward.isDefEq.respectTransparency false in
/-- A genuine two-sided negative-real resolvent of the actual A operator.
The normalization is e P_e = (A+1/e)⁻¹. -/
theorem resolves_negative (e : ℝ) (he : 0 < e) :
    Resolves A.op (-(e⁻¹ : ℝ) : ℂ)
      ((e : ℂ) • physicalCutoffC A e he) := by
  have heC : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  constructor
  · intro x
    obtain ⟨hx, ha⟩ := physicalCutoffC_domain A e he x
    have haC : A.op ⟨physicalCutoffC A e he x, hx⟩ =
        (e : ℂ)⁻¹ • (x - physicalCutoffC A e he x) := by
      rw [ha, ← Complex.ofReal_inv]
      exact (algebraMap_smul ℂ (e⁻¹) (x - physicalCutoffC A e he x)).symm
    have hm := A.op.domain.smul_mem (e : ℂ) hx
    refine ⟨hm, ?_⟩
    change A.op ((e : ℂ) • (⟨physicalCutoffC A e he x, hx⟩ : A.op.domain)) -
      (-(e⁻¹ : ℝ) : ℂ) • ((e : ℂ) • physicalCutoffC A e he x) = x
    rw [LinearPMap.map_smul, haC]
    simp only [Complex.ofReal_inv, smul_smul, mul_inv_cancel₀ heC, neg_mul,
      inv_mul_cancel₀ heC, neg_smul, one_smul]
    abel
  · intro v
    let i := inclusion A
    let q : FormDomain A := (show Core A from v)
    have hi : i.adjoint (v : H) = gram (i.restrictScalars ℝ) q := by
      rw [gram_complex]
      change i.adjoint (v : H) = i.adjoint (inclusion A ((show Core A from v) : FormDomain A))
      exact congrArg i.adjoint (inclusion_coe A (show Core A from v)).symm
    have hpC : perturbed (i.restrictScalars ℝ) e q =
        gram (i.restrictScalars ℝ) q + (e : ℂ) • q := by
      change gram (i.restrictScalars ℝ) q + e • q = _
      exact congrArg (fun w : FormDomain A => gram (i.restrictScalars ℝ) q + w)
        (algebraMap_smul ℂ e q).symm
    have hinput : i.adjoint (A.op v - (-(e⁻¹ : ℝ) : ℂ) • (v : H)) =
        (e : ℂ)⁻¹ • perturbed (i.restrictScalars ℝ) e q := by
      rw [map_sub, map_smul, inclusion_adjoint_operator A (show Core A from v), hi, hpC]
      simp only [Complex.ofReal_inv, neg_smul, sub_neg_eq_add,
        smul_add, smul_smul, inv_mul_cancel₀ heC, one_smul]
      exact add_comm _ _
    change (e : ℂ) • i (inverseC i e he
      (i.adjoint (A.op v - (-(e⁻¹ : ℝ) : ℂ) • (v : H)))) = (v : H)
    rw [hinput, map_smul, map_smul]
    have hr : inverseC i e he (perturbed (i.restrictScalars ℝ) e q) = q :=
      inverse_perturbed (i.restrictScalars ℝ) e he q
    rw [hr, smul_smul, mul_inv_cancel₀ heC, one_smul]
    exact inclusion_coe A (show Core A from v)

end QuantumNLS.Ext005PhysicalResolventR35b
#print axioms QuantumNLS.Ext005PhysicalResolventR35b.physicalCutoffC_domain
#print axioms QuantumNLS.Ext005PhysicalResolventR35b.resolves_negative

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalResolventR35b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalResolventR35b." then
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
  Lean.logInfo m!"R35b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
