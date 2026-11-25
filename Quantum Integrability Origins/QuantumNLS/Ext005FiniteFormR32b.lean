import QuantumNLS.Ext005SourceHypothesesR114

/-! Intrinsic characterization of the completed form domain by finite
operator-core pairings. The bounded functional is extended and represented;
form-domain membership is a conclusion, not an input. This supplies a
precise finite-form reading for domain containment, without claiming a
spectral functional calculus for unbounded operators. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory UniformSpace
namespace QuantumNLS.Ext005FiniteFormR32b
open Ext005OperatorFormR113 Ext005ShiftR114 Ext005FormEmbeddingR114
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Finiteness of the closed energy form, expressed entirely on D(A).
The bound may depend on x; no continuous embedding is assumed. -/
def FiniteCoreEnergy (A : PositiveOperator H) (x : H) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ v : Core A, ‖⟪x, A.op v⟫_ℂ‖ ≤ M * ‖v‖

/-- A >= 1 and self-adjointness imply that tests against Av separate H. -/
lemma operator_tests_separate (A : PositiveOperator H) (x : H)
    (hx : ∀ v : A.op.domain, ⟪x, A.op v⟫_ℂ = 0) : x = 0 := by
  have hm : x ∈ A.op.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨0, by
      intro v
      rw [inner_zero_left, hx v]⟩
  have heq := LinearPMap.isSelfAdjoint_def.mp A.selfAdjoint
  have hmA : x ∈ A.op.domain := by simpa only [heq] using hm
  have hz : A.op ⟨x, hmA⟩ = 0 := by
    apply A.selfAdjoint.dense_domain.eq_of_inner_left ℂ
    intro v hv
    rw [inner_zero_left]
    exact (operator_symmetric A ⟨x, hmA⟩ ⟨v, hv⟩).trans (hx ⟨v, hv⟩)
  have h := A.lower ⟨x, hmA⟩
  rw [hz, inner_zero_right, Complex.zero_re] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])

/-- Q(A) is exactly the ambient vectors with finite core energy.
The reverse implication constructs a completion vector by Riesz representation. -/
theorem form_domain_iff_finite (A : PositiveOperator H) (x : H) :
    (∃ u : FormDomain A, inclusion A u = x) ↔ FiniteCoreEnergy A x := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨‖u‖, norm_nonneg _, ?_⟩
    intro v
    rw [inclusion_pair]
    simpa only [Completion.norm_coe] using norm_inner_le_norm u (v : FormDomain A)
  · rintro ⟨M, hM, hbound⟩
    let f : Core A →L[ℂ] ℂ := LinearMap.mkContinuous
      { toFun := fun v => ⟪x, A.op v⟫_ℂ
        map_add' := by
          intro u v
          change ⟪x, A.op ((show A.op.domain from u) + (show A.op.domain from v))⟫_ℂ = _
          rw [LinearPMap.map_add, inner_add_right]
        map_smul' := by
          intro c v
          change ⟪x, A.op (c • (show A.op.domain from v))⟫_ℂ = _
          rw [LinearPMap.map_smul, inner_smul_right]
          rfl }
      M hbound
    let F : FormDomain A →L[ℂ] ℂ :=
      f.extend (Completion.toComplL : Core A →L[ℂ] FormDomain A)
    let u : FormDomain A := (toDual ℂ (FormDomain A)).symm F
    have hF (v : Core A) : F (v : FormDomain A) = ⟪x, A.op v⟫_ℂ :=
      f.extend_eq Completion.denseRange_coe (Completion.isUniformInducing_coe _) v
    have hp (v : Core A) : ⟪inclusion A u - x, A.op v⟫_ℂ = 0 := by
      rw [inner_sub_left, inclusion_pair]
      have hu : ⟪u, (v : FormDomain A)⟫_ℂ = F (v : FormDomain A) := toDual_symm_apply
      rw [hu, hF, sub_self]
    refine ⟨u, sub_eq_zero.mp (operator_tests_separate A _ hp)⟩

/-- If the B+1 form is finite at each Q(A) vector in the core-pairing
sense, actual Q(A) subset Q(B+1) follows. No embedding bound is an input. -/
theorem containment_of_finite_forms (A D : PositiveOperator H)
    (hfinite : ∀ u : FormDomain A, FiniteCoreEnergy D (inclusion A u)) :
    FormContained A D := by
  intro u
  exact (form_domain_iff_finite D (inclusion A u)).mpr (hfinite u)

/-- Under that finite-form reading, the continuous embedding and a uniform
B-energy bound follow from the already proved closed graph theorem. -/
theorem comparison_bound_of_finite (A : PositiveOperator H) (B : NonnegativeOperator H)
    (hfinite : ∀ u : FormDomain A, FiniteCoreEnergy (plusOne B) (inclusion A u)) :
    ∃ h : FormContained A (plusOne B), ∃ K : ℝ, 0 ≤ K ∧
      ∀ u : FormDomain A, comparisonEnergy A B h u ≤ K * ‖u‖ ^ 2 := by
  let h := containment_of_finite_forms A (plusOne B) hfinite
  exact ⟨h, ‖comparison A (plusOne B) h‖ ^ 2, sq_nonneg _,
    comparisonEnergy_bound A B h⟩

end QuantumNLS.Ext005FiniteFormR32b
#print axioms QuantumNLS.Ext005FiniteFormR32b.form_domain_iff_finite
#print axioms QuantumNLS.Ext005FiniteFormR32b.containment_of_finite_forms
#print axioms QuantumNLS.Ext005FiniteFormR32b.comparison_bound_of_finite

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005FiniteFormR32b." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005FiniteFormR32b." then
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
  Lean.logInfo m!"R32b aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
