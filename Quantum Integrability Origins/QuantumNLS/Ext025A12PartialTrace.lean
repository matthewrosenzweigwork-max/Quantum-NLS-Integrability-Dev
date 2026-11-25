import QuantumNLS.Ext025A12Normal
import QuantumNLS.Ext025A12Tensor

/-! General partial trace on the repository's trace ideal, defined by duality
and Riesz representation on arbitrary completed complex Hilbert tensor products. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025A12PartialTrace
open TraceClass TraceIdeal TraceCompact TensorCarrier FiniteTraceCompression
  Ext025B11TracePairing Ext025B11TraceBasis Ext025A12Trace Ext025A12Normal Ext025A12Tensor
variable {X Y ι κ : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- The bounded sesquilinear form of the dual trace functional. -/
def form (b : HilbertBasis ι ℂ (HilbertTensor ℂ X Y))
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) :
    X →L⋆[ℂ] X →L[ℂ] ℂ :=
  (ContinuousLinearMap.compL ℂ X (X →L[ℂ] X) ℂ
    ((pairing b T ht).comp (ampliate ℂ X Y))).comp (InnerProductSpace.rankOne ℂ).flip

/-- Partial trace in a specified ambient Hilbert basis. Independence is proved
below. The adjoint converts the Riesz convention into the linear trace convention. -/
def inBasis (b : HilbertBasis ι ℂ (HilbertTensor ℂ X Y))
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) : X →L[ℂ] X :=
  (InnerProductSpace.continuousLinearMapOfBilin (form b T ht)).adjoint

omit [CompleteSpace Y] in
theorem inner_inBasis (b : HilbertBasis ι ℂ (HilbertTensor ℂ X Y))
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) (x y : X) :
    ⟪x,inBasis b T ht y⟫_ℂ = trace b (ampliate ℂ X Y (InnerProductSpace.rankOne ℂ y x)*T) := by
  rw [inBasis,ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- Independence of the ambient basis, including nonseparable Hilbert spaces. -/
theorem inBasis_independent (b : HilbertBasis ι ℂ (HilbertTensor ℂ X Y))
    (c : HilbertBasis κ ℂ (HilbertTensor ℂ X Y))
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) :
    inBasis b T ht = inBasis c T ht := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_inBasis,inner_inBasis]
  exact trace_basis_independent b c _ (lt_top_iff_ne_top.mpr (finite_left _ T ht.ne))

/-- The general trace-class partial trace over the second Hilbert factor. -/
def partialTrace (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y)
    (ht : IsTraceClass T) : X →L[ℂ] X := inBasis (refBasis _) T ht

theorem inner_partialTrace (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y)
    (ht : IsTraceClass T) (x y : X) :
    ⟪x,partialTrace T ht y⟫_ℂ = tr (ampliate ℂ X Y (InnerProductSpace.rankOne ℂ y x)*T) :=
  inner_inBasis _ T ht x y

theorem partialTrace_add (S T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y)
    (hs : IsTraceClass S) (ht : IsTraceClass T) :
    partialTrace (S+T) (hs.add ht) = partialTrace S hs+partialTrace T ht := by
  ext y
  apply ext_inner_left ℂ
  intro x
  simp only [add_apply,inner_add_right,inner_partialTrace,tr,mul_add,
    trace_add _ (lt_top_iff_ne_top.mpr (finite_left _ S hs.ne))
      (lt_top_iff_ne_top.mpr (finite_left _ T ht.ne))]

theorem partialTrace_smul (a : ℂ) (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y)
    (ht : IsTraceClass T) :
    partialTrace (a • T) (finite_smul a ht) = a • partialTrace T ht := by
  ext y
  apply ext_inner_left ℂ
  intro x
  simp only [smul_apply,inner_smul_right,inner_partialTrace,tr,mul_smul_comm,trace_smul]

theorem sum_rankOne_eq (c : HilbertBasis κ ℂ X) (s : Finset κ) (A : X →L[ℂ] X) :
    ∑ i ∈ s, InnerProductSpace.rankOne ℂ (c i) (A (c i)) = proj c s*A.adjoint := by
  simp only [proj,Finset.sum_mul,ContinuousLinearMap.mul_def,InnerProductSpace.rankOne_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem finite_pairing (c : HilbertBasis κ ℂ X) (s : Finset κ) (A : X →L[ℂ] X)
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) :
    ∑ i ∈ s, ⟪A (c i),partialTrace T ht (c i)⟫_ℂ =
      tr (ampliate ℂ X Y (proj c s*A.adjoint)*T) := by
  simp only [inner_partialTrace]
  change (∑ i ∈ s, ((pairing (refBasis _) T ht).comp (ampliate ℂ X Y))
    (InnerProductSpace.rankOne ℂ (c i) (A (c i)))) = _
  rw [← map_sum,sum_rankOne_eq]
  rfl

/-- The exact contraction constant one in the frozen trace norm. -/
theorem traceNorm_partialTrace_le
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) :
    traceNorm (partialTrace T ht) ≤ traceNorm T := by
  rw [← ENNReal.ofReal_toReal ht.ne]
  apply traceNorm_le_of_forall (refBasis X)
  intro A ha s
  rw [finite_pairing]
  apply (RCLike.re_le_norm _).trans
  apply (pairing_bound (refBasis _) _ T ht.ne).trans
  have h : ‖ampliate ℂ X Y (proj (refBasis X) s*A.adjoint)‖ ≤ 1 :=
    (norm_ampliate_le _).trans ((norm_mul_le _ _).trans (by
      have hp := norm_proj_le (refBasis X) s
      have ha' : ‖A.adjoint‖ ≤ 1 := by simpa using ha
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg A.adjoint)).trans
        (by simpa only [one_mul] using ha')))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (ENNReal.toReal_nonneg)

theorem partialTrace_isTraceClass
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) :
    IsTraceClass (partialTrace T ht) := (traceNorm_partialTrace_le T ht).trans_lt ht

open scoped ComplexOrder in
/-- Positivity preservation is proved from the positive trace functional. -/
theorem partialTrace_positive
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T)
    (hT : T.IsPositive) : (partialTrace T ht).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hn : 0 ≤ ⟪x,partialTrace T ht x⟫_ℂ := by
    rw [inner_partialTrace]
    exact pairing_nonneg (refBasis _) _ T
      (ampliate_positive _ (InnerProductSpace.isPositive_rankOne_self x)) hT ht
  have hl : ⟪partialTrace T ht x,x⟫_ℂ = ⟪x,partialTrace T ht x⟫_ℂ := by
    rw [← inner_conj_symm (partialTrace T ht x) x]
    exact Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp hn).2.symm
  rw [hl]
  exact ⟨Complex.ext (by rfl) (by simpa using (Complex.nonneg_iff.mp hn).2),
    (Complex.nonneg_iff.mp hn).1⟩

/-- Full bounded-observable duality, with the source's right-product order. -/
theorem partialTrace_duality
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T)
    (A : X →L[ℂ] X) :
    tr (partialTrace T ht*A) = tr (T*ampliate ℂ X Y A) := by
  let c := refBasis X
  let b := refBasis (HilbertTensor ℂ X Y)
  have hpt := partialTrace_isTraceClass T ht
  have hdiag := (diagonal_summable c (A*partialTrace T ht)
    (finite_left A _ hpt.ne)).hasSum
  have hstrong := pairing_strong b (fun s : Finset (RefIndex X) =>
    ampliate ℂ X Y (proj c s*A)) (ampliate ℂ X Y A) T ht
    (ampliate_proj_mul_strong c A) ‖A‖ (fun s => (norm_ampliate_le _).trans
      ((norm_mul_le _ _).trans (by
        have hp := norm_proj_le c s
        exact mul_le_of_le_one_left (norm_nonneg A) hp)))
  have he (s : Finset (RefIndex X)) :
      ∑ i ∈ s, ⟪c i,(A*partialTrace T ht) (c i)⟫_ℂ =
        trace b (ampliate ℂ X Y (proj c s*A)*T) := by
    have hh := finite_pairing c s A.adjoint T ht
    simp only [ContinuousLinearMap.adjoint_adjoint] at hh
    change (∑ i ∈ s, ⟪A.adjoint (c i),partialTrace T ht (c i)⟫_ℂ) =
      trace b (ampliate ℂ X Y (proj c s*A)*T) at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_apply_eq_comp,ContinuousLinearMap.adjoint_inner_left]
  have hh : trace c (A*partialTrace T ht) = trace b (ampliate ℂ X Y A*T) :=
    tendsto_nhds_unique (by simpa only [HasSum,SummationFilter.unconditional_filter,he,trace] using hdiag) hstrong
  change trace c (partialTrace T ht*A) = trace b (T*ampliate ℂ X Y A)
  rw [← trace_cycle c A _ hpt]
  exact hh.trans (trace_cycle b _ T ht)

/-- The dual pairing characterizes the partial trace uniquely. -/
theorem partialTrace_unique
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T)
    (S : X →L[ℂ] X) (_hs : IsTraceClass S)
    (h : ∀ A : X →L[ℂ] X, tr (S*A) = tr (T*ampliate ℂ X Y A)) :
    S = partialTrace T ht := by
  ext y
  apply ext_inner_left ℂ
  intro x
  have hh := (h (InnerProductSpace.rankOne ℂ y x)).trans
    (partialTrace_duality T ht (InnerProductSpace.rankOne ℂ y x)).symm
  simpa only [tr,trace_rankOne_left] using hh

/-- Partial trace as a complex-linear map between the actual trace ideals. -/
def partialTraceLinear : traceIdeal (HilbertTensor ℂ X Y) →ₗ[ℂ] traceIdeal X where
  toFun T := ⟨partialTrace T.val T.property,partialTrace_isTraceClass T.val T.property⟩
  map_add' S T := Subtype.ext (partialTrace_add S.val T.val S.property T.property)
  map_smul' a T := Subtype.ext (partialTrace_smul a T.val T.property)

/-- Existence and uniqueness with precisely the bounded-observable pairing. -/
theorem existsUnique_partialTrace
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) :
    ∃! S : traceIdeal X, ∀ A : X →L[ℂ] X,
      tr (S.val*A) = tr (T*ampliate ℂ X Y A) := by
  refine ⟨⟨partialTrace T ht,partialTrace_isTraceClass T ht⟩,
    partialTrace_duality T ht,?_⟩
  intro S hs
  exact Subtype.ext (partialTrace_unique T ht S.val S.property hs)

/-- Compatibility with the frozen pure-state reduced density. -/
theorem partialTrace_rankOne (ψ : HilbertTensor ℂ X Y)
    (ht : IsTraceClass (InnerProductSpace.rankOne ℂ ψ ψ)) :
    partialTrace (InnerProductSpace.rankOne ℂ ψ ψ) ht = reducedDensity ψ := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [inner_partialTrace,tr,trace_rankOne_left]
  rw [← (reducedDensity_isSelfAdjoint ψ).adjoint_eq,
    ContinuousLinearMap.adjoint_inner_right,inner_reducedDensity_left]
  rfl

/-- Preservation of the complex trace, hence of positive total mass. -/
theorem partialTrace_trace
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T) :
    tr (partialTrace T ht) = tr T := by
  simpa only [mul_one,ampliate_one] using partialTrace_duality T ht (1 : X →L[ℂ] X)

theorem partialTrace_posTrace
    (T : HilbertTensor ℂ X Y →L[ℂ] HilbertTensor ℂ X Y) (ht : IsTraceClass T)
    (hT : T.IsPositive) : posTrace (partialTrace T ht) = posTrace T := by
  have hp := partialTrace_positive T ht hT
  have he := partialTrace_trace T ht
  simp only [tr,trace_positive _ _ hp,trace_positive _ _ hT] at he
  have hr : (posTrace (partialTrace T ht)).toReal = (posTrace T).toReal := Complex.ofReal_injective he
  have hpf : posTrace (partialTrace T ht) ≠ ⊤ := by
    rw [← traceNorm_of_isPositive hp]
    exact (partialTrace_isTraceClass T ht).ne
  have htf : posTrace T ≠ ⊤ := by
    rw [← traceNorm_of_isPositive hT]
    exact ht.ne
  calc
    posTrace (partialTrace T ht) = ENNReal.ofReal (posTrace (partialTrace T ht)).toReal :=
      (ENNReal.ofReal_toReal hpf).symm
    _ = ENNReal.ofReal (posTrace T).toReal := congrArg ENNReal.ofReal hr
    _ = posTrace T := ENNReal.ofReal_toReal htf

end QuantumNLS.Ext025A12PartialTrace

#print axioms QuantumNLS.Ext025A12PartialTrace.partialTrace
#print axioms QuantumNLS.Ext025A12PartialTrace.inBasis_independent
#print axioms QuantumNLS.Ext025A12PartialTrace.partialTrace_add
#print axioms QuantumNLS.Ext025A12PartialTrace.partialTrace_smul
#print axioms QuantumNLS.Ext025A12PartialTrace.traceNorm_partialTrace_le
#print axioms QuantumNLS.Ext025A12PartialTrace.partialTrace_isTraceClass
#print axioms QuantumNLS.Ext025A12PartialTrace.partialTrace_positive
#print axioms QuantumNLS.Ext025A12PartialTrace.partialTrace_duality
#print axioms QuantumNLS.Ext025A12PartialTrace.partialTrace_unique
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A12PartialTrace" then
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
  Lean.logInfo m!"Ext025A12PartialTrace audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
