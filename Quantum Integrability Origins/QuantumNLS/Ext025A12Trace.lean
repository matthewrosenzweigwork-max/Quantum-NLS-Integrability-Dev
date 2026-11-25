import QuantumNLS.Ext025B11TraceBasis

/-! General complex trace extensions for GP-09. All operators and ideal norms
are those of the frozen repository. No separability assumption is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025A12Trace
open TraceClass TraceIdeal Ext025B11TracePairing Ext025B11TraceBasis
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem finite_smul (a : ℂ) {T : E →L[ℂ] E} (hT : IsTraceClass T) :
    IsTraceClass (a • T) := by
  rw [IsTraceClass, traceNorm_smul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT

theorem finite_sub {S T : E →L[ℂ] E} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S-T) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ T]
  exact hS.add (finite_smul _ hT)

theorem trace_add (b : HilbertBasis ι ℂ E) {S T : E →L[ℂ] E}
    (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace b (S+T) = trace b S + trace b T := by
  simp only [trace, add_apply, inner_add_right]
  exact (diagonal_summable b S hS.ne).tsum_add (diagonal_summable b T hT.ne)

omit [CompleteSpace E] in
theorem trace_smul (b : HilbertBasis ι ℂ E) (a : ℂ) (T : E →L[ℂ] E) :
    trace b (a • T) = a * trace b T := by
  simp only [trace, smul_apply, inner_smul_right, tsum_mul_left]

theorem trace_adjoint (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) :
    trace b T.adjoint = star (trace b T) := by
  change (∑' i, ⟪b i,T.adjoint (b i)⟫_ℂ) = (starRingEnd ℂ) (∑' i, ⟪b i,T (b i)⟫_ℂ)
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro i
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

/-- Positive trace-class operators span the entire complex trace ideal.
This is an elimination theorem, with all four positive pieces constructed. -/
theorem positive_span (P : (E →L[ℂ] E) → Prop)
    (hpos : ∀ T, T.IsPositive → IsTraceClass T → P T)
    (hadd : ∀ S T, IsTraceClass S → IsTraceClass T → P S → P T → P (S+T))
    (hsmul : ∀ (a : ℂ) T, IsTraceClass T → P T → P (a • T))
    (T : E →L[ℂ] E) (ht : IsTraceClass T) : P T := by
  have hsub (S R : E →L[ℂ] E) (hs : IsTraceClass S) (hr : IsTraceClass R)
      (hp : P S) (hq : P R) : P (S-R) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ R]
    exact hadd _ _ hs (finite_smul _ hr) hp (hsmul _ _ hr hq)
  have hself (S : E →L[ℂ] E) (hs : IsSelfAdjoint S) (hts : IsTraceClass S) : P S := by
    have habs : IsTraceClass (CFC.abs S) := by
      simpa only [IsTraceClass,traceNorm, CFC.cfcAbs_cfcAbs] using hts
    have hp : (CFC.abs S + S).IsPositive := by
      apply ContinuousLinearMap.nonneg_iff_isPositive.mp
      rw [CFC.abs_add_self S hs]
      simpa only [two_smul] using add_nonneg (CFC.posPart_nonneg S) (CFC.posPart_nonneg S)
    have hq : (CFC.abs S - S).IsPositive := by
      apply ContinuousLinearMap.nonneg_iff_isPositive.mp
      rw [CFC.abs_sub_self S hs]
      simpa only [two_smul] using add_nonneg (CFC.negPart_nonneg S) (CFC.negPart_nonneg S)
    have he : S = (2 : ℂ)⁻¹ • ((CFC.abs S+S)-(CFC.abs S-S)) := by
      module
    rw [he]
    exact hsmul _ _ (finite_sub (habs.add hts) (finite_sub habs hts))
      (hsub _ _ (habs.add hts) (finite_sub habs hts)
        (hpos _ hp (habs.add hts)) (hpos _ hq (finite_sub habs hts)))
  let S := T+T.adjoint
  let R := (-Complex.I) • (T-T.adjoint)
  have hs : IsSelfAdjoint S := by
    change star S = S
    simp [S, ← ContinuousLinearMap.star_eq_adjoint, add_comm]
  have hr : IsSelfAdjoint R := by
    change star R = R
    simp [R, ← ContinuousLinearMap.star_eq_adjoint, smul_sub,add_comm]
  have hst : IsTraceClass S := ht.add (TraceIdeal.IsTraceClass.adjoint ht)
  have hrt : IsTraceClass R := finite_smul _ (finite_sub ht (TraceIdeal.IsTraceClass.adjoint ht))
  have he : T = (2 : ℂ)⁻¹ • (S + Complex.I • R) := by
    simp only [S,R,smul_smul]
    norm_num
    module
  rw [he]
  exact hsmul _ _ (hst.add (finite_smul _ hrt))
    (hadd _ _ hst (finite_smul _ hrt) (hself S hs hst) (hsmul _ _ hrt (hself R hr hrt)))

/-- Basis independence for every complex trace-class input. -/
theorem trace_basis_independent (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (T : E →L[ℂ] E) (ht : IsTraceClass T) : trace b T = trace c T := by
  apply positive_span (fun T => trace b T = trace c T) _ _ _ T ht
  · intro S hs _
    rw [trace_positive b S hs, trace_positive c S hs]
  · intro S R hs hr hp hq
    rw [trace_add b hs hr,trace_add c hs hr,hp,hq]
  · intro a S _ hp
    rw [trace_smul,trace_smul,hp]

/-- A basis-free complex trace on the repository's trace-class operators. -/
def tr (T : E →L[ℂ] E) : ℂ := trace (refBasis E) T

theorem tr_eq (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (ht : IsTraceClass T) :
    tr T = trace b T := trace_basis_independent _ b T ht

/-- The trace-class objects form a complex submodule of bounded operators. -/
def traceIdeal (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    Submodule ℂ (E →L[ℂ] E) where
  carrier := {T | IsTraceClass T}
  zero_mem' := by
    change IsTraceClass (0 : E →L[ℂ] E)
    rw [IsTraceClass,(traceNorm_eq_zero_iff _).mpr rfl]
    exact ENNReal.zero_lt_top
  add_mem' := fun hs ht => hs.add ht
  smul_mem' := fun a _ ht => finite_smul a ht

end QuantumNLS.Ext025A12Trace

#print axioms QuantumNLS.Ext025A12Trace.positive_span
#print axioms QuantumNLS.Ext025A12Trace.trace_basis_independent
#print axioms QuantumNLS.Ext025A12Trace.tr_eq
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A12Trace" then
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
  Lean.logInfo m!"Ext025A12Trace audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
