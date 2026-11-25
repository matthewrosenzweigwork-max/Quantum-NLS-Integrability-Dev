import QuantumNLS.Ext025B11TracePairing

/-! Basis independence of the complex pairing with a positive trace-class
sandwich, by polarization into four positive bounded conjugations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped InnerProductSpace BigOperators ENNReal ComplexOrder
namespace QuantumNLS.Ext025B11TraceBasis
open TraceClass Ext025B11TracePairing Ext025B7GentleCompression
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem trace_positive (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (hT : T.IsPositive) :
    trace b T = ((posTrace T).toReal : ℂ) := by
  have he (i : ι) : ⟪b i,T (b i)⟫_ℂ = ((⟪b i,T (b i)⟫_ℂ).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hT.inner_nonneg_right (b i))).2.symm
  calc
    trace b T = ∑' i, ((⟪b i,T (b i)⟫_ℂ).re : ℂ) := tsum_congr he
    _ = (((∑' i, (⟪b i,T (b i)⟫_ℂ).re) : ℝ) : ℂ) := (Complex.ofReal_tsum _).symm
    _ = _ := by
      congr 1
      rw [posTrace_eq b hT,traceIn,ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
      apply tsum_congr
      intro i
      exact (ENNReal.toReal_ofReal (hT.re_inner_nonneg_right (b i))).symm

/-- Every positive bounded conjugation has finite trace. -/
theorem conjugate_finite (T X : E →L[ℂ] E) (hT : T.IsPositive)
    (ht : IsTraceClass T) : traceNorm (X*T*X.adjoint) ≠ ⊤ := by
  rw [traceNorm_of_isPositive (block_positive T X hT)]
  exact block_finite T X hT ht

/-- Four positive conjugations recover the complex pairing. -/
theorem polarization (b : HilbertBasis ι ℂ E) (K T : E →L[ℂ] E)
    (hT : T.IsPositive) (ht : IsTraceClass T) :
    trace b (K*T) = (4 : ℂ)⁻¹ *
      (trace b ((K+1)*T*(K+1).adjoint)-trace b ((K-1)*T*(K-1).adjoint)+
        Complex.I*(trace b ((K+Complex.I • 1)*T*(K+Complex.I • 1).adjoint)-
          trace b ((K-Complex.I • 1)*T*(K-Complex.I • 1).adjoint))) := by
  have hs (X : E →L[ℂ] E) :=
    diagonal_summable b (X*T*X.adjoint) (conjugate_finite T X hT ht)
  have hh := (((hs (K+1)).hasSum.sub (hs (K-1)).hasSum).add
    (((hs (K+Complex.I • 1)).hasSum.sub (hs (K-Complex.I • 1)).hasSum).mul_left Complex.I)).mul_left (4 : ℂ)⁻¹
  unfold trace
  rw [← hh.tsum_eq]
  apply tsum_congr
  intro i
  simp only [← ContinuousLinearMap.star_eq_adjoint,star_smul,star_one,
    Complex.star_def,Complex.conj_I,map_add,map_sub,map_smul,
    mul_apply_eq_comp,add_apply,sub_apply,smul_apply,one_apply_eq_self,
    inner_add_right,inner_sub_right,inner_smul_right]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The physical complex expectation is independent of the chosen basis,
including arbitrary non-Hermitian bounded K. -/
theorem pairing_basis_independent (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (K T : E →L[ℂ] E) (hT : T.IsPositive) (ht : IsTraceClass T) :
    trace b (K*T) = trace c (K*T) := by
  rw [polarization b K T hT ht,polarization c K T hT ht]
  simp only [trace_positive _ _ (block_positive T _ hT)]
end QuantumNLS.Ext025B11TraceBasis

#print axioms QuantumNLS.Ext025B11TraceBasis.pairing_basis_independent
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B11TraceBasis" then
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
  Lean.logInfo m!"Ext025B11TraceBasis audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
