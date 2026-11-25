import QuantumNLS.TraceIdeal
import QuantumNLS.PhysicalEnergyTrace

/-! Literal source contract FIN-EXT025-GP-09 (coverage qualifications follow below).
Hypotheses:
The operators act on separable Hilbert spaces. Trace-class and Hilbert–Schmidt factors have the indicated finite ideal norms; cyclic rearrangements include one trace-class factor and bounded other factors.
For positive energy sandwiches the trace of the nonnegative form against the density matrix is finite. Partial traces are over a Hilbert tensor factor.
Conclusion:
The trace ideals are complete two-sided ideals; the product of two Hilbert–Schmidt operators is trace class with the product-norm bound. The trace is basis independent and cyclic with bounded factors. Partial trace is positive, trace preserving on positive inputs and contractive in trace norm.
Application wrappers:
Construct the partial trace by matrix elements and sums over an orthonormal basis, first for positive finite-rank matrices and then by trace-norm completion. Its dual pairing with B is the full trace pairing with B tensor identity; the bounded-operator dual norm yields contraction.
If rho is positive and has finite A energy, A^(1/2) rho A^(1/2) is defined as the positive trace-class form sandwich, with trace equal to the form expectation. For a projection P, split rho into four P/complement blocks and factor the cross blocks through rho^(1/2). Hilbert–Schmidt Cauchy–Schwarz bounds them by the square root of the product of the two positive diagonal traces. This is the report’s gentle-compression estimate, not an additional imported compactness theorem.
An integral kernel in L2 gives a Hilbert–Schmidt operator with its L2 kernel norm. This is the exact estimate used for the two Volterra kernels and for the physical pairing kernel.
-/

/-! FIN-EXT025-GP-09: new HS-product bound and faithful frozen trace wrappers.
Completion, complex cyclic trace, general mixed-state partial trace and the
measurable L2-kernel isometry are OPEN, not replaced by the pure-state results.
No field in this module supplies an ideal or partial-trace conclusion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate ENNReal ComplexOrder
open InnerProductSpace
namespace QuantumNLS.Ext025STrace
open TraceClass TraceIdeal TraceCompact TensorCarrier
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The product of two Hilbert-Schmidt factors is trace class, with the
product of their HS norms. Neither factor is assumed trace class. -/
theorem hs_product_bound (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E)
    (hA : hsSq b A ≠ ⊤) (hB : hsSq b B ≠ ⊤) :
    traceNorm (A * B) ≤ ENNReal.ofReal
      (Real.sqrt (hsSq b A).toReal * Real.sqrt (hsSq b B).toReal) := by
  apply traceNorm_le_of_forall b
  intro X hX s
  have hswap : hsSq b (A.adjoint * X) ≤ hsSq b A := by
    rw [hsSq_eq_hsSq_adjoint b b]
    have he : (A.adjoint * X).adjoint = X.adjoint ∘L A := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint]
    rw [he]
    exact hsSq_comp_le b (by simpa using hX) A
  have ha : ∑ i ∈ s, ‖(A.adjoint * X) (b i)‖ ^ 2 ≤ (hsSq b A).toReal :=
    (sum_norm_sq_le b _ (ne_top_of_le_ne_top hA hswap) s).trans
      (ENNReal.toReal_mono hA hswap)
  have hb := sum_norm_sq_le b B hB s
  have he : ∑ i ∈ s, ⟪X (b i), (A * B) (b i)⟫_ℂ =
      ∑ i ∈ s, ⟪(A.adjoint * X) (b i), B (b i)⟫_ℂ := by
    apply Finset.sum_congr rfl
    intro i _
    exact (A.adjoint_inner_left _ _).symm
  rw [he]
  have hnorm : ‖∑ i ∈ s, ⟪(A.adjoint * X) (b i), B (b i)⟫_ℂ‖ ≤
      ∑ i ∈ s, ‖(A.adjoint * X) (b i)‖ * ‖B (b i)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_inner_le_norm _ _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => ‖(A.adjoint * X) (b i)‖) (fun i => ‖B (b i)‖)
  have hsq : (∑ i ∈ s, ‖(A.adjoint * X) (b i)‖ * ‖B (b i)‖)^2 ≤
      (hsSq b A).toReal * (hsSq b B).toReal :=
    hcs.trans (mul_le_mul ha hb (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      ENNReal.toReal_nonneg)
  have hr : (Real.sqrt (hsSq b A).toReal * Real.sqrt (hsSq b B).toReal)^2 =
      (hsSq b A).toReal * (hsSq b B).toReal := by
    rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg]
  have hle : (∑ i ∈ s, ‖(A.adjoint * X) (b i)‖ * ‖B (b i)‖) ≤
      Real.sqrt (hsSq b A).toReal * Real.sqrt (hsSq b B).toReal := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)).mp
    rwa [hr]
  exact (RCLike.re_le_norm _).trans (hnorm.trans hle)

theorem hs_product_traceClass (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E)
    (hA : hsSq b A ≠ ⊤) (hB : hsSq b B ≠ ⊤) : IsTraceClass (A * B) :=
  (hs_product_bound b A B hA hB).trans_lt ENNReal.ofReal_lt_top

/-- GP-09 proved ideal clauses. Completeness and cyclicity are explicitly
not claimed by this named partial contract; see Ext025S.gaps.json. -/
theorem «FIN-EXT025-GP-09» (W T V : E →L[ℂ] E) :
    traceNorm (W * T * V) ≤ ENNReal.ofReal ‖W‖ * traceNorm T * ENNReal.ofReal ‖V‖ ∧
    traceNorm T.adjoint = traceNorm T ∧
    (IsTraceClass T → IsTraceClass (W * T * V)) ∧
    (∀ (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] E),
      hsSq b A ≠ ⊤ → hsSq b B ≠ ⊤ →
      IsTraceClass (A * B) ∧ traceNorm (A * B) ≤ ENNReal.ofReal
        (Real.sqrt (hsSq b A).toReal * Real.sqrt (hsSq b B).toReal)) := by
  refine ⟨traceNorm_mul_mul_le W T V, traceNorm_adjoint T, ?_, ?_⟩
  · intro hT
    exact (traceNorm_mul_mul_le W T V).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT) ENNReal.ofReal_lt_top)
  · intro b A B hA hB
    exact ⟨hs_product_traceClass b A B hA hB, hs_product_bound b A B hA hB⟩

/-- Positive bounded sandwiches, with the quantitative trace bound. -/
theorem positive_compression (T W : E →L[ℂ] E) (hT : T.IsPositive) :
    (W.adjoint * T * W).IsPositive ∧
    posTrace (W.adjoint * T * W) ≤ ENNReal.ofReal (‖W‖ ^ 2) * posTrace T := by
  have hp : (W.adjoint * T * W).IsPositive := by
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using hT.adjoint_conj W
  refine ⟨hp, ?_⟩
  rw [← traceNorm_of_isPositive hp, ← traceNorm_of_isPositive hT]
  refine (traceNorm_mul_mul_le W.adjoint T W).trans (le_of_eq ?_)
  rw [LinearIsometryEquiv.norm_map, pow_two, ENNReal.ofReal_mul (norm_nonneg _)]
  ring

/-- Positive block trace is exactly the squared HS norm of its square-root
factor. This is valid for arbitrary bounded blocks, not just projections. -/
theorem block_trace_hs (b : HilbertBasis ι ℂ E) (ρ P : E →L[ℂ] E)
    (hρ : ρ.IsPositive) : posTrace (P * ρ * P.adjoint) = hsSq b (P * CFC.sqrt ρ) := by
  let S := P * CFC.sqrt ρ
  have hs : IsSelfAdjoint (CFC.sqrt ρ) := (CFC.sqrt_nonneg ρ).isSelfAdjoint
  have he : S * S.adjoint = P * ρ * P.adjoint := by
    dsimp [S]
    change (P * CFC.sqrt ρ) * star (P * CFC.sqrt ρ) = P * ρ * star P
    rw [star_mul, hs.star_eq, mul_assoc, ← mul_assoc (CFC.sqrt ρ),
      CFC.sqrt_mul_sqrt_self ρ (ContinuousLinearMap.nonneg_iff_isPositive.mpr hρ), ← mul_assoc]
  have hp : (S * S.adjoint).IsPositive := by
    simpa only [ContinuousLinearMap.mul_def] using ContinuousLinearMap.isPositive_self_comp_adjoint S
  rw [← he, posTrace_eq b hp]
  calc traceIn b (S * S.adjoint) = hsSq b S.adjoint := by
         simpa only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.mul_def] using
           traceIn_adjoint_comp_self b S.adjoint
       _ = hsSq b S := (hsSq_eq_hsSq_adjoint b b S).symm

/-- Positive cross blocks are bounded by the square root of the product of
the two diagonal traces. Taking P and 1-P gives the report's cross-block step. -/
theorem gp09_cross_block (b : HilbertBasis ι ℂ E) (ρ P Q : E →L[ℂ] E)
    (hρ : ρ.IsPositive) (hP : posTrace (P * ρ * P.adjoint) ≠ ⊤)
    (hQ : posTrace (Q * ρ * Q.adjoint) ≠ ⊤) :
    traceNorm (P * ρ * Q.adjoint) ≤ ENNReal.ofReal
      (Real.sqrt (posTrace (P * ρ * P.adjoint)).toReal *
       Real.sqrt (posTrace (Q * ρ * Q.adjoint)).toReal) := by
  have hs : IsSelfAdjoint (CFC.sqrt ρ) := (CFC.sqrt_nonneg ρ).isSelfAdjoint
  have he : CFC.sqrt ρ * Q.adjoint = (Q * CFC.sqrt ρ).adjoint := by
    change CFC.sqrt ρ * star Q = star (Q * CFC.sqrt ρ)
    rw [star_mul, hs.star_eq]
  have hswap : hsSq b (CFC.sqrt ρ * Q.adjoint) = hsSq b (Q * CFC.sqrt ρ) := by
    rw [he]
    exact (hsSq_eq_hsSq_adjoint b b _).symm
  have hbound := hs_product_bound b (P * CFC.sqrt ρ) (CFC.sqrt ρ * Q.adjoint)
    (by rwa [← block_trace_hs b ρ P hρ])
    (by rwa [hswap, ← block_trace_hs b ρ Q hρ])
  have hp : (P * CFC.sqrt ρ) * (CFC.sqrt ρ * Q.adjoint) = P * ρ * Q.adjoint := by
    rw [mul_assoc, ← mul_assoc (CFC.sqrt ρ), CFC.sqrt_mul_sqrt_self ρ (ContinuousLinearMap.nonneg_iff_isPositive.mpr hρ),
      ← mul_assoc]
  rwa [hp, hswap, ← block_trace_hs b ρ P hρ, ← block_trace_hs b ρ Q hρ] at hbound

/-- Basis independence includes infinite positive traces. -/
theorem positive_trace_basis {κ : Type*} (b : HilbertBasis ι ℂ E)
    (d : HilbertBasis κ ℂ E) (T : E →L[ℂ] E) (hT : T.IsPositive) :
    traceIn b T = traceIn d T := traceIn_eq_of_basis b d hT

section Tensor
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
/-- Pure-state partial trace: positivity, exact trace in every basis and
trace-class membership, on an actual completed Hilbert tensor factor. -/
theorem gp09_pure_partial_trace {κ : Type*} (b : HilbertBasis κ ℂ X)
    (ψ : HilbertTensor ℂ X Y) :
    (reducedDensity ψ).IsPositive ∧ traceIn b (reducedDensity ψ) = ENNReal.ofReal (‖ψ‖^2) ∧
    IsTraceClass (reducedDensity ψ) := by
  refine ⟨reducedDensity_isPositive ψ, traceIn_reducedDensity b ψ, ?_⟩
  rw [IsTraceClass, traceNorm_of_isPositive (reducedDensity_isPositive ψ), posTrace,
    traceIn_reducedDensity]
  exact ENNReal.ofReal_lt_top

/-- The frozen reduced-density continuity estimate, with its exact norm. -/
theorem gp09_pure_partial_trace_stability (ψ φ : HilbertTensor ℂ X Y) :
    traceNorm (reducedDensity ψ - reducedDensity φ) ≤
      ENNReal.ofReal (‖ψ - φ‖ * (‖ψ‖ + ‖φ‖)) := traceNorm_reducedDensity_sub_le ψ φ
end Tensor

section Energy
open PhysicalEnergyTrace
variable (L : ℝ) (k : ℕ)
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
/-- The physical kinetic-energy sandwich wrapper retains finite form energy
and does not require range(rho) to lie in the operator domain. -/
theorem gp09_energy_sandwich (e : X ≃ₗᵢ[ℂ] QuantumNLS.Energy.L2 (QuantumNLS.Energy.Mom k))
    (ρ : X →L[ℂ] X) (hρ : ρ.IsPositive) (hE : physTrace L k e ρ ≠ ⊤) :
    ∃ T : X →L[ℂ] X, T.IsPositive ∧ IsTraceClass T ∧
      ρ = physW L k e * T * physW L k e ∧ posTrace T = physTrace L k e ρ :=
  phys_realization hρ hE
end Energy
end QuantumNLS.Ext025STrace

#print axioms QuantumNLS.Ext025STrace.hs_product_bound
#print axioms QuantumNLS.Ext025STrace.hs_product_traceClass
#print axioms QuantumNLS.Ext025STrace.«FIN-EXT025-GP-09»
#print axioms QuantumNLS.Ext025STrace.positive_compression
#print axioms QuantumNLS.Ext025STrace.block_trace_hs
#print axioms QuantumNLS.Ext025STrace.gp09_cross_block
#print axioms QuantumNLS.Ext025STrace.positive_trace_basis
#print axioms QuantumNLS.Ext025STrace.gp09_pure_partial_trace
#print axioms QuantumNLS.Ext025STrace.gp09_pure_partial_trace_stability
#print axioms QuantumNLS.Ext025STrace.gp09_energy_sandwich

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025STrace." then
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
  Lean.logInfo m!"Ext025STrace audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
