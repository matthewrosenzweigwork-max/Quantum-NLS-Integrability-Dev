import QuantumNLS.EnergyProjection
import QuantumNLS.LinearTailSelfadjoint
import QuantumNLS.LinearTailSourceEstimates

/-! Literal exponential evolution for the actual finite-tail generator.
No physical derivative bound or energy-domain membership is postulated. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace
namespace QuantumNLS.LinearTailPhysicalEvolution
open TensorCarrier PhysicalTensor LinearTailGenerator LinearTailHamiltonian
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The usual bounded-generator unitary group, exp(-isA). -/
def evolution (A : H →L[ℂ] H) (s : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((s : ℂ) • ((-Complex.I) • A))

theorem evolution_zero (A : H →L[ℂ] H) : evolution A 0 = 1 := by
  simp [evolution]

theorem evolution_unitary {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (s : ℝ) :
    evolution A s ∈ unitary (H →L[ℂ] H) := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ (H →L[ℂ] H)
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star ((s : ℂ) • ((-Complex.I) • A)) = -((s : ℂ) • ((-Complex.I) • A))
  simp [star_smul, hA.star_eq]

theorem evolution_norm {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (s : ℝ) (ψ : H) :
    ‖evolution A s ψ‖ = ‖ψ‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (evolution_unitary hA s) ψ

/-- Actual vector differentiation, for every real time. -/
theorem hasDerivAt_evolution (A : H →L[ℂ] H) (ψ : H) (s : ℝ) :
    HasDerivAt (fun q : ℝ => evolution A q ψ)
      ((-Complex.I) • A (evolution A s ψ)) s := by
  have h := (hasDerivAt_exp_smul_const' ((-Complex.I) • A) (s : ℂ)).clm_apply
    (hasDerivAt_const (s : ℂ) ψ)
  have hr := h.complexToReal_fderiv'.comp_hasDerivAt s Complex.ofRealCLM.hasDerivAt
  simpa [evolution, mul_apply_eq_comp, Function.comp_def, Complex.real_smul] using hr

/-- A commuting bounded projection fixes the entire orbit whenever it
fixes the initial vector. This applies to the actual energy cutoff. -/
theorem evolution_fixed {P A : H →L[ℂ] H} (hPA : Commute P A)
    {ψ : H} (hψ : P ψ = ψ) (s : ℝ) : P (evolution A s ψ) = evolution A s ψ := by
  have hscalar (c : ℂ) : Commute P (c • A) := by
    change P * (c • A) = (c • A) * P
    apply ContinuousLinearMap.ext
    intro x
    change P (c • A x) = c • A (P x)
    rw [map_smul]
    exact congrArg (fun y => c • y) (congrArg (fun T : H →L[ℂ] H => T x) hPA.eq)
  have h := (hscalar ((s : ℂ) * (-Complex.I))).exp_right
  simp only [mul_smul] at h
  have hh := congrArg (fun T : H →L[ℂ] H => T ψ) h.eq
  simpa [evolution, mul_apply_eq_comp, hψ] using hh

/-- Differentiating an actual bounded observable along that orbit. -/
theorem hasDerivAt_expectation (A J : H →L[ℂ] H) (ψ : H) (s : ℝ) :
    HasDerivAt (fun q : ℝ => ⟪evolution A q ψ, J (evolution A q ψ)⟫_ℂ)
      (⟪(-Complex.I) • A (evolution A s ψ), J (evolution A s ψ)⟫_ℂ +
        ⟪evolution A s ψ, J ((-Complex.I) • A (evolution A s ψ))⟫_ℂ) s := by
  convert!
    (hasDerivAt_evolution A ψ s).inner ℂ
    ((J.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_evolution A ψ s)) using 1
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', add_comm]

/-- The actual expectation derivative is the commutator, with its sign
fixed by exp(-isA). The observable need not be selfadjoint. -/
theorem hasDerivAt_expectation_commutator {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)
    (J : H →L[ℂ] H) (ψ : H) (s : ℝ) :
    HasDerivAt (fun q : ℝ => ⟪evolution A q ψ, J (evolution A q ψ)⟫_ℂ)
      (Complex.I * ⟪evolution A s ψ, (A * J - J * A) (evolution A s ψ)⟫_ℂ) s := by
  apply (hasDerivAt_expectation A J ψ s).congr_deriv
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA)
    (evolution A s ψ) (J (evolution A s ψ))
  change ⟪A (evolution A s ψ), J (evolution A s ψ)⟫_ℂ =
    ⟪evolution A s ψ, A (J (evolution A s ψ))⟫_ℂ at hs
  simp only [inner_smul_left, map_smul, inner_smul_right, map_neg, Complex.conj_I,
    neg_neg, sub_apply, mul_apply_eq_comp, inner_sub_right, hs]
  ring

variable (L : ℝ) [Fact (0 < L)]

/-- Selfadjointness on the actual position-space symmetric realization. -/
theorem symGen_selfadjoint (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ) :
    IsSelfAdjoint (symGen L κ N a t) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  obtain ⟨v, rfl⟩ := (BethePhysicalTransfer.symmetricPosition L N).surjective x
  obtain ⟨w, rfl⟩ := (BethePhysicalTransfer.symmetricPosition L N).surjective y
  change ⟪symGen L κ N a t (BethePhysicalTransfer.symmetricPosition L N v),
    BethePhysicalTransfer.symmetricPosition L N w⟫_ℂ =
      ⟪BethePhysicalTransfer.symmetricPosition L N v,
        symGen L κ N a t (BethePhysicalTransfer.symmetricPosition L N w)⟫_ℂ
  rw [symGen_sp, symGen_sp, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  have h : IsSelfAdjoint (genSum L κ N a t) := by
    simpa only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using
      LinearTailSelfadjoint.genSum_selfadjoint L κ N a t
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h) v w

/-- Literal evolution under N L_N(t) on SymL2. -/
def physicalEvolution (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ) (s : ℝ) :
    ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N :=
  evolution ((N : ℂ) • symGen L κ N a t) s

theorem physicalEvolution_norm (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (s : ℝ) (ψ : ContactOperator.SymL2 L N) :
    ‖physicalEvolution L κ N a t s ψ‖ = ‖ψ‖ :=
  evolution_norm ((show IsSelfAdjoint (N : ℂ) from by simp [isSelfAdjoint_iff]).smul
    (symGen_selfadjoint L κ N a t)) s ψ

/-- The literal physical vector orbit has the expected Schrodinger derivative. -/
theorem physicalEvolution_hasDerivAt (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (ψ : ContactOperator.SymL2 L N) (s : ℝ) :
    HasDerivAt (fun q : ℝ => physicalEvolution L κ N a t q ψ)
      ((-Complex.I) • ((N : ℂ) • symGen L κ N a t) (physicalEvolution L κ N a t s ψ)) s :=
  hasDerivAt_evolution _ ψ s

/-- Every actual bounded observable has this physical commutator derivative. -/
theorem physicalExpectation_hasDerivAt (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (J : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N)
    (ψ : ContactOperator.SymL2 L N) (s : ℝ) :
    HasDerivAt (fun q : ℝ => ⟪physicalEvolution L κ N a t q ψ, J (physicalEvolution L κ N a t q ψ)⟫_ℂ)
      (Complex.I * ⟪physicalEvolution L κ N a t s ψ,
        (((N : ℂ) • symGen L κ N a t) * J - J * ((N : ℂ) • symGen L κ N a t))
          (physicalEvolution L κ N a t s ψ)⟫_ℂ) s :=
  hasDerivAt_expectation_commutator
    ((show IsSelfAdjoint (N : ℂ) from by simp [isSelfAdjoint_iff]).smul
      (symGen_selfadjoint L κ N a t)) J ψ s

/-- The actual spectral energy projection supplied by energy_projection
fixes the literal exponential orbit. No evolution-invariance premise. -/
theorem physicalEvolution_cutoff (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (E : ℝ) (a : Finset ℤ) (t : ℤ → ℝ) :
    ∃ P : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N,
      (∀ n : BetheFreeFamily.Label N,
        P (BetheConditionalBasis.normalizedWave L N
          ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) =
          ((if EnergyProjection.energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) •
            BetheConditionalBasis.normalizedWave L N
              ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) ∧
      P * P = P ∧ ContinuousLinearMap.adjoint P = P ∧
      ∀ ψ, P ψ = ψ → ∀ s : ℝ,
        P (physicalEvolution L κ N a t s ψ) = physicalEvolution L κ N a t s ψ := by
  obtain ⟨P, hdiag, hPP, hsa, _, hcomm⟩ := EnergyProjection.energy_projection L κ hκ N hN E a t
  have hNcomm : Commute P ((N : ℂ) • symGen L κ N a t) := by
    change P * ((N : ℂ) • symGen L κ N a t) = ((N : ℂ) • symGen L κ N a t) * P
    apply ContinuousLinearMap.ext
    intro x
    change P ((N : ℂ) • symGen L κ N a t x) = (N : ℂ) • symGen L κ N a t (P x)
    rw [map_smul]
    exact congrArg (fun y => (N : ℂ) • y) (congrArg (fun T : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N => T x) hcomm.eq)
  exact ⟨P, hdiag, hPP, hsa, fun ψ hψ s => evolution_fixed hNcomm hψ s⟩

end QuantumNLS.LinearTailPhysicalEvolution

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.LinearTailPhysicalEvolution.evolution
#print axioms QuantumNLS.LinearTailPhysicalEvolution.evolution_zero
#print axioms QuantumNLS.LinearTailPhysicalEvolution.evolution_unitary
#print axioms QuantumNLS.LinearTailPhysicalEvolution.evolution_norm
#print axioms QuantumNLS.LinearTailPhysicalEvolution.hasDerivAt_evolution
#print axioms QuantumNLS.LinearTailPhysicalEvolution.evolution_fixed
#print axioms QuantumNLS.LinearTailPhysicalEvolution.hasDerivAt_expectation
#print axioms QuantumNLS.LinearTailPhysicalEvolution.hasDerivAt_expectation_commutator
#print axioms QuantumNLS.LinearTailPhysicalEvolution.symGen_selfadjoint
#print axioms QuantumNLS.LinearTailPhysicalEvolution.physicalEvolution
#print axioms QuantumNLS.LinearTailPhysicalEvolution.physicalEvolution_norm
#print axioms QuantumNLS.LinearTailPhysicalEvolution.physicalEvolution_hasDerivAt
#print axioms QuantumNLS.LinearTailPhysicalEvolution.physicalExpectation_hasDerivAt
#print axioms QuantumNLS.LinearTailPhysicalEvolution.physicalEvolution_cutoff

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.LinearTailPhysicalEvolution." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
