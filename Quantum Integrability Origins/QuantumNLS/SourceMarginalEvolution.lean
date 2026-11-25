import QuantumNLS.SourceGeneratorBound
import QuantumNLS.MixedTraceNorm
import QuantumNLS.MarginalPureState

/-! Actual physical cutoff-orbit derivative, time integration, and marginal duality. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Filter Topology Set
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.SourceMarginalEvolution
open TensorCarrier PhysicalTensor KernelDefinition LinearTailGenerator LinearTailHamiltonian
open LinearTailPhysicalEvolution PhysicalCutoffEvolutionBounds SourceGeneratorBound
variable (L : ℝ) [Fact (0 < L)]

/-- The diagonal specification identifies one and the same physical cutoff,
independently of which finite tail was used to construct it. -/
theorem cutoff_unique (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (E : ℝ)
    {P Q : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N}
    (hP : IsEnergyCutoff L κ N hκ hN E P) (hQ : IsEnergyCutoff L κ N hκ hN E Q) : P = Q := by
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast (show 0 < N by omega))
  obtain ⟨-, -, -, -, -, ho, hd, -⟩ := UnconditionalBetheBasis.basis L N hN (κ / (N : ℝ)) hc
  let B := HilbertBasis.mk ho hd.ge
  apply TransferNormality.ext_of_hilbertBasis B
  intro n
  have hB : B n = BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n :=
    congrFun (HilbertBasis.coe_mk ho hd.ge) n
  rw [hB, hP n, hQ n]

/-- The literal orbit, retaining the symmetric-sector codomain. -/
def sectorOrbit (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ) (s : ℝ)
    (ψ : ContactOperator.SymL2 L N) : SymSector ℂ (L2T L) N :=
  (BethePhysicalTransfer.symmetricPosition L N).symm (physicalEvolution L κ N a t s ψ)

theorem sectorOrbit_norm (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ) (s : ℝ)
    (ψ : ContactOperator.SymL2 L N) : ‖sectorOrbit L κ N a t s ψ‖ = ‖ψ‖ := by
  rw [sectorOrbit, LinearIsometryEquiv.norm_map, physicalEvolution_norm]

theorem sectorOrbit_zero (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (ψ : ContactOperator.SymL2 L N) :
    sectorOrbit L κ N a t 0 ψ = (BethePhysicalTransfer.symmetricPosition L N).symm ψ := by
  simp [sectorOrbit, physicalEvolution, evolution_zero]

/-- Differentiation on the actual symmetric tensor carrier. -/
theorem sectorOrbit_derivative (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (ψ : ContactOperator.SymL2 L N) (s : ℝ) :
    HasDerivAt (fun q => sectorOrbit L κ N a t q ψ)
      ((-Complex.I) • ((N : ℂ) • genSum L κ N a t) (sectorOrbit L κ N a t s ψ)) s := by
  let e := BethePhysicalTransfer.symmetricPosition L N
  have h := (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
    (physicalEvolution_hasDerivAt L κ N a t ψ s)
  have hc (x : ContactOperator.SymL2 L N) : e.symm (symGen L κ N a t x) = genSum L κ N a t (e.symm x) := by
    have hh := symGen_sp L κ N a t (e.symm x)
    rw [e.apply_symm_apply] at hh
    rw [hh, e.symm_apply_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars',
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    map_smul, smul_apply, hc] at h
  convert! h using 1


/-- The actual differentiated observable is its N-scaled commutator. -/
theorem expectation_derivative (κ : ℝ) (N k : ℕ) (hk : k ≤ N)
    (a : Finset ℤ) (t : ℤ → ℝ) (J : BoundedSymmetricKernel (L2T L) k)
    (ψ : ContactOperator.SymL2 L N) (s : ℝ) :
    HasDerivAt (fun q => ⟪sectorOrbit L κ N a t q ψ,
      genericU_N_r N k hk J (sectorOrbit L κ N a t q ψ)⟫_ℂ)
      (Complex.I * ⟪sectorOrbit L κ N a t s ψ,
        (((N : ℂ) • genSum L κ N a t) * genericU_N_r N k hk J -
          genericU_N_r N k hk J * ((N : ℂ) • genSum L κ N a t))
          (sectorOrbit L κ N a t s ψ)⟫_ℂ) s := by
  let A := ((N : ℂ) • genSum L κ N a t)
  let K := genericU_N_r N k hk J
  let v := sectorOrbit L κ N a t s ψ
  have hv := sectorOrbit_derivative L κ N a t ψ s
  have h := hv.inner ℂ ((K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hv)
  apply h.congr_deriv
  have ha : IsSelfAdjoint A :=
    (show IsSelfAdjoint (N : ℂ) from by simp [isSelfAdjoint_iff]).smul
      (show IsSelfAdjoint (genSum L κ N a t) from by
        simpa only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using
          LinearTailSelfadjoint.genSum_selfadjoint L κ N a t)
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha) v (K v)
  change ⟪A v, K v⟫_ℂ = ⟪v, A (K v)⟫_ℂ at hs
  simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    inner_smul_left, map_smul, inner_smul_right, map_neg, Complex.conj_I, neg_neg,
    sub_apply, mul_apply_eq_comp, inner_sub_right]
  change -Complex.I * ⟪v, K (A v)⟫_ℂ + Complex.I * ⟪A v, K v⟫_ℂ =
    Complex.I * (⟪v, A (K v)⟫_ℂ - ⟪v, K (A v)⟫_ℂ)
  rw [hs]
  ring

/-- Observable time integration on either side of zero. -/
theorem integrated_expectation (κ : ℝ) (hκ : 0 < κ) (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (P : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N)
    (hP : IsEnergyCutoff L κ N hκ hN E P)
    (ψ : ContactOperator.SymL2 L N) (hψ : P ψ = ψ) (hnorm : ‖ψ‖ = 1)
    (R : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (ht : ∀ m ∈ a, |t m| ≤ 1) (ha : ∀ m ∈ a, (R : ℤ) < |m|)
    (J : BoundedSymmetricKernel (L2T L) k) (hJ : ‖J‖ ≤ 1) (s : ℝ) (hs : |s| ≤ 1) :
    ‖⟪sectorOrbit L κ N a t s ψ, genericU_N_r N k hk J (sectorOrbit L κ N a t s ψ)⟫_ℂ -
      ⟪sectorOrbit L κ N a t 0 ψ, genericU_N_r N k hk J (sectorOrbit L κ N a t 0 ψ)⟫_ℂ‖ ≤
        epsilon L κ E k R := by
  obtain ⟨Q, hQ, herror⟩ := PhysicalPlacementError.cutoff_placement_error L κ hκ N hN E hE a t
  have hPQ := cutoff_unique L κ hκ N hN E hP hQ
  subst Q
  let F := fun q => ⟪sectorOrbit L κ N a t q ψ,
    genericU_N_r N k hk J (sectorOrbit L κ N a t q ψ)⟫_ℂ
  have hd (q : ℝ) : ‖deriv F q‖ ≤ epsilon L κ E k R := by
    rw [(expectation_derivative L κ N k hk a t J ψ q).deriv]
    rw [norm_mul, Complex.norm_I, one_mul]
    exact generator_bound L κ hκ N k hN hk E hE R a t J hJ
      (sectorOrbit L κ N a t q ψ) (by rw [sectorOrbit_norm, hnorm])
      (fun n hn S => herror ψ hψ hnorm q n hn R a t ht ha S)
  have hi := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun q (_ : q ∈ Icc (-1 : ℝ) 1) => (expectation_derivative L κ N k hk a t J ψ q).differentiableAt)
    (fun q (_ : q ∈ Icc (-1 : ℝ) 1) => hd q) (convex_Icc (-1 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, by norm_num⟩) (abs_le.mp hs)
  refine hi.trans ?_
  apply mul_le_of_le_one_right (epsilon_nonneg L hκ.le E k R)
  simpa only [sub_zero, Real.norm_eq_abs] using hs

/-- Duality on the actual arbitrary-N reduced density; the equality casts
are eliminated before applying the frozen general symmetric-state theorem. -/
theorem marginal_duality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N k : ℕ) (hk : k ≤ N) (v w : SymSector ℂ H N) {c : ℝ}
    (h : ∀ J : BoundedSymmetricKernel H k, ‖J‖ ≤ 1 →
      ‖⟪v, genericU_N_r N k hk J v⟫_ℂ - ⟪w, genericU_N_r N k hk J w⟫_ℂ‖ ≤ c) :
    TraceClass.traceNorm (reducedDensityN N k hk v.val - reducedDensityN N k hk w.val) ≤ ENNReal.ofReal c := by
  let cs : ∀ {m n : ℕ}, m = n → SymSector ℂ H m ≃ₗᵢ[ℂ] SymSector ℂ H n :=
    fun {_ _} h => by cases h; exact LinearIsometryEquiv.refl ℂ _
  have hi {m n : ℕ} (he : m = n) (A : BoundedSymmetricKernel H m)
      (x : SymSector ℂ H n) :
      ⟪x, castSymSectorOperator he A x⟫_ℂ =
        ⟪cs he.symm x, A (cs he.symm x)⟫_ℂ := by
    cases he
    rfl
  have hv {m n : ℕ} (he : m = n) (x : SymSector ℂ H m) :
      (cs he x).val = castHTP he x.val := by
    cases he
    rfl
  let he := Nat.add_sub_of_le hk
  have hd := MixedTraceNorm.traceNorm_reducedDensityPower_sub_le k (N - k)
    (cs he.symm v) (cs he.symm w) (by
      intro J hJ
      have hh := h J hJ
      simp only [genericU_N_r, hi] at hh
      exact hh)
  simpa only [hv, reducedDensityN] using hd


/-- The uniform source-route reduced-marginal estimate, for any operator
with the actual energy-cutoff diagonal specification. -/
theorem physical_marginal_bound (κ : ℝ) (hκ : 0 < κ) (N k : ℕ) (hN : 1 ≤ N) (hk : k ≤ N)
    (E : ℝ) (hE : 0 ≤ E)
    (P : ContactOperator.SymL2 L N →L[ℂ] ContactOperator.SymL2 L N)
    (hP : IsEnergyCutoff L κ N hκ hN E P)
    (ψ : ContactOperator.SymL2 L N) (hψ : P ψ = ψ) (hnorm : ‖ψ‖ = 1)
    (R : ℕ) (a : Finset ℤ) (t : ℤ → ℝ)
    (ht : ∀ m ∈ a, |t m| ≤ 1) (ha : ∀ m ∈ a, (R : ℤ) < |m|)
    (s : ℝ) (hs : |s| ≤ 1) :
    TraceClass.traceNorm (reducedDensityN N k hk (tensorOrbit L κ N a t s ψ) -
      reducedDensityN N k hk ((BethePhysicalTransfer.symmetricPosition L N).symm ψ).val) ≤
        ENNReal.ofReal (epsilon L κ E k R) := by
  have h := marginal_duality N k hk (sectorOrbit L κ N a t s ψ) (sectorOrbit L κ N a t 0 ψ)
    (fun J hJ => integrated_expectation L κ hκ N k hN hk E hE P hP ψ hψ hnorm R a t ht ha J hJ s hs)
  rw [sectorOrbit_zero] at h
  exact h

end QuantumNLS.SourceMarginalEvolution

-- AUTHOR AUDITS
#print axioms QuantumNLS.SourceMarginalEvolution.cutoff_unique
#print axioms QuantumNLS.SourceMarginalEvolution.sectorOrbit
#print axioms QuantumNLS.SourceMarginalEvolution.sectorOrbit_norm
#print axioms QuantumNLS.SourceMarginalEvolution.sectorOrbit_zero
#print axioms QuantumNLS.SourceMarginalEvolution.sectorOrbit_derivative
#print axioms QuantumNLS.SourceMarginalEvolution.expectation_derivative
#print axioms QuantumNLS.SourceMarginalEvolution.integrated_expectation
#print axioms QuantumNLS.SourceMarginalEvolution.marginal_duality
#print axioms QuantumNLS.SourceMarginalEvolution.physical_marginal_bound

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SourceMarginalEvolution." then
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
