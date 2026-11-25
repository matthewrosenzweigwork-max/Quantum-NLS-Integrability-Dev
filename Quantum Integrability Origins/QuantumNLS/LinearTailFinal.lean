import QuantumNLS.SourceMarginalEvolution

/-! R-36C23346, all clauses in one theorem, for the actual source generator.
The cutoff is specified by the actual Bethe spectral diagonal in positive
sectors and by the identity in the vacuum sector. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
open Filter Topology
open scoped InnerProductSpace BigOperators
namespace QuantumNLS.LinearTailFinal
open TensorCarrier PhysicalTensor KernelDefinition ContactOperator
open LinearTailGenerator LinearTailHamiltonian LinearTailPhysicalEvolution
open PhysicalCutoffEvolutionBounds SourceGeneratorBound SourceMarginalEvolution
/-- The zero bounded generator has identity evolution at every time. -/
theorem zero_generator_evolution {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) (s : ℝ) :
    evolution ((0 : ℂ) • A) s = 1 := by
  simp [evolution]

variable (L : ℝ) [Fact (0 < L)]

/-- Actual spectral cutoff, with its vacuum convention made explicit. -/
def EnergyCutoff (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (E : ℝ)
    (P : SymL2 L N →L[ℂ] SymL2 L N) : Prop :=
  (N = 0 → P = 1) ∧ ∀ hN : 1 ≤ N, IsEnergyCutoff L κ N hκ hN E P

/-- The source lemma as one theorem: exact generator identity, bounded
selfadjointness, actual Hamiltonian and corrected-count commutation, and
uniform reduced-marginal convergence of exp(-is N L_N(t)). -/
theorem «R-36C23346» (κ : ℝ) (hκ : 0 < κ) :
    (∀ (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ),
      genSum L κ N a t =
        ∑ j : Fin N, (((1 / L) * κ ^ j.val * HighMomentsRank.fallR N (j.val + 1) : ℝ) : ℂ) •
          genericU_N_r N (j.val + 1) j.2 (finiteT L (j.val + 1) a t) ∧
      IsSelfAdjoint (genSum L κ N a t)) ∧
    (∀ (N : ℕ) (hN : 1 ≤ N) (a : Finset ℤ) (t : ℤ → ℝ),
      (∀ (ψ : SymL2 L N) (hψ : ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
          (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain),
        ∃ h : symGen L κ N a t ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
            (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain,
          Hop (L := L) (N := N) (κ / (N : ℝ))
              (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le ⟨symGen L κ N a t ψ, h⟩ =
            symGen L κ N a t (Hop (L := L) (N := N) (κ / (N : ℝ))
              (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le ⟨ψ, hψ⟩)) ∧
      (∀ (g : BetheOccupationGauge.Gauge) (j : ℤ),
        Commute (genSum L κ N a t)
          (CartesianOccupationTransfer.physical
            (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) g j j))) ∧
    (∀ (E : ℝ), 0 ≤ E → ∀ k : ℕ,
      ∃ ε : ℕ → ℝ, (∀ R, 0 ≤ ε R) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ (N : ℕ) (hk : k ≤ N), ∃ P : SymL2 L N →L[ℂ] SymL2 L N,
          EnergyCutoff L κ hκ N E P ∧ P * P = P ∧ P.adjoint = P ∧
          ∀ (ψ : SymL2 L N), P ψ = ψ → ‖ψ‖ = 1 →
          ∀ (R : ℕ) (a : Finset ℤ) (t : ℤ → ℝ),
            (∀ m ∈ a, |t m| ≤ 1) → (∀ m ∈ a, (R : ℤ) < |m|) →
          ∀ (s : ℝ), |s| ≤ 1 →
            TraceClass.traceNorm (reducedDensityN N k hk (tensorOrbit L κ N a t s ψ) -
              reducedDensityN N k hk ((BethePhysicalTransfer.symmetricPosition L N).symm ψ).val) ≤
                ENNReal.ofReal (ε R)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N a t
    refine ⟨generator_identity L κ hκ N a t, ?_⟩
    simpa only [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] using
      LinearTailSelfadjoint.genSum_selfadjoint L κ N a t
  · intro N hN a t
    exact ⟨genSum_commutes_contactHamiltonian L κ hκ N hN a t,
      fun g j => LinearTailCommute.genSum_commutes_correctedCount L κ hκ N hN a t g j⟩
  · intro E hE k
    refine ⟨epsilon L κ E k, epsilon_nonneg L hκ.le E k, epsilon_tendsto L hκ.le hE k, ?_⟩
    intro N hk
    by_cases hN : 1 ≤ N
    · obtain ⟨P, hP, hPP, hsa, -, -⟩ := EnergyProjection.energy_projection L κ hκ N hN E ∅ (fun _ => 0)
      refine ⟨P, ⟨fun h0 => by omega, fun _ => hP⟩, hPP, hsa, ?_⟩
      intro ψ hψ hnorm R a t ht ha s hs
      exact physical_marginal_bound L κ hκ N k hN hk E hE P hP ψ hψ hnorm R a t ht ha s hs
    · have hn : N = 0 := by omega
      subst N
      refine ⟨1, ⟨fun _ => rfl, fun h => by omega⟩, one_mul _, ?_, ?_⟩
      · exact ContinuousLinearMap.adjoint_one
      · intro ψ _ _ R a t _ _ s _
        have he : tensorOrbit L κ 0 a t s ψ = ((BethePhysicalTransfer.symmetricPosition L 0).symm ψ).val := by
          have hu : physicalEvolution L κ 0 a t s = 1 := by
            unfold physicalEvolution
            convert! zero_generator_evolution (symGen L κ 0 a t) s using 1
            norm_num
            congr 1
            apply ContinuousLinearMap.ext
            intro x
            apply Subtype.ext
            change (0 : ℂ) • (symGen L κ 0 a t x).val = 0
            exact zero_smul ℂ ((symGen L κ 0 a t x).val)
          simp only [tensorOrbit, hu, one_apply_eq_self]

        rw [he]
        refine (MarginalPureState.traceNorm_reducedDensityN_sub_le 0 k hk
          ((BethePhysicalTransfer.symmetricPosition L 0).symm ψ).val
          ((BethePhysicalTransfer.symmetricPosition L 0).symm ψ).val).trans ?_
        simp only [sub_self, norm_zero, zero_mul, ENNReal.ofReal_zero]
        exact bot_le


end QuantumNLS.LinearTailFinal

#print axioms QuantumNLS.LinearTailFinal.zero_generator_evolution
#print axioms QuantumNLS.LinearTailFinal.EnergyCutoff
#print axioms QuantumNLS.LinearTailFinal.«R-36C23346»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.LinearTailFinal." then
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
