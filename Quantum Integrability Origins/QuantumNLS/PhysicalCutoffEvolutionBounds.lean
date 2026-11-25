import QuantumNLS.PhysicalCutoffFormDomain
import QuantumNLS.PhysicalMarginalCompactness

/-! Actual cutoff evolution stays in the physical form domain, with the
literal energy bound and canonical marginal quadratic-error control. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology
namespace QuantumNLS.PhysicalCutoffEvolutionBounds
open ContactOperator LinearTailPhysicalEvolution PhysicalTensor TensorCarrier EnergyPreparationDef
variable (L : ℝ) [Fact (0 < L)]

def IsEnergyCutoff (κ : ℝ) (N : ℕ) (hκ : 0 < κ) (hN : 1 ≤ N) (E : ℝ)
    (P : SymL2 L N →L[ℂ] SymL2 L N) : Prop :=
  ∀ n : BetheFreeFamily.Label N,
    P (BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ),
        (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) =
      ((if EnergyProjection.energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) •
        BetheConditionalBasis.normalizedWave L N ⟨κ / (N : ℝ),
          (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n

/-- Every actual cutoff orbit has its physical H1 representative and source energy bound. -/
theorem cutoff_orbit_form_bound (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (E : ℝ) (hE : 0 ≤ E) (a : Finset ℤ) (t : ℤ → ℝ) :
    ∃ P : SymL2 L N →L[ℂ] SymL2 L N,
      IsEnergyCutoff L κ N hκ hN E P ∧ P * P = P ∧ P.adjoint = P ∧
      ∀ ψ : SymL2 L N, P ψ = ψ → ∀ s : ℝ,
        ∃ v : VSym L N, valSym v = physicalEvolution L κ N a t s ψ ∧
          (ContactForm.q (κ / (N : ℝ)) v.1 v.1).re ≤ (N : ℝ) * E * ‖ψ‖ ^ 2 := by
  obtain ⟨P, hdiag, hPP, hsa, hinv⟩ := physicalEvolution_cutoff L κ hκ N hN E a t
  refine ⟨P, hdiag, hPP, hsa, fun ψ hψ s => ?_⟩
  obtain ⟨v, hv, he⟩ := PhysicalCutoffFormDomain.cutoff_form_bound L κ hκ N hN E hE
    P hdiag (physicalEvolution L κ N a t s ψ) (hinv ψ hψ s)
  exact ⟨v, hv, by simpa only [physicalEvolution_norm] using he⟩

/-- The literal full physical tensor orbit, via the frozen symmetric-position isometry. -/
def tensorOrbit (κ : ℝ) (N : ℕ) (a : Finset ℤ) (t : ℤ → ℝ) (s : ℝ)
    (ψ : SymL2 L N) : Xk L N :=
  ((BethePhysicalTransfer.symmetricPosition L N).symm (physicalEvolution L κ N a t s ψ)).val

/-- The constructed sourceError controls every actual normalized energy-cutoff orbit marginal.
No H1 or form-energy assumptions occur on the evolving vector. -/
theorem cutoff_marginal_quadratic_error (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (E : ℝ) (hE : 0 ≤ E) (a : Finset ℤ) (t : ℤ → ℝ) :
    ∃ P : SymL2 L N →L[ℂ] SymL2 L N, IsEnergyCutoff L κ N hκ hN E P ∧
      ∀ ψ : SymL2 L N, P ψ = ψ → ‖ψ‖ = 1 → ∀ s : ℝ,
      ∀ (n : ℕ) (hn : n + 1 ≤ N) (R : ℕ) (b : Finset ℤ) (v : ℤ → ℝ),
      (∀ m ∈ b, |v m| ≤ 1) → (∀ m ∈ b, (R : ℤ) < |m|) →
      LinearTailKineticError.quadraticError (LinearTailKineticError.fullT L n b v)
        (reducedDensityN N (n + 1) hn (tensorOrbit L κ N a t s ψ)) ≤
          LinearTailKineticError.sourceError L n E R := by
  obtain ⟨P, hdiag, _, _, horbit⟩ := cutoff_orbit_form_bound L κ hκ N hN E hE a t
  refine ⟨P, hdiag, fun ψ hψ hnorm s n hn R b v hv hb => ?_⟩
  obtain ⟨x, hx, he⟩ := horbit ψ hψ s
  have hsec : tensorOrbit L κ N a t s ψ ∈ physSector L N :=
    ((BethePhysicalTransfer.symmetricPosition L N).symm (physicalEvolution L κ N a t s ψ)).property
  have hnorm' : ‖tensorOrbit L κ N a t s ψ‖ = 1 := by
    change ‖(BethePhysicalTransfer.symmetricPosition L N).symm (physicalEvolution L κ N a t s ψ)‖ = 1
    rw [LinearIsometryEquiv.norm_map, physicalEvolution_norm, hnorm]
  have hpos : physUnitary (tensorOrbit L κ N a t s ψ) =
      (physicalEvolution L κ N a t s ψ).val := by
    change physUnitary (physUnitary.symm _) = _
    exact LinearIsometryEquiv.apply_symm_apply _ _
  have hx' : x.val.val = physUnitary (tensorOrbit L κ N a t s ψ) := by
    rw [hpos]
    exact congrArg Subtype.val hx
  have he' : EnergyPreparationDef.hN κ N x.val ≤ (N : ℝ) * E := by
    simpa [EnergyPreparationDef.hN, ProductEnergyPreparation.hN, hnorm] using he
  exact PhysicalMarginalCompactness.marginal_quadratic_error L hn hκ.le hsec hnorm' x.val hx' he' R b v hv hb

end QuantumNLS.PhysicalCutoffEvolutionBounds

#print axioms QuantumNLS.PhysicalCutoffEvolutionBounds.IsEnergyCutoff
#print axioms QuantumNLS.PhysicalCutoffEvolutionBounds.cutoff_orbit_form_bound
#print axioms QuantumNLS.PhysicalCutoffEvolutionBounds.tensorOrbit
#print axioms QuantumNLS.PhysicalCutoffEvolutionBounds.cutoff_marginal_quadratic_error

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.PhysicalCutoffEvolutionBounds." then
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
