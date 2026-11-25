import QuantumNLS.EnergyFormPass
import QuantumNLS.Ext025B11TraceBasis

/-! R-C17D95AA physical consumer interface: basis-independent complex
expectation, independence of the chosen form realization, and the standard
uniform-convergence topology. The source's arbitrary-A extension is separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.EnergyFormPassFinal
open EnergyPreparationDef Ext025B10PhysicalEnergy Ext025B10EnergyFamily
open Ext025B11TracePairing Ext025B11TraceBasis EnergyFormPass
variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- No preferred-basis convention is part of the physical form expectation. -/
theorem expectation_basis {ι : Type*} (b : HilbertBasis ι ℂ (Xk L k))
    (K : Xk L k →L[ℂ] Xk L k) (ρ : FiniteEnergy L k) :
    expectation K ρ = trace b (K*sandwich ρ) :=
  pairing_basis_independent (basis L k) b K (sandwich ρ)
    (sandwich_spec ρ).1 (sandwich_spec ρ).2.1

/-- The source's positive trace-class form realization can be used directly;
the expectation does not depend on the choice made in its construction. -/
theorem expectation_realization (K : Xk L k →L[ℂ] Xk L k) (ρ : FiniteEnergy L k)
    (S : Xk L k →L[ℂ] Xk L k) (hS : IsFormRealization ρ.val S) :
    expectation K ρ = trace (basis L k) (K*S) := by
  have he : sandwich ρ = S := formRealization_unique (sandwich_spec ρ).2.2.1 hS
  simp only [expectation,he]

/-- Any source form with kinetic sandwich K equals the represented form on
its full physical form domain, since W is the inverse of the physical root. -/
theorem form_unique (K : Xk L k →L[ℂ] Xk L k)
    (C : (AhalfT L k).domain → (AhalfT L k).domain → ℂ)
    (hC : ∀ x y, C ⟨W L k x,W_mem x⟩ ⟨W L k y,W_mem y⟩ = ⟪x,K y⟫_ℂ)
    (f g : (AhalfT L k).domain) : C f g = form K f g := by
  have hf : (⟨W L k (AhalfT L k f),W_mem _⟩ : (AhalfT L k).domain) = f :=
    Subtype.ext (W_AhalfT f)
  have hg : (⟨W L k (AhalfT L k g),W_mem _⟩ : (AhalfT L k).domain) = g :=
    Subtype.ext (W_AhalfT g)
  have h := hC (AhalfT L k f) (AhalfT L k g)
  rw [hf,hg] at h
  exact h

/-- Physical A_k version of the entire compact-form passage, including
non-Hermitian forms, as convergence in the uniform topology. -/
theorem R_C17D95AA_physical {T : Type*}
    (ρ : ℕ → T → FiniteEnergy L k) (σ : T → FiniteEnergy L k)
    (B : ℝ) (hB : 0 ≤ B)
    (hρ : ∀ n t, energyTrace (ρ n t).val ≤ ENNReal.ofReal B)
    (hσ : ∀ t, energyTrace (σ t).val ≤ ENNReal.ofReal B)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t,
      TraceClass.traceNorm ((ρ n t).val-(σ t).val) ≤ ENNReal.ofReal δ)
    (K : Xk L k →L[ℂ] Xk L k) (hK : IsCompactOperator K) :
    TendstoUniformly (fun n t => expectation K (ρ n t))
      (fun t => expectation K (σ t)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [EnergyFormPass.R_C17D95AA_physical ρ σ B hB hρ hσ hconv K hK
    (ε/2) (half_pos hε)] with n hn
  intro t
  rw [dist_eq_norm,norm_sub_rev]
  exact (hn t).trans_lt (half_lt_self hε)
end QuantumNLS.EnergyFormPassFinal

#print axioms QuantumNLS.EnergyFormPassFinal.R_C17D95AA_physical
#print axioms QuantumNLS.EnergyFormPassFinal.expectation_basis
#print axioms QuantumNLS.EnergyFormPassFinal.expectation_realization
#print axioms QuantumNLS.EnergyFormPassFinal.form_unique
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.EnergyFormPassFinal" then
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
  Lean.logInfo m!"EnergyFormPassFinal audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
