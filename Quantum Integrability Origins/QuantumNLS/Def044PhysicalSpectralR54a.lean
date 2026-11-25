import QuantumNLS.ActualModelInterfacesR52a

/-! Physical realization of DEF-044 clause (1), at each fixed smooth unit
profile. The finite-sector transfer, charges and Born law use the same
actual Bethe basis. The scalar measure is the full-mass physical measure
and obeys D1 at every exterior noninteger-force cut. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
namespace QuantumNLS.Def044PhysicalSpectralR54a

open PhysicalTensor BetheLabels BetheCoefficientTransform BetheSpectralCharges
open Def044D1SpectralR51a
open Def044InterfacesR51a (Smooth physical)

variable {L κ : ℝ} [Fact (0 < L)]

/-- At the given physical profile, both spectral requirements are derived.
The quantum record has the exact eigenvalue, expansion and factorial bound.
The scalar record uses the original Born law for this profile and all positive
particle numbers, with a common threshold and fixed contour height. -/
def spectral (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    SpectralInterface hκ (physical u) hu :=
  ⟨ActualModelQuantumR52a.quantum_requirements hκ,
    Classical.choice (ActualModelInterfacesR52a.scalar_requirements hκ u hu)⟩

theorem measure_eq (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    (spectral hκ u hu).scalar.indexed.μ = PhysicalQuantumMeasure.measure hκ (physical u) :=
  (spectral hκ u hu).scalar.physical_measure

/-- The whole sector is resolved by the same orthonormal basis used by the
transfer, charges and original product law. -/
theorem complete_resolution (hκ : 0 < κ) (N : ℕ) :
    Function.Surjective (coefficientTransform (basis (L := L) hκ N)) :=
  full_resolution hκ N

/-- At every order, a vector of the common basis lies in the maximal
charge domain and has the power sum of the same real roots as eigenvalue. -/
theorem charge_eigenrelation (hκ : 0 < κ) (N r : ℕ) (m : MArr (N+1)) :
    ∃ hm : basis (L := L) hκ N m ∈ (charge (basis (L := L) hκ N) (κ/(N+1)) r).domain,
      charge (basis (L := L) hκ N) (κ/(N+1)) r ⟨basis (L := L) hκ N m, hm⟩ =
        ((∑ j, root (L := L) (κ := κ) N m j ^ r : ℝ) : ℂ) • basis (L := L) hκ N m := by
  let b := basis (L := L) hκ N
  let ev := eigenvalue L (N+1) (κ/(N+1)) r
  change ∃ hm : b m ∈ (multiplier b ev).domain,
    multiplier b ev ⟨b m, hm⟩ = (ev m : ℂ) • b m
  exact ⟨basis_mem_domain b ev m, multiplier_basis b ev m⟩

/-- Joint spectral commutation on the actual charge projections at every
order, including order zero. -/
theorem transfer_commutes_chargeProjection (hκ : 0 < κ) (N r : ℕ) (z : ℂ) (s : Set ℝ) :
    Commute (NormalizedTransfer.normalizedTransfer L κ (N+1) z)
      (BoundedBetheTransfer.chargeProjection L hκ (by omega : 0 < N+1) r s) :=
  BoundedBetheTransfer.commute_chargeProjection L hκ (by omega : 0 < N+1) z r s

/-- The cut quantifier ranges over the actual physical measure. Both D1
inequalities use the boundary function in the assembled spectral record. -/
theorem every_regular_cut (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (x : ℝ)
    (hx : D1Def043.regularCut L κ (PhysicalQuantumMeasure.measure hκ (physical u)) x) :
    let μ := PhysicalQuantumMeasure.measure hκ (physical u)
    let reG := (spectral hκ u hu).scalar.indexed.reG
    ∃! a : ℤ, (2*Real.pi*a < IndexedScalarMeasure.exteriorForce L κ μ x ∧
      IndexedScalarMeasure.exteriorForce L κ μ x < 2*Real.pi*(a+1)) ∧
      (∀ᵐ t ∂μ, t < x → IndexedScalarMeasure.indexLabel L κ reG t ≤ a) ∧
      (∀ᵐ t ∂μ, x < t → (a : ℝ)+1 ≤ IndexedScalarMeasure.indexLabel L κ reG t) := by
  have h := every_d1_cut (spectral hκ u hu).scalar x
  rw [measure_eq hκ u hu] at h
  exact h hx

/-- The multiplier lower bound in the record covers the boundary used in the
growing-window packet. The integrations on this boundary use the positive
orientation of `LabelExactPeriod.rectIntegral`. -/
theorem rectangle_eq_gamma (a h : ℝ) :
    rectangle a h = ResolventNeighborhood.GammaN a h := by
  simp only [rectangle, ResolventNeighborhood.GammaN, abs_le, or_comm]

end QuantumNLS.Def044PhysicalSpectralR54a

#print axioms QuantumNLS.Def044PhysicalSpectralR54a.spectral
#print axioms QuantumNLS.Def044PhysicalSpectralR54a.measure_eq
#print axioms QuantumNLS.Def044PhysicalSpectralR54a.complete_resolution
#print axioms QuantumNLS.Def044PhysicalSpectralR54a.charge_eigenrelation
#print axioms QuantumNLS.Def044PhysicalSpectralR54a.transfer_commutes_chargeProjection
#print axioms QuantumNLS.Def044PhysicalSpectralR54a.every_regular_cut
#print axioms QuantumNLS.Def044PhysicalSpectralR54a.rectangle_eq_gamma

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def044PhysicalSpectralR54a." ||
        n.toString.startsWith "_private.QuantumNLS.Def044PhysicalSpectralR54a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          (n.toString.splitOn "RegularCut").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"Round54 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
