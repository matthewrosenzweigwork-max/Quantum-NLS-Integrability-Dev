import QuantumNLS.IndexedMassProperness
import QuantumNLS.ResetNormalizationBinding

/-! DEF-020, def:report-20. A specification on candidate maps only.
The DEF-014 measures/phases are the explicit parametric IndexedMassData.
No candidate, inverse, or symplectic property is supplied by this definition.
The derivative is real Frechet differentiation, with the orthonormal complex
Fourier coefficient isometry restricted to real scalars. -/
noncomputable section
set_option autoImplicit false
namespace QuantumNLS.QuantumFourierSpecification
open MeasureTheory QuantumNLS.Fourier IndexedMassProperness ResetNormalizationUniqueness
open scoped ComplexConjugate
variable {L κ : ℝ} [Fact (0 < L)]

abbrev PhysicalField (L : ℝ) [Fact (0 < L)] : Type := Lp ℂ 2 (volume : Measure (AddCircle L))
abbrev Coordinates := lp (fun _ : ℤ => ℂ) 2

/-- Exactly the realized DEF-001/U1 orthonormal Fourier differential. -/
def differential (L : ℝ) [Fact (0 < L)] : PhysicalField L →L[ℝ] Coordinates :=
  (fourierL2 L).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

theorem differential_apply (u : PhysicalField L) (n : ℤ) :
    differential L u n = coeff L (u : AddCircle L → ℂ) n := fourierL2_apply L u n

/-- Literal DEF-020 specification; existence is a subsequent theorem obligation. -/
def Specification (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates) : Prop :=
  HasFDerivAt w (differential L) 0 ∧
  (∀ u, w (Cphys L u) = star (w u)) ∧
  (∀ u n, ‖w u n‖ ^ 2 = D.seq u n)

theorem specification_iff (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates) :
    Specification D w ↔ HasFDerivAt w (differential L) 0 ∧
      (∀ u, w (Cphys L u) = star (w u)) ∧
      (∀ u n, ‖w u n‖ ^ 2 = D.seq u n) := Iff.rfl

theorem derivative_eq (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (h : Specification D w) : fderiv ℝ w 0 = differential L := h.1.fderiv

theorem exact_action (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (h : Specification D w) (u : PhysicalField L) (n : ℤ) : ‖w u n‖ ^ 2 = D.seq u n := h.2.2 u n

theorem torus_membership (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (h : Specification D w) (u : PhysicalField L) : w u ∈ ActionTorus.actionTorus (D.map u) := h.2.2 u

/-- The normalization differential really is realized by the linear Fourier map. -/
theorem fourier_derivative : HasFDerivAt (fourierL2 L) (differential L) 0 :=
  (differential L).hasFDerivAt

/-- The physical Cphys is the literal u -> conjugate(u(-x)), almost everywhere. -/
theorem physical_reflection (u : PhysicalField L) :
    (Cphys L u : AddCircle L → ℂ) =ᵐ[volume] fun x => conj (u (-x)) := coeFn_Cphys L u

/-- Read-only coeff_conj_reflect via the existing physical L2 binding. -/
theorem fourier_reflection (u : PhysicalField L) : fourierL2 L (Cphys L u) = star (fourierL2 L u) := by
  ext n
  exact fourier_Cphys L u n

/-- At zero, the two normalization requirements hold for the linear differential. -/
theorem zero_normalizations :
    HasFDerivAt (fourierL2 L) (differential L) 0 ∧
      fourierL2 L (Cphys L 0) = star (fourierL2 L 0) :=
  ⟨fourier_derivative, fourier_reflection 0⟩

/-- Compatibility at zero is conditional on the parametric masses vanishing
there; no such physical binding is silently added to IndexedMassData. -/
theorem zero_actions_iff (D : IndexedMassData L κ) :
    (∀ n, ‖fourierL2 L (0 : PhysicalField L) n‖ ^ 2 = D.seq 0 n) ↔ ∀ n, D.seq 0 n = 0 := by
  simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact forall_congr' fun n => eq_comm

/-- A candidate with zero actions at the origin necessarily sends zero to zero. -/
theorem zero_of_zero_actions (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (h : Specification D w) (h0 : ∀ n, D.seq 0 n = 0) : w 0 = 0 := by
  ext n
  have hn := h.2.2 0 n
  rw [h0 n] at hn
  simpa using (sq_eq_zero_iff.mp hn |> norm_eq_zero.mp)

/-- Reflection normalization and exact actions force reflection-invariant masses. -/
theorem masses_reflection (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (h : Specification D w) (u : PhysicalField L) (n : ℤ) : D.seq (Cphys L u) n = D.seq u n := by
  rw [← h.2.2, h.2.1, lp.star_apply, norm_star, h.2.2]

end QuantumNLS.QuantumFourierSpecification

#print axioms QuantumNLS.QuantumFourierSpecification.PhysicalField
#print axioms QuantumNLS.QuantumFourierSpecification.Coordinates
#print axioms QuantumNLS.QuantumFourierSpecification.differential
#print axioms QuantumNLS.QuantumFourierSpecification.differential_apply
#print axioms QuantumNLS.QuantumFourierSpecification.Specification
#print axioms QuantumNLS.QuantumFourierSpecification.specification_iff
#print axioms QuantumNLS.QuantumFourierSpecification.derivative_eq
#print axioms QuantumNLS.QuantumFourierSpecification.exact_action
#print axioms QuantumNLS.QuantumFourierSpecification.torus_membership
#print axioms QuantumNLS.QuantumFourierSpecification.fourier_derivative
#print axioms QuantumNLS.QuantumFourierSpecification.physical_reflection
#print axioms QuantumNLS.QuantumFourierSpecification.fourier_reflection
#print axioms QuantumNLS.QuantumFourierSpecification.zero_normalizations
#print axioms QuantumNLS.QuantumFourierSpecification.zero_actions_iff
#print axioms QuantumNLS.QuantumFourierSpecification.zero_of_zero_actions
#print axioms QuantumNLS.QuantumFourierSpecification.masses_reflection

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.QuantumFourierSpecification.PhysicalField,
    ``QuantumNLS.QuantumFourierSpecification.Coordinates,
    ``QuantumNLS.QuantumFourierSpecification.differential,
    ``QuantumNLS.QuantumFourierSpecification.differential_apply,
    ``QuantumNLS.QuantumFourierSpecification.Specification,
    ``QuantumNLS.QuantumFourierSpecification.specification_iff,
    ``QuantumNLS.QuantumFourierSpecification.derivative_eq,
    ``QuantumNLS.QuantumFourierSpecification.exact_action,
    ``QuantumNLS.QuantumFourierSpecification.torus_membership,
    ``QuantumNLS.QuantumFourierSpecification.fourier_derivative,
    ``QuantumNLS.QuantumFourierSpecification.physical_reflection,
    ``QuantumNLS.QuantumFourierSpecification.fourier_reflection,
    ``QuantumNLS.QuantumFourierSpecification.zero_normalizations,
    ``QuantumNLS.QuantumFourierSpecification.zero_actions_iff,
    ``QuantumNLS.QuantumFourierSpecification.zero_of_zero_actions,
    ``QuantumNLS.QuantumFourierSpecification.masses_reflection]
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
            throwError "Quantum Fourier specification nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.QuantumFourierSpecification.PhysicalField,
    ``QuantumNLS.QuantumFourierSpecification.Coordinates,
    ``QuantumNLS.QuantumFourierSpecification.differential,
    ``QuantumNLS.QuantumFourierSpecification.differential_apply,
    ``QuantumNLS.QuantumFourierSpecification.Specification,
    ``QuantumNLS.QuantumFourierSpecification.specification_iff,
    ``QuantumNLS.QuantumFourierSpecification.derivative_eq,
    ``QuantumNLS.QuantumFourierSpecification.exact_action,
    ``QuantumNLS.QuantumFourierSpecification.torus_membership,
    ``QuantumNLS.QuantumFourierSpecification.fourier_derivative,
    ``QuantumNLS.QuantumFourierSpecification.physical_reflection,
    ``QuantumNLS.QuantumFourierSpecification.fourier_reflection,
    ``QuantumNLS.QuantumFourierSpecification.zero_normalizations,
    ``QuantumNLS.QuantumFourierSpecification.zero_actions_iff,
    ``QuantumNLS.QuantumFourierSpecification.zero_of_zero_actions,
    ``QuantumNLS.QuantumFourierSpecification.masses_reflection]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Quantum Fourier specification aggregate audit PASS: {seen.size} transitive constants. Generic definitions independent of EXT-001; actual BCB1 instantiation carries its explicit Prop premise."
