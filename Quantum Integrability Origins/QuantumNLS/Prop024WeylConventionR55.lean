import QuantumNLS.Prop024ContractionsR54
import QuantumNLS.Prop022OMain

/-! Round 55: connect the frozen PROP-022 printed Weyl convention to the
physical displacement used by the PROP-024 interaction.  The exact PROP-022
conclusion is retained under the single named intermediate input
`Prop022PairInput`; this module does not add a Weyl/interaction compatibility
premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace QuantumNLS.Prop024WeylConventionR55

open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors
open Ext006PhysFockCoord Ext006SmoothOperatorsR34a Ext006StrongFieldR41a
open Ext006InverseGraphsR36a Ext006KernelHilbertSchmidt
open Prop022OVacuum Prop022PositiveDataR126 Prop022ClassicalFlowR126
  Prop022FlowDifferentialR126 Prop022VariationalR123 Prop022FockPropagatorR122
  Ext006PhysQuasifree Ext006NumberPhase
open Prop024ContractionsR54

variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The exact frozen PROP-022 Q7B:lem:pair conclusion, named as the sole
PROP-022 input to intermediate PROP-024 assembly theorems. -/
abbrev Prop022PairInput
    (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ)
    (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n)
    (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P) : Prop :=
  let B := Prop022PositiveDataR126.positiveExtension K
  let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
  let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
  let Phi := Prop022ClassicalFlowR126.classicalFlow B M A hA.le hB hsa
  let u := Prop022ActualProfileR117.profile B M A hA.le hB hsa u₀
  let S := fun t s : ℝ => fderiv ℝ (Phi (t - s)) (u s)
  let a := fun t : ℝ => Prop022PrintedCoefficientsR124.numberOperator B (u t)
  let b := fun t : ℝ => Prop022PairHSR122.pairKernel B (u t)
  let α := Prop022VariationalR123.alpha B M A hA.le hB hsa u₀
  let β := Prop022VariationalR123.betaBlock B M A hA.le hB hsa u₀
  let V := fun t s : ℝ =>
    Prop022FockPropagatorR122.propagator B M A (by linarith) hA.le hB hsa u₀ s t
  (∀ t, (a t).adjoint = a t ∧
      (∀ i j : ℤ, ⟪Ext006KernelHilbertSchmidt.physicalBasis L i,
          (b t) (Ext006KernelHilbertSchmidt.physicalBasis L j)⟫_ℂ =
        ⟪Ext006KernelHilbertSchmidt.physicalBasis L j,
          (b t) (Ext006KernelHilbertSchmidt.physicalBasis L i)⟫_ℂ) ∧
      TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L) (b t) ≠ ⊤ ∧
      Real.sqrt ((TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
        (b t)).toReal) ≤ Prop022FactorialMajorantR115.pairMajorant A * M ∧
      ‖a t‖ ≤ M * ∑' r : ℕ,
        (((r+1 : ℕ) : ℝ)^2 * A^(r+1) /
          Real.sqrt ((2*(r+1)).factorial : ℝ))) ∧
    (∀ s t : ℝ, S t s =
      (Prop022VariationalR123.flow B M A hA.le hB hsa u₀ t s).toContinuousLinearMap) ∧
    (∀ s t (x : L2T L), Complex.I • deriv (fun r => S r s x) t =
      a t (S t s x) + b t
        (Ext006KernelHilbertSchmidt.conjugation
          (Ext006KernelHilbertSchmidt.physicalBasis L) (S t s x))) ∧
    (∀ s t (x : L2T L), S t s x = α t s x + β t s
      (Ext006KernelHilbertSchmidt.conjugation
        (Ext006KernelHilbertSchmidt.physicalBasis L) x)) ∧
    ((∀ r q : ℝ, |r| ≤ T → |q| ≤ T → ‖S r q‖ ≤ P) → ∀ t, |t| ≤ T →
      TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L) (β t 0) ≠ ⊤ ∧
      Real.sqrt ((TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
        (β t 0)).toReal) ≤ |t| * Prop022FactorialMajorantR115.pairMajorant A * M * P) ∧
    (∀ s (x : Fock L), V s s x = x) ∧
    (∀ r s t (x : Fock L), V t s (V s r x) = V t r x) ∧
    (∀ s (x : Fock L), Continuous (fun t => V t s x)) ∧
    (∀ s t (x : Fock L), (∀ j : ℕ,
        x ∈ Ext005Moments.momentDomain (L := L) j) →
      HasDerivAt (fun r => V r s x) ((-Complex.I) •
        Prop022StrongOperatorR125.strongCoordinates
          (Prop022FactorialCoefficientsR115.numberCoefficient B (u t))
          (Prop022FactorialCoefficientsR115.pairCoefficient B (u t))
          (Ext005FormCutoffR109.rootLift 2 (V t s x))) t) ∧
    (∀ s t (v : L2T L) (x : Fock L),
      V t s (Prop022OVacuum.printedWeyl v ((V t s).symm x)) =
        Prop022OVacuum.printedWeyl (S t s v) x) ∧
    (∀ t, Ext006PhysQuasifree.PhysicalQuasifreeSource (V t 0 vac) ∧
      ‖V t 0 vac‖ = 1 ∧
      Ext006NumberPhase.numberExpectation (fun n => (n : ℝ≥0∞)) (V t 0 vac) =
        TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L) (β t 0))

/-- R54's displacement is exactly the frozen PROP-022 printed Weyl operator
at the physical vector `sqrt(N) u`; this fixes the scalar and sign at the
operator level. -/
theorem physicalWeyl_eq_printedWeyl (N : ℕ) (u : L2T L) (x : Fock L) :
    physicalWeyl N u x =
      Prop022OVacuum.printedWeyl ((Real.sqrt (N : ℝ) : ℂ) • u) x := by
  unfold physicalWeyl Prop022OVacuum.printedWeyl
  congr 1
  rw [smul_smul]

/-- The generator identity for the exact scaled physical displacement,
inherited from the frozen PROP-022 printed-Weyl generator theorem. -/
theorem physicalWeyl_generator (N : ℕ) (u : L2T L) (w : Ext006SmoothOperatorsR34a.D) :
    Complex.I • (Ext006StrongFieldR41a.field
        ((Ext006KernelHilbertSchmidt.physicalBasis L).repr
          ((-Complex.I * (Real.sqrt (N : ℝ) : ℂ)) • u)) w).1 =
      (Ext006SmoothOperatorsR34a.C
          ((Ext006KernelHilbertSchmidt.physicalBasis L).repr
            ((Real.sqrt (N : ℝ) : ℂ) • u)) w).1 -
        (Ext006SmoothOperatorsR34a.A
          ((Ext006KernelHilbertSchmidt.physicalBasis L).repr
            ((Real.sqrt (N : ℝ) : ℂ) • u)) w).1 := by
  have harg :
      ((-Complex.I * (Real.sqrt (N : ℝ) : ℂ)) : ℂ) • u =
        (-Complex.I) • ((Real.sqrt (N : ℝ) : ℂ) • u) := by
    rw [smul_smul]
  rw [harg]
  exact Prop022OVacuum.printedWeyl_generator
    ((Real.sqrt (N : ℝ) : ℂ) • u) w

/-- The sole output taken from PROP-022 during intermediate assembly: the
printed quasifree-vacuum and number data, projected from the exact named
input above. -/
theorem pairInput_vacuum_data
    (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ)
    (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n)
    (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P)
    (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP) :
    let B := Prop022PositiveDataR126.positiveExtension K
    let hB := Prop022PositiveDataR126.positiveExtension_bound K M A hK
    let hsa := Prop022PositiveDataR126.positiveExtension_selfAdjoint K hsK
    let V := fun t s : ℝ =>
      Prop022FockPropagatorR122.propagator B M A (by linarith) hA.le hB hsa u₀ s t
    ∀ t, PhysicalQuasifreeSource (V t 0 vac) ∧ ‖V t 0 vac‖ = 1 ∧
      numberExpectation (fun n => (n : ℝ≥0∞)) (V t 0 vac) =
        TraceClass.hsSq (Ext006KernelHilbertSchmidt.physicalBasis L)
          (Prop022VariationalR123.betaBlock B M A hA.le hB hsa u₀ t 0) := by
  dsimp [Prop022PairInput] at hPair
  rcases hPair with ⟨_, _, _, _, _, _, _, _, _, _, hVac⟩
  exact hVac

end QuantumNLS.Prop024WeylConventionR55

#print axioms QuantumNLS.Prop024WeylConventionR55.physicalWeyl_eq_printedWeyl
#print axioms QuantumNLS.Prop024WeylConventionR55.physicalWeyl_generator
#print axioms QuantumNLS.Prop024WeylConventionR55.pairInput_vacuum_data

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024WeylConventionR55." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024WeylConventionR55." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"R55 Weyl convention aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
