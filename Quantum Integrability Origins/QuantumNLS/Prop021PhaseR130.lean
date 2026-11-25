import QuantumNLS.Prop021DisplacementR129
import QuantumNLS.Prop022GradientR118
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-! The literal printed phase for the constructed Hartree trajectory,
including negative times, and the exact linear cancellation on the common
number-moment domain. The moving-center Weyl derivative remains separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 10000
open scoped InnerProductSpace Topology
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop021PhaseR130
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022ClassicalTimeR116
open Prop022GradientR118 Prop021DisplacementR129 Ext006PhysFockCoord
open Ext006SmoothOperatorsR34a Ext006StrongFieldR41a Ext006ModeDomainR33a
variable {L : ℝ} [Fact (0 < L)]
local instance profileGroup : AddCommGroup (L2T L) := MeasureTheory.Lp.instNormedAddCommGroup.toAddCommGroup
local instance (priority := 1200) profileRealNS : NormedSpace ℝ (L2T L) :=
  NormedSpace.restrictScalars ℝ ℂ _
local instance (priority := 1200) profileRealModule : Module ℝ (L2T L) :=
  (profileRealNS (L := L)).toModule
local instance (priority := 1200) profileRealSMul : SMul ℝ (L2T L) :=
  (profileRealNS (L := L)).toSMul
local instance (priority := 1200) complexRealNS : NormedSpace ℝ ℂ :=
  NormedAlgebra.toNormedSpace ℂ
local instance (priority := 1200) complexRealModule : Module ℝ ℂ := complexRealNS.toModule
local instance (priority := 1200) complexRealSMul : SMul ℝ ℂ := complexRealNS.toSMul
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))
local notation "u" => profile B M A hA hB hs u₀

/-- F(u_s)+Im<u_s,dot u_s>, with dot u the actual derivative. -/
def density (t : ℝ) : ℝ := classicalSeries B (u t) + (⟪u t,deriv u t⟫_ℂ).im

include hM in
lemma density_continuous : Continuous (density B M A hA hB hs u₀) := by
  have hp := profile_spec B M A hA hB hs u₀
  have hi : Continuous (fun t => ⟪u t,deriv u t⟫_ℂ) :=
    hp.2.1.continuous.inner (𝕜 := ℂ) hp.2.1.continuous_deriv_one
  exact (actual_classicalSeries_C1 B M A hM hA hB hs u₀).continuous.add
    (Complex.continuous_im.comp hi)

/-- Exactly theta_N from the printed proof; the integral is signed. -/
def theta (N : ℕ) (t : ℝ) : ℝ :=
  (N:ℝ) * ∫ s in (0:ℝ)..t, density B M A hA hB hs u₀ s

lemma theta_zero (N : ℕ) : theta B M A hA hB hs u₀ N 0 = 0 := by
  simp [theta]

include hM in
theorem theta_hasDerivAt (N : ℕ) (t : ℝ) :
    HasDerivAt (theta B M A hA hB hs u₀ N)
      ((N:ℝ) * density B M A hA hB hs u₀ t) t := by
  have hc := density_continuous B M A hM hA hB hs u₀
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (N:ℝ)

/-- Exactly exp(-i theta_N(t)). -/
def phase (N : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((-Complex.I) * (theta B M A hA hB hs u₀ N t:ℂ))

lemma phase_norm (N : ℕ) (t : ℝ) : ‖phase B M A hA hB hs u₀ N t‖=1 := by
  simp [phase,Complex.norm_exp]

lemma phase_zero (N : ℕ) : phase B M A hA hB hs u₀ N 0 = 1 := by
  simp [phase,theta_zero]

include hM in
theorem phase_hasDerivAt (N : ℕ) (t : ℝ) :
    HasDerivAt (phase B M A hA hB hs u₀ N)
      (((-Complex.I) * ((N:ℝ) * density B M A hA hB hs u₀ t:ℂ)) *
        phase B M A hA hB hs u₀ N t) t := by
  delta complexRealModule complexRealNS complexRealSMul
  unfold phase
  have hd0 := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
    (theta_hasDerivAt B M A hM hA hB hs u₀ N t)
  have hd := (hd0.const_mul (-Complex.I)).cexp
  simpa only [Function.comp_apply,Complex.ofRealCLM_apply,Complex.ofReal_mul,mul_comm] using hd

/-- Scalar cancellation with the Weyl derivative's i Im<v,dot v> term,
including the exact N normalization. -/
theorem scalar_cancellation (N : ℕ) (t : ℝ) :
    ((N:ℝ) * density B M A hA hB hs u₀ t:ℂ) -
      ((N:ℝ) * (⟪u t,deriv u t⟫_ℂ).im:ℂ) =
        ((N:ℝ) * classicalSeries B (u t):ℂ) := by
  simp only [density,Complex.ofReal_add]
  ring

/-- Coordinate linear Hamiltonian, with literal normalized creation and
annihilation, on the already constructed common physical domain. -/
def linearHamiltonian (g : L2T L) (x : Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) : Fock L :=
  (Phi (L := L)).symm ((field ((Ext006KernelHilbertSchmidt.physicalBasis L).repr g) (smoothLift x hx)).val)

lemma rotated_generator (g : Ext006BogoliubovAlg.H) :
    C ((-Complex.I) • g)-Ext006SmoothOperatorsR34a.A ((-Complex.I) • g) = (-Complex.I) • field g := by
  rw [Ext006InverseGraphsR36a.C_smul,Ext006InverseGraphsR36a.A_smul,field]
  simp only [Complex.star_def,map_neg,Complex.conj_I,neg_neg]
  module

/-- The ACTUAL classical equation cancels the smooth Weyl generator's
linear Hamiltonian, with no assumed motion equation or field identity. -/
theorem linear_cancellation (t : ℝ) (x : Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) :
    generator (deriv u t) x hx = (-Complex.I) • linearHamiltonian (gradient B (u t)) x hx := by
  have hd := (profile_spec B M A hA hB hs u₀).2.2.2.1 t
  rw [hd.deriv, velocity_eq_neg_I_gradient]
  unfold generator linearHamiltonian
  rw [map_smul,rotated_generator]
  exact map_smul _ _ _

/-- The displacement center and its actual strong derivative. -/
def center (N : ℕ) (t : ℝ) : L2T L := (Real.sqrt (N:ℝ):ℂ) • u t

theorem center_hasDerivAt (N : ℕ) (t : ℝ) :
    HasDerivAt (center B M A hA hB hs u₀ N)
      ((Real.sqrt (N:ℝ):ℂ) • velocity B (u t)) t :=
  by
    delta profileGroup profileRealModule
    unfold center
    have hd := (profile_spec B M A hA hB hs u₀).2.2.2.1 t
    have hh := HasDerivAt.const_smul (Real.sqrt (N:ℝ):ℂ) hd
    exact hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun r => rfl))

/-- The Weyl scalar term has exactly the printed N factor. -/
theorem center_inner (N : ℕ) (t : ℝ) :
    (⟪center B M A hA hB hs u₀ N t,
      deriv (center B M A hA hB hs u₀ N) t⟫_ℂ).im =
      (N:ℝ) * (⟪u t,deriv u t⟫_ℂ).im := by
  rw [(center_hasDerivAt B M A hA hB hs u₀ N t).deriv,
    ← ((profile_spec B M A hA hB hs u₀).2.2.2.1 t).deriv]
  simp only [center,inner_smul_left,inner_smul_right,Complex.conj_ofReal,← mul_assoc,
    ← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg N),Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

end QuantumNLS.Prop021PhaseR130
#print axioms QuantumNLS.Prop021PhaseR130.theta_hasDerivAt
#print axioms QuantumNLS.Prop021PhaseR130.phase_hasDerivAt
#print axioms QuantumNLS.Prop021PhaseR130.scalar_cancellation
#print axioms QuantumNLS.Prop021PhaseR130.linear_cancellation

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021PhaseR130"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R130 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
