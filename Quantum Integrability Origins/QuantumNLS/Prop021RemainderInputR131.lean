import QuantumNLS.Prop021PhaseR130
import QuantumNLS.Prop021QuadraticR130
import QuantumNLS.Prop021ManyBodyR129
import QuantumNLS.Prop024PairMomentsR55

/-! The exact Q7B:lem:remainder input on torus Fock. Its identity uses
the printed displacement and the same maximal Hamiltonian as PROP-021.
The source hypotheses are expressed using the spectral moments of PROP-023. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop021RemainderInputR131
open BetheCoefficientTransform PhysicalTensor Ext025B3PhysicalSectors
open Ext006NumberPhase Ext006ModeDomainR33a Ext005Moments Prop021ManyBodyR129
open Prop022FactorialCoefficientsR115 Prop022ClassicalTimeR116 Prop022GradientR118
open Prop022StrongOperatorR125 Prop021PhaseR130 Prop022OVacuum
open Prop022ActualProfileR117 Prop021QuadraticBindingR129 Ext006PhysFockCoord
open Prop022PositiveDataR126 Prop022ClassicalFlowR126 Prop021RatesR128
open Prop022FactorialMajorantR115 Prop022FockPropagatorR122
open Prop024WeylConventionR55
variable {L : ℝ} [Fact (0 < L)]

/-- Both displayed estimates of Q7B:eq:mgf on the physical number operator. -/
def NumberMoments (Q : ℝ) (x : Fock L) : Prop :=
  exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ)) ∧
  ∀ j : ℕ, 1 ≤ j → ∃ hx : x ∈ (polynomialRoot j).domain,
    ‖polynomialRoot j ⟨x,hx⟩‖ ≤ Real.rpow (32 * Q * j) ((j : ℝ) / 2)

/-- The literal constant, linear and quadratic terms of the shifted Hamiltonian. -/
def lowOrders (B : ∀ m, HN L m →L[ℂ] HN L m) (N : ℕ) (u : L2T L)
    (x : Fock L) (hx : Smooth (Ext006PhysicalVacuum.coefficient x))
    (h₂ : x ∈ momentDomain (L := L) 2) : Fock L :=
  ((N : ℝ) * classicalSeries B u : ℂ) • x +
    (Real.sqrt N : ℂ) • linearHamiltonian (gradient B u) x hx +
    quadraticAction (numberCoefficient B u) (pairCoefficient B u) ⟨x,h₂⟩

/-- The literal PROP-024 interaction has the same maximal domain and
action as the Hamiltonian used by PROP-021 and PROP-025. -/
theorem interaction_eq_hamiltonian
    (B : ∀ m, HN L m →L[ℂ] HN L m) (N : ℕ) :
    Prop024PhysicalHamiltonianR54.interaction N B = hamiltonian B N := by
  apply congrArg (fun F : ∀ n, HN L n →L[ℂ] HN L n => block F)
  funext n
  unfold Prop024PhysicalHamiltonianR54.interactionSector sector
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hU := PlacementConsistency.physicalU_N_r_eq_genericU_N_r L n (i.val+1)
    (Nat.succ_le_of_lt i.isLt) (B (i.val+1))
  change ((_ : ℝ) : ℂ) • KernelDefinition.physicalU_N_r L n _ _ _ = _
  rw [hU]
  congr 2
  unfold Prop024PhysicalHamiltonianR54.fallingScale
  rw [div_eq_mul_inv, inv_pow, mul_comm]

/-- The strong action asserted by the printed remainder estimate, at
fixed model parameters and constant. -/
def RemainderEstimate (A CA' : ℝ) : Prop :=
  ∀ (B : ∀ m, HN L m →L[ℂ] HN L m) (M : ℝ), 1 ≤ M → FactorialBound B M A →
    (∀ m, (B m).adjoint = B m) →
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ (u : L2T L), ‖u‖ = 1 → ∀ x : Fock L, NumberMoments Q x →
    ∃ (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) (h₂ : x ∈ momentDomain (L := L) 2)
      (hd : printedWeyl ((Real.sqrt N : ℂ) • u) x ∈ (hamiltonian B N).domain) (R : Fock L),
        hamiltonian B N ⟨printedWeyl ((Real.sqrt N : ℂ) • u) x,hd⟩ =
          printedWeyl ((Real.sqrt N : ℂ) • u) (lowOrders B N u x hx h₂ + R) ∧
        ‖R‖ ≤ CA' * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ)

/-- Q7B:lem:remainder. Moving the unitary to the right gives its
conjugation identity as a strong action on the shifted vector. The
existential remainder is uniquely determined by that identity. -/
def Prop024RemainderInput : Prop :=
  ∀ A : ℝ, 0 < A → ∃ CA' : ℝ, 0 ≤ CA' ∧ RemainderEstimate (L := L) A CA'

/-- The low-order terms are defined for every vector in the printed
moment class. Their domain witnesses add no hypothesis to PROP-024. -/
theorem smooth_of_numberMoments (Q : ℝ) (x : Fock L) (hm : NumberMoments Q x) :
    Smooth (Ext006PhysicalVacuum.coefficient x) := by
  apply (Prop021DisplacementR129.common_domain x).2
  intro j
  rw [momentDomain_iff]
  cases j with
  | zero =>
      have h := (lp.hasSum_norm (p := 2) (by norm_num) x).summable
      simpa only [momentWeight, pow_zero, one_mul, ENNReal.toReal_ofNat, Real.rpow_two] using h
  | succ j =>
      obtain ⟨hdom, _⟩ := hm.2 (j+1) (by omega)
      have hs := (lp.hasSum_norm (p := 2) (by norm_num)
        (polynomialRoot (j+1) ⟨x,hdom⟩)).summable
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Prop023SpectralMoments.root_apply,
        Prop023SpectralMoments.root_sector_norm_sq] at hs
      apply Summable.of_nonneg_of_le (fun n => mul_nonneg (momentWeight_nonneg _ _) (sq_nonneg _)) _ hs
      intro n
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      unfold momentWeight
      exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]) _

section PositiveRanks

variable (K : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ))
    (hsK : ∀ n, (K n).adjoint = K n) (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P)
local notation "B" => positiveExtension K
local notation "hB" => positiveExtension_bound K M A hK
local notation "hs" => positiveExtension_selfAdjoint K hsK
local notation "hM₀" => (zero_le_one.trans hM)
local notation "u" => profile B M A hA.le hB hs u₀
local notation "ξ" => fluctuation B M A hM₀ hA.le hB hs u₀
local notation "Q" => numberParameter (pairMajorant A) T M P
local notation "V" => propagator B M A hM₀ hA.le hB hs u₀

/-- The exact frozen PROP-022 input supplies PROP-023 on the same vacuum
that has the strong evolution proved in R129. -/
theorem actual_moments (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖fderiv ℝ (classicalFlow B M A hA.le hB hs (r - q)) (u q)‖ ≤ P)
    (t : ℝ) (ht : |t| ≤ T) : NumberMoments Q (ξ t) := by
  have hv : ξ t = V 0 t vac := Prop021QuadraticR130.single_unitary B M A hM₀ hA.le hB hs u₀ 0 t vac
  rw [hv]
  unfold NumberMoments numberParameter
  simpa only [mul_pow] using
    Prop024PairMomentsR55.pairInput_moments K M A hM hA hK hsK u₀ T P hP hPair hS t ht

/-- Specialization of the precise PROP-024 input to the quadratic vacuum,
with its number moments discharged by the precise PROP-022 input. -/
theorem shifted_vacuum
    (hPair : Prop022PairInput K M A hM hA hK hsK u₀ T P hP)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖fderiv ℝ (classicalFlow B M A hA.le hB hs (r - q)) (u q)‖ ≤ P)
    (CA' : ℝ) (hRem : RemainderEstimate (L := L) A CA')
    (N : ℕ) (hN : 256 * Real.exp 1 * A * Q ≤ N) (t : ℝ) (ht : |t| ≤ T) :
    ∃ (hx : Smooth (Ext006PhysicalVacuum.coefficient (ξ t))) (h₂ : ξ t ∈ momentDomain (L := L) 2)
      (hd : printedWeyl ((Real.sqrt N : ℂ) • u t) (ξ t) ∈ (hamiltonian B N).domain) (R : Fock L),
        hamiltonian B N ⟨printedWeyl ((Real.sqrt N : ℂ) • u t) (ξ t),hd⟩ =
          printedWeyl ((Real.sqrt N : ℂ) • u t) (lowOrders B N (u t) (ξ t) hx h₂ + R) ∧
        ‖R‖ ≤ CA' * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ) := by
  have hu : ‖u t‖ = 1 := (profile_spec B M A hA.le hB hs u₀).2.2.1 t
  exact hRem B M hM hB hs N Q (one_le_numberParameter _ _ _ _) hN (u t) hu (ξ t)
    (actual_moments K M A hM hA hK hsK u₀ T P hP hPair hS t ht)

end PositiveRanks

section Cancellation

open Prop021DisplacementR129 Ext006SmoothOperatorsR34a Ext005MomentEnergyR108 Ext005FormCutoffR109
open Ext006KernelHilbertSchmidt
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))
local notation "u" => profile B M A hA hB hs u₀
local notation "ξ" => fluctuation B M A hM hA hB hs u₀

private lemma generator_real_smul (r : ℝ) (v : L2T L) (x : Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) :
    generator ((r : ℂ) • v) x hx = (r : ℂ) • generator v x hx := by
  unfold generator
  rw [map_smul, Ext006InverseGraphsR36a.C_smul, Ext006InverseGraphsR36a.A_smul,
    Complex.star_def, Complex.conj_ofReal]
  let Cr := C ((physicalBasis L).repr v)
  let An := A ((physicalBasis L).repr v)
  change (Phi (L := L)).symm (((r : ℂ) • Cr - (r : ℂ) • An) (smoothLift x hx)).val =
    (r : ℂ) • (Phi (L := L)).symm ((Cr-An) (smoothLift x hx)).val
  rw [← smul_sub (r : ℂ) Cr An, LinearMap.smul_apply, Submodule.coe_smul, map_smul]

/-- The sum of the phase derivative, Weyl generator with its scalar term,
and actual quasifree velocity equals the strong low-order Hamiltonian
velocity. This is a vector identity on the actual propagated vacuum. -/
theorem vacuum_cancellation (N : ℕ) (t : ℝ)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient (ξ t))) (h₂ : ξ t ∈ momentDomain (L := L) 2) :
    ((-Complex.I) * ((N : ℝ) * density B M A hA hB hs u₀ t : ℂ)) • ξ t +
      generator (deriv (center B M A hA hB hs u₀ N) t) (ξ t) hx +
      (Complex.I *
        (⟪center B M A hA hB hs u₀ N t, deriv (center B M A hA hB hs u₀ N) t⟫_ℂ).im) • ξ t +
      deriv ξ t = (-Complex.I) • lowOrders B N (u t) (ξ t) hx h₂ := by
  have hquad : deriv ξ t =
      (-Complex.I) • quadraticAction (numberCoefficient B (u t)) (pairCoefficient B (u t))
        ⟨ξ t,h₂⟩ := by
    have hd := (singleEvolution_hasDerivAt B M A hM hA hB hs u₀ 0 t vac
      Prop022SmoothDomainR126.vacuum_smooth).deriv
    change deriv ξ t = _ at hd
    rw [hd]
    unfold Prop022StrongEquationR125.strongForce quadraticAction
    change _ • strongCoordinates _ _
      (rootLift 2 (Prop022FockPropagatorR122.evolution B M A hM hA hB hs u₀ 0 t vac)) = _
    have he : Prop022FockPropagatorR122.evolution B M A hM hA hB hs u₀ 0 t vac = ξ t :=
      (singleEvolution_eq B M A hM hA hB hs u₀ 0 t vac).symm
    rw [he, rootLift_eq 2 _ h₂]
    rfl
  have hphase : (-Complex.I) * ((N : ℝ) * density B M A hA hB hs u₀ t : ℂ) +
      Complex.I * ((N : ℝ) * (⟪u t, deriv u t⟫_ℂ).im : ℂ) =
      (-Complex.I) * ((N : ℝ) * classicalSeries B (u t) : ℂ) := by
    linear_combination (-Complex.I) * scalar_cancellation B M A hA hB hs u₀ N t
  rw [center_inner, (center_hasDerivAt B M A hA hB hs u₀ N t).deriv,
    ← ((profile_spec B M A hA hB hs u₀).2.2.2.1 t).deriv,
    generator_real_smul, linear_cancellation B M A hA hB hs u₀, hquad]
  have hadd {x y z w : Fock L} : x+y+z+w = (x+z)+y+w := by abel
  rw [hadd, ← add_smul]
  simp only [Complex.ofReal_mul]
  rw [hphase]
  unfold lowOrders
  module

end Cancellation

end QuantumNLS.Prop021RemainderInputR131

#print axioms QuantumNLS.Prop021RemainderInputR131.interaction_eq_hamiltonian
#print axioms QuantumNLS.Prop021RemainderInputR131.smooth_of_numberMoments
#print axioms QuantumNLS.Prop021RemainderInputR131.actual_moments
#print axioms QuantumNLS.Prop021RemainderInputR131.shifted_vacuum
#print axioms QuantumNLS.Prop021RemainderInputR131.vacuum_cancellation

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021RemainderInputR131"].any
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
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
