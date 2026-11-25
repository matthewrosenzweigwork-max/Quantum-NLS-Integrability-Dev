import QuantumNLS.Ext005CrossJCompatibilityR127
import QuantumNLS.Prop022SmoothDomainR126

/-! Bind the single R127 evolution to the actual physical quadratic flow
and its vacuum. All D3 number-moment and essential energy bounds are
proved; no uniqueness in a weaker class is used. R127 remains under review. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology
open Set
namespace QuantumNLS.Prop021QuadraticBindingR129
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext005Moments Ext005MomentEnergyR108 Ext005MomentDomainR33b
open Ext005PhysicalSourceR121 Ext005CrossJCompatibilityR127
open Prop022FactorialCoefficientsR115 Prop022FockPropagatorR122 Prop022DomainR122
open Prop022SmoothDomainR126 Ext006PhysFockCoord
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.rclikeToReal ℂ (Fock L)
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))
local notation "V" => evolution B M A hM hA hB hs u₀

/-- A single choice is made before any moment index is selected. -/
def singleEvolution : ℝ → ℝ → Fock L →ₗᵢ[ℂ] Fock L :=
  Classical.choose (EXT005_single_evolution_R127 B M A hM hA hB hs u₀)
local notation "U" => singleEvolution B M A hM hA hB hs u₀

/-- Identify the actual chosen R127 solution using its PROVED D3 class,
then extend from the dense first moment domain by the two isometries. -/
theorem singleEvolution_eq (s t : ℝ) (x : Fock L) : U s t x = V s t x := by
  have hp := Classical.choose_spec (EXT005_single_evolution_R127 B M A hM hA hB hs u₀)
  have hd (y : momentDomain (L := L) 1) : U s t y.val = V s t y.val := by
    have he := solution_eq_common B M A hM hA hB hs u₀ 1 (by omega)
      (min s t) (max s t) (min_le_max) s ⟨min_le_left _ _,le_max_left _ _⟩
      y.val y.property (fun r => U s r y.val)
      (hp.2.2.2.2.2.1 1 (by omega) (min s t) (max s t) s y)
      (hp.1 s y.val)
    exact he t ⟨min_le_right _ _, le_max_right _ _⟩
  exact (moment_dense (L := L) 1).induction_on
    (p := fun x : Fock L => U s t x = V s t x) x
    (isClosed_eq (U s t).continuous (V s t).continuous) hd

/-- The selected evolution carries exactly the physical quadratic
Hamiltonian's common-domain strong derivative. -/
theorem singleEvolution_hasDerivAt (s t : ℝ) (x : Fock L)
    (hx : Ext006ModeDomainR33a.Smooth (Ext006PhysicalVacuum.coefficient x)) :
    HasDerivAt (fun r => U s r x)
      (Prop022StrongEquationR125.strongForce B M A hM hA hB hs u₀ s
        ⟨x,(smooth_iff_moments x).mp hx 4⟩ t) t := by
  simp_rw [singleEvolution_eq]
  exact evolution_smooth_hasDerivAt B M A hM hA hB hs u₀ s t x hx

def fluctuation (t : ℝ) : Fock L := U 0 t vac
local notation "ξ" => fluctuation B M A hM hA hB hs u₀

lemma fluctuation_eq (t : ℝ) : ξ t = vacuumEvolution B M A hM hA hB hs u₀ t :=
  singleEvolution_eq B M A hM hA hB hs u₀ 0 t vac

theorem fluctuation_initial_norm_smooth :
    ξ 0 = vac ∧ (∀ t, ‖ξ t‖ = 1) ∧
      (∀ t, Ext006ModeDomainR33a.Smooth (Ext006PhysicalVacuum.coefficient (ξ t))) ∧
      ContDiff ℝ 1 ξ := by
  have he : ξ = vacuumEvolution B M A hM hA hB hs u₀ :=
    funext (fluctuation_eq B M A hM hA hB hs u₀)
  rw [he]
  exact actual_vacuum_initial_norm_smooth B M A hM hA hB hs u₀

/-- Every application to the vacuum has its own proved uniform comparison
energy bound, as required by the owner-corrected EXT-005 contract. -/
theorem fluctuation_energyBounded (j : ℕ) (hj : 1 ≤ j) (T : ℝ) :
    EnergyBounded j (Icc (-T) T) ξ := by
  change EnergyBounded j (Icc (-T) T) (fun t => U 0 t vac)
  have h := evolution_energyBounded B M A hM hA hB hs u₀ j hj 0 T
    ⟨vac,(smooth_iff_moments vac).mp vacuum_smooth j⟩
  simpa only [zero_sub,zero_add,← singleEvolution_eq] using h

/-- The weak equation, norm continuity and essential Q(A) bound are all
conclusions for the SAME vacuum curve on every finite signed interval. -/
theorem fluctuation_D3 (j : ℕ) (hj : 1 ≤ j) (l r : ℝ) :
    Ext005SourceIntervalR32b.D3On (momentPositive j) l r
      (physicalSource B M A hM hA hB hs u₀ j hj l r) ξ := by
  change Ext005SourceIntervalR32b.D3On (momentPositive j) l r
    (physicalSource B M A hM hA hB hs u₀ j hj l r) (fun t => U 0 t vac)
  have h := common_D3 B M A hM hA hB hs u₀ j hj l r 0
    ⟨vac,(smooth_iff_moments vac).mp vacuum_smooth j⟩
  simpa only [← singleEvolution_eq] using h

end QuantumNLS.Prop021QuadraticBindingR129
#print axioms QuantumNLS.Prop021QuadraticBindingR129.singleEvolution_eq
#print axioms QuantumNLS.Prop021QuadraticBindingR129.singleEvolution_hasDerivAt
#print axioms QuantumNLS.Prop021QuadraticBindingR129.fluctuation_energyBounded
#print axioms QuantumNLS.Prop021QuadraticBindingR129.fluctuation_D3

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021QuadraticBindingR129"].any
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
  Lean.logInfo m!"R129 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
