import QuantumNLS.Prop022StrongEquationR125
import QuantumNLS.Ext006StrongVacuumR33a
import QuantumNLS.Ext006SmearedCCRR34a

/-! Match the physical number-moment domain of the actual quadratic
propagator with the occupation smooth domain used by the source fields.
This supplies a domain bridge toward covariance, not covariance itself. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology
open Set Filter ContinuousLinearMap
namespace QuantumNLS.Prop022SmoothDomainR126
open Occupation PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext005Moments Ext005MomentEnergyR108 Ext006PhysicalVacuum
open Ext006ModeDomainR33a Ext006PhysFockCoord Prop022FockPropagatorR122
open Prop022DomainR122 Prop022FactorialCoefficientsR115
variable {L : ℝ} [Fact (0 < L)]
local instance : NormedSpace ℝ (Fock L) := NormedSpace.restrictScalars ℝ ℂ (Fock L)
local instance : InnerProductSpace ℝ (Fock L) := InnerProductSpace.rclikeToReal ℂ (Fock L)

lemma sector_weighted_parseval (j n : ℕ) (x : Fock L) :
    Summable (fun m : Arr n => ((total m.val : ℝ)+1)^j * ‖coefficient x m.val‖^2) ∧
      (∑' m : Arr n, ((total m.val : ℝ)+1)^j * ‖coefficient x m.val‖^2) =
        momentWeight j n * ‖x n‖^2 := by
  let c := occupationCoefficient (freeBasis L n) (x n)
  have he (m : Arr n) : coefficient x m.val = c m := by
    rcases m with ⟨m, hm⟩
    change total m = n at hm
    subst n
    rfl
  have hs := lp.hasSum_norm (p := 2) (by norm_num) c
  have hs' : Summable (fun m : Arr n => ‖c m‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs.summable
  have he' : (fun m : Arr n => ((total m.val : ℝ)+1)^j * ‖coefficient x m.val‖^2) =
      fun m => momentWeight j n * ‖c m‖^2 := by
    funext m
    rw [he m, show total m.val = n from m.property]
    rfl
  rw [he']
  refine ⟨hs'.mul_left _, ?_⟩
  rw [tsum_mul_left]
  congr 1
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, c, LinearIsometryEquiv.norm_map]
    using hs.tsum_eq

/-- Exact domain equivalence, proved by Parseval and the disjoint particle
number fibers. Neither real tsum without summability nor energy finiteness
by notation is used as a domain test. -/
theorem coefficient_moment_iff (j : ℕ) (x : Fock L) :
    Summable (fun m : Occ => ((total m : ℝ)+1)^j * ‖coefficient x m‖^2) ↔
      x ∈ momentDomain (L := L) j := by
  rw [momentDomain_iff]
  constructor
  · intro hx
    have hs := (Equiv.summable_iff (Equiv.sigmaFiberEquiv (fun m : Occ => total m))).2 hx
    have hh := hs.sigma
    exact hh.congr (fun n => (sector_weighted_parseval j n x).2)
  · intro hx
    apply (Equiv.summable_iff (Equiv.sigmaFiberEquiv (fun m : Occ => total m))).1
    apply (summable_sigma_of_nonneg
      (f := fun p : (Σ n : ℕ, Arr n) => ((total p.2.val : ℝ)+1)^j * ‖coefficient x p.2.val‖^2)
      (fun _ => mul_nonneg (by positivity) (sq_nonneg _))).2
    refine ⟨fun n => (sector_weighted_parseval j n x).1, ?_⟩
    exact hx.congr (fun n => (sector_weighted_parseval j n x).2.symm)

/-- The BD smooth domain is exactly the common physical moment domain. -/
theorem smooth_iff_moments (x : Fock L) :
    Smooth (coefficient x) ↔ ∀ j : ℕ, x ∈ momentDomain (L := L) j := by
  exact forall_congr' (fun j => coefficient_moment_iff j x)

/-- The actual physical vacuum belongs to the common field domain. -/
lemma vacuum_smooth : Smooth (coefficient (vac (L := L))) := by
  have he : coefficient (vac (L := L)) =
      fun m => (lp.single 2 0 (1 : ℂ) : OccupationHilbert.L2 Occ) m := by
    funext m
    change Phi (physCore (ket 0)) m = _
    rw [physCore_ket, LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  exact Ext006SmearedCCRR34a.single_smooth 0

variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))
local notation "V" => evolution B M A hM hA hB hs u₀

/-- The actual R122 propagator preserves the source-field smooth domain,
in both directions, for all signed initial and final times. -/
theorem evolution_smooth_iff (s t : ℝ) (x : Fock L) :
    Smooth (coefficient (V s t x)) ↔ Smooth (coefficient x) := by
  rw [smooth_iff_moments, smooth_iff_moments]
  constructor
  · intro hx j
    exact domain_mono (by omega : j ≤ j+1)
      ((evolution_domain_iff B M A hM hA hB hs u₀ (j+1) (by omega) s t x).mp (hx (j+1)))
  · intro hx j
    exact domain_mono (by omega : j ≤ j+1)
      ((evolution_energy B M A hM hA hB hs u₀ (j+1) (by omega) s t ⟨x,hx (j+1)⟩).1)

/-- Smooth initial vectors have the strong physical quadratic equation from
R125. The datum's domain obligation is now expressed in source-field terms. -/
theorem evolution_smooth_hasDerivAt (s t : ℝ) (x : Fock L)
    (hx : Smooth (coefficient x)) :
    HasDerivAt (fun r => V s r x)
      (Prop022StrongEquationR125.strongForce B M A hM hA hB hs u₀ s
        ⟨x, (smooth_iff_moments x).mp hx 4⟩ t) t :=
  Prop022StrongEquationR125.evolution_hasDerivAt B M A hM hA hB hs u₀ s t
    ⟨x, (smooth_iff_moments x).mp hx 4⟩

/-- The actual Hamiltonian vacuum evolution, without a pointwise choice of
implementers or phases. Quasifreeness and its beta number identity still
require the actual-propagator covariance theorem. -/
def vacuumEvolution (t : ℝ) : Fock L := V 0 t vac

theorem actual_vacuum_initial_norm_smooth :
    vacuumEvolution B M A hM hA hB hs u₀ 0 = vac ∧
      (∀ t, ‖vacuumEvolution B M A hM hA hB hs u₀ t‖ = 1) ∧
      (∀ t, Smooth (coefficient (vacuumEvolution B M A hM hA hB hs u₀ t))) ∧
      ContDiff ℝ 1 (vacuumEvolution B M A hM hA hB hs u₀) := by
  refine ⟨evolution_self B M A hM hA hB hs u₀ 0 vac, fun t => ?_,
    fun t => (evolution_smooth_iff B M A hM hA hB hs u₀ 0 t vac).mpr vacuum_smooth, ?_⟩
  · change ‖(evolution B M A hM hA hB hs u₀ 0 t) vac‖ = 1
    rw [LinearIsometry.norm_map, vac, physCore_ket, LinearIsometryEquiv.norm_map,
      lp.norm_single (by norm_num)]
    exact norm_one
  · exact Prop022StrongEquationR125.evolution_C1 B M A hM hA hB hs u₀ 0
      ⟨vac, (smooth_iff_moments vac).mp vacuum_smooth 4⟩

end QuantumNLS.Prop022SmoothDomainR126
#print axioms QuantumNLS.Prop022SmoothDomainR126.coefficient_moment_iff
#print axioms QuantumNLS.Prop022SmoothDomainR126.smooth_iff_moments
#print axioms QuantumNLS.Prop022SmoothDomainR126.evolution_smooth_iff
#print axioms QuantumNLS.Prop022SmoothDomainR126.evolution_smooth_hasDerivAt
#print axioms QuantumNLS.Prop022SmoothDomainR126.actual_vacuum_initial_norm_smooth

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022SmoothDomainR126." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022SmoothDomainR126." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R126 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
