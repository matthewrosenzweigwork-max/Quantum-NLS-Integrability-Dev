import QuantumNLS.Prop021ManyBodyDomainR129
import QuantumNLS.Prop021ManyBodySelfAdjointR129

/-! Strongly continuous unitary group of the literal Q7B maximal Hamiltonian.
The group law is exact sectorwise; continuity uses the Hilbert direct sum
approximation. No moment bound on the initial Fock vector is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology
namespace QuantumNLS.Prop021ManyBodyGroupR129
open BetheCoefficientTransform Ext025B3PhysicalSectors Prop021ManyBodyR129
open Prop021ManyBodyDomainR129 Ext005FormCutoffR109 LinearTailPhysicalEvolution
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m)
  (hB : ∀ m, (B m).adjoint = B m) (N : ℕ)
local notation "E" => manyBodyEvolution B hB N

lemma manyBody_zero (x : Fock L) : E 0 x = x := by
  apply lp.ext
  funext n
  rw [manyBodyEvolution_apply, evolution_zero, one_apply_eq_self]

lemma bounded_evolution_add {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A : K →L[ℂ] K) (s t : ℝ) :
    evolution A s * evolution A t = evolution A (s+t) := by
  let : NormedAlgebra ℚ (K →L[ℂ] K) := .restrictScalars ℚ ℂ (K →L[ℂ] K)
  have hc : Commute ((s : ℂ) • ((-Complex.I) • A)) ((t : ℂ) • ((-Complex.I) • A)) :=
    ((Commute.refl ((-Complex.I) • A)).smul_left (s : ℂ)).smul_right (t : ℂ)
  rw [evolution, evolution, ← NormedSpace.exp_add_of_commute hc, evolution]
  rw [Complex.ofReal_add, add_smul]

/-- The full group law retains the actual finite placement Hamiltonians. -/
theorem manyBody_add (s t : ℝ) (x : Fock L) : E s (E t x) = E (s+t) x := by
  apply lp.ext
  funext n
  simp only [manyBodyEvolution_apply]
  exact congrArg (fun T : HN L n →L[ℂ] HN L n => T (x n))
    (bounded_evolution_add (sector B N n) s t)

lemma cutoff_mem_hamiltonian (J : ℕ) (x : Fock L) :
    cutoff J x ∈ (hamiltonian B N).domain := by
  rw [cutoff_sum]
  exact (hamiltonian B N).domain.sum_mem
    (fun n _ => projection_mem_blockDomain (sector B N) n x)

/-- Strong continuity on every Fock datum, including vectors outside D(H_N). -/
theorem manyBody_continuous (x : Fock L) : Continuous (fun t => E t x) := by
  have hc (J : ℕ) : Continuous (fun t => E t (cutoff J x)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (manyBody_hasDerivAt B hB N ⟨cutoff J x, cutoff_mem_hamiltonian B N J x⟩ t).continuousAt)
  exact (orbit_cutoff_uniform B hB N x).continuous (Filter.Eventually.of_forall hc).frequently

/-- Two-sided domain invariance follows from the proved inverse group law. -/
theorem manyBody_domain_iff (x : Fock L) (t : ℝ) :
    E t x ∈ (hamiltonian B N).domain ↔ x ∈ (hamiltonian B N).domain := by
  constructor
  · intro hx
    have h := evolution_mem_domain B hB N ⟨E t x,hx⟩ (-t)
    rwa [manyBody_add, neg_add_cancel, manyBody_zero] at h
  · intro hx
    exact evolution_mem_domain B hB N ⟨x,hx⟩ t

end QuantumNLS.Prop021ManyBodyGroupR129
#print axioms QuantumNLS.Prop021ManyBodyGroupR129.manyBody_add
#print axioms QuantumNLS.Prop021ManyBodyGroupR129.manyBody_continuous
#print axioms QuantumNLS.Prop021ManyBodyGroupR129.manyBody_domain_iff

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ManyBodyGroupR129"].any
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
