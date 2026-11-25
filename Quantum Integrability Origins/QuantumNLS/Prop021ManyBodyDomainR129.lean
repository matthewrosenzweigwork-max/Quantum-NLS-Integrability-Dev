import QuantumNLS.Prop021ManyBodyR129
import QuantumNLS.Ext005FormCutoffR109
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Maximal-domain dynamics for the literal Q7B many-body direct sum.
There is no uniform bound on sector Hamiltonians. Finite sector truncations
converge together with their derivatives in physical Hilbert norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology
open Filter
namespace QuantumNLS.Prop021ManyBodyDomainR129
open BetheCoefficientTransform Ext025B3PhysicalSectors Prop021ManyBodyR129
open Ext005FormCutoffR109 LinearTailPhysicalEvolution
variable {L : ℝ} [Fact (0 < L)]
variable (B : ∀ m, HN L m →L[ℂ] HN L m)
  (hB : ∀ m, (B m).adjoint = B m) (N : ℕ)
local notation "E" => manyBodyEvolution B hB N
local notation "H" => hamiltonian B N

lemma bounded_evolution_commutes {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (A : K →L[ℂ] K) (t : ℝ) (z : K) :
    A (evolution A t z) = evolution A t (A z) := by
  let : NormedAlgebra ℚ (K →L[ℂ] K) := .restrictScalars ℚ ℂ (K →L[ℂ] K)
  have hc : Commute A ((t : ℂ) • ((-Complex.I) • A)) := by
    change A * ((t : ℂ) • ((-Complex.I) • A)) = ((t : ℂ) • ((-Complex.I) • A)) * A
    apply ContinuousLinearMap.ext
    intro y
    change A ((t : ℂ) • ((-Complex.I) • A y)) = (t : ℂ) • ((-Complex.I) • A (A y))
    rw [map_smul, map_smul]
  have he := hc.exp_right
  exact congrArg (fun T : K →L[ℂ] K => T z) he.eq

lemma sector_commutes (n : ℕ) (t : ℝ) (z : HN L n) :
    sector B N n (evolution (sector B N n) t z) =
      evolution (sector B N n) t (sector B N n z) :=
  bounded_evolution_commutes (sector B N n) t z

/-- Maximal domain invariance uses exact sector commutation and isometry. -/
lemma evolution_mem_domain (x : (H).domain) (t : ℝ) : E t x.val ∈ (H).domain := by
  apply Memℓp.of_norm
  have he (n : ℕ) : ‖sector B N n (E t x.val n)‖ = ‖sector B N n (x.val n)‖ := by
    rw [manyBodyEvolution_apply, sector_commutes]
    exact evolution_norm (show IsSelfAdjoint (sector B N n) from sector_adjoint B hB N n) t _
  simpa only [he] using x.property.norm

lemma hamiltonian_commutes (x : (H).domain) (t : ℝ) :
    H ⟨E t x.val, evolution_mem_domain B hB N x t⟩ = E t (H x) := by
  apply lp.ext
  funext n
  exact sector_commutes B N n t (x.val n)

lemma evolve_projection (n : ℕ) (t : ℝ) (x : Fock L) :
    E t (projection L n x) = inclusion L n (evolution (sector B N n) t (x n)) := by
  apply lp.ext
  funext m
  by_cases h : m = n
  · subst m
    simp only [manyBodyEvolution_apply, projection_same]
    change _ = (lp.single 2 n _) n
    simp only [lp.single_apply, Pi.single_eq_same]
  · rw [manyBodyEvolution_apply, projection_other L n m h, map_zero]
    change 0 = (lp.single 2 n _) m
    simp only [lp.single_apply, Pi.single_eq_of_ne h]

/-- Every finite sector truncation of the physical orbit has the actual
Schrodinger derivative, with the maximal direct-sum image of its datum. -/
lemma cutoff_hasDerivAt (x : (H).domain) (J : ℕ) (t : ℝ) :
    HasDerivAt (fun r => E r (cutoff J x.val))
      ((-Complex.I) • E t (cutoff J (H x))) t := by
  have hd (n : ℕ) : HasDerivAt (fun r => E r (projection L n x.val))
      ((-Complex.I) • E t (projection L n (H x))) t := by
    have hv := ((inclusion L n).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_evolution (sector B N n) (x.val n) t)
    have hf : (fun r => E r (projection L n x.val)) =
        (fun r => inclusion L n (evolution (sector B N n) r (x.val n))) :=
      funext (fun r => evolve_projection B hB N n r x.val)
    rw [hf]
    convert! hv using 1
    rw [evolve_projection]
    change (-Complex.I) • inclusion L n (evolution (sector B N n) t (sector B N n (x.val n))) =
      inclusion L n ((-Complex.I) • sector B N n (evolution (sector B N n) t (x.val n)))
    rw [map_smul, sector_commutes]
  have hh := HasDerivAt.sum (u := Finset.range J) (fun n _ => hd n)
  convert! hh using 1
  · funext r
    simp only [cutoff_sum, map_sum, Finset.sum_apply]
  · simp only [cutoff_sum, map_sum, Finset.smul_sum]

lemma orbit_cutoff_uniform (x : Fock L) :
    TendstoUniformly (fun J t => E t (cutoff J x)) (fun t => E t x) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp (cutoff_tendsto x)) ε hε] with J hJ
  intro t
  simpa only [LinearIsometryEquiv.dist_map, dist_comm] using hJ

/-- Strong differentiability on the entire maximal direct-sum domain. -/
theorem manyBody_hasDerivAt (x : (H).domain) (t : ℝ) :
    HasDerivAt (fun r => E r x.val) ((-Complex.I) • E t (H x)) t := by
  have hu : TendstoUniformly (fun J t => (-Complex.I) • E t (cutoff J (H x)))
      (fun t => (-Complex.I) • E t (H x)) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp (cutoff_tendsto (H x))) ε hε] with J hJ
    intro t
    simpa only [dist_smul₀, norm_neg, Complex.norm_I, one_mul,
      LinearIsometryEquiv.dist_map, dist_comm] using hJ
  exact hasDerivAt_of_tendstoUniformly hu
    (Eventually.of_forall (fun J t => cutoff_hasDerivAt B hB N x J t))
    (fun t => (E t).continuous.continuousAt.tendsto.comp (cutoff_tendsto x.val)) t

/-- The derivative is exactly -i H_N applied to the evolving vector, with
its domain membership proved above. -/
theorem manyBody_schrodinger (x : (H).domain) (t : ℝ) :
    HasDerivAt (fun r => E r x.val)
      ((-Complex.I) • H ⟨E t x.val, evolution_mem_domain B hB N x t⟩) t := by
  rw [hamiltonian_commutes]
  exact manyBody_hasDerivAt B hB N x t

end QuantumNLS.Prop021ManyBodyDomainR129
#print axioms QuantumNLS.Prop021ManyBodyDomainR129.evolution_mem_domain
#print axioms QuantumNLS.Prop021ManyBodyDomainR129.manyBody_schrodinger

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ManyBodyDomainR129"].any
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
