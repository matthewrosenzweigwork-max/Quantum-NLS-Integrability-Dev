import QuantumNLS.Ext006BD02R44a
import QuantumNLS.Prop022SmoothDomainR126

/-! Physical Q7B displacement W(v)=exp(a*(v)-a(v)) from the accepted
source Stone exponential exp(i(a*(f)+a(f))), with f=-iv. This module fixes
the normalization and proves strong radial differentiation on the common
number-moment domain. Moving-center differentiation is a later obligation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace Topology
namespace QuantumNLS.Prop021DisplacementR129
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext006PhysFockCoord Ext006KernelHilbertSchmidt Ext006SourceWeylR44a
open Ext006GlobalCovarianceR43a Ext006WeylScalingR44a
open Ext006SmoothOperatorsR34a Ext006StrongFieldR41a Ext006ModeDomainR33a
variable {L : ℝ} [Fact (0 < L)]
attribute [local instance] InnerProductSpace.complexToReal

/-- The Q7B physical convention, constructed from the accepted source group. -/
def displacement (v : L2T L) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  sourceWeyl ((-Complex.I) • v)

lemma ray_eq (v : L2T L) (t : ℝ) (x : Fock L) :
    displacement ((t : ℂ) • v) x = physicalExponential ((-Complex.I) • v) t x := by
  rw [displacement, sourceWeyl_eq]
  have he : (-Complex.I) • ((t : ℂ) • v) = t • ((-Complex.I) • v) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact smul_comm (-Complex.I) (t : ℂ) v
  rw [he, physical_real_smul]

/-- All real scalar parameters share the same literal Stone generator. -/
theorem displacement_ray_continuous (v : L2T L) (x : Fock L) :
    Continuous (fun t : ℝ => displacement ((t : ℂ) • v) x) := by
  simp_rw [ray_eq]
  exact physicalExponential_strong_continuous _ _

lemma displacement_ray_zero (v : L2T L) (x : Fock L) :
    displacement ((0 : ℂ) • v) x = x := by
  calc
    displacement ((0 : ℂ) • v) x = physicalExponential ((-Complex.I) • v) 0 x := by
      simpa only [Complex.ofReal_zero] using ray_eq v 0 x
    _ = x := by
      rw [physicalExponential_apply, Ext006SeriesIdentificationR43a.unitary_zero,
        LinearIsometryEquiv.symm_apply_apply]

def smoothLift (x : Fock L) (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) : D :=
  ⟨Phi x, hx⟩

/-- The common physical domain is precisely the intersection of all
positive number-moment domains, by the frozen R126 Parseval theorem. -/
theorem common_domain (x : Fock L) :
    Smooth (Ext006PhysicalVacuum.coefficient x) ↔
      ∀ j : ℕ, x ∈ Ext005Moments.momentDomain (L := L) j :=
  Prop022SmoothDomainR126.smooth_iff_moments x

/-- Actual normalized creation minus annihilation, transported to physical Fock. -/
def generator (v : L2T L) (x : Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) : Fock L :=
  (Phi (L := L)).symm
    (((C ((physicalBasis L).repr v)-A ((physicalBasis L).repr v)) (smoothLift x hx)).val)

lemma rotated_field (h : Ext006BogoliubovAlg.H) :
    Complex.I • field ((-Complex.I) • h) = C h-A h := by
  rw [field, Ext006InverseGraphsR36a.A_smul, Ext006InverseGraphsR36a.C_smul]
  simp only [Complex.star_def, map_neg, Complex.conj_I, neg_neg, smul_add, smul_smul,
    Complex.I_mul_I, mul_neg, neg_neg, one_smul]
  module

lemma generator_rotation (v : L2T L) (x : Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) :
    generator v x hx = (Phi (L := L)).symm
      (Complex.I • (field ((physicalBasis L).repr ((-Complex.I) • v)) (smoothLift x hx)).val) := by
  have hr : (physicalBasis L).repr ((-Complex.I) • v) =
      (-Complex.I) • (physicalBasis L).repr v := map_smul _ _ _
  rw [hr]
  have he := congrArg (fun T : Module.End ℂ D => (T (smoothLift x hx)).val)
    (rotated_field ((physicalBasis L).repr v))
  change (Complex.I • field ((-Complex.I) • (physicalBasis L).repr v) (smoothLift x hx)).val = _ at he
  exact congrArg (Phi (L := L)).symm he.symm

/-- Strong derivative of the actual spectral Weyl displacement on every
common moment vector. No field-domain or derivative premise is supplied. -/
theorem displacement_ray_hasDerivAt (v : L2T L) (x : Fock L)
    (hx : Smooth (Ext006PhysicalVacuum.coefficient x)) (t : ℝ) :
    HasDerivAt (fun r : ℝ => displacement ((r : ℂ) • v) x)
      (displacement ((t : ℂ) • v) (generator v x hx)) t := by
  let h := (physicalBasis L).repr ((-Complex.I) • v)
  let w := smoothLift x hx
  have hg : (w.val, (field h w).val) ∈ Ext006FieldClosureR42a.closedFieldGraph h :=
    subset_closure ⟨w, rfl⟩
  have hd := Ext006StoneGeneratorR44a.graph_hasDerivAt h w.val (field h w).val hg t
  have hp := ((Phi (L := L)).symm.toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt
    (fun r => (Phi (L := L)).symm (Ext006BoundedExponentialR43a.unitary h r (Phi x)))
    ((Phi (L := L)).symm (Complex.I • Ext006BoundedExponentialR43a.unitary h t (field h w).val)) t at hp
  simpa only [ray_eq, physicalExponential_apply, generator_rotation,
    LinearIsometryEquiv.apply_symm_apply, map_smul, h, w] using hp

/-- Source covariance in the displacement convention includes the explicit
complex-structure conjugation v ↦ i S(-iv). -/
theorem displacement_covariance
    (S : L2T L ≃L[ℝ] L2T L) (U : Fock L ≃ₗᵢ[ℂ] Fock L)
    (hU : SourceWeylImplementer S U) (v : L2T L) (x : Fock L) :
    U (displacement v (U.symm x)) = displacement (Complex.I • S ((-Complex.I) • v)) x := by
  rw [displacement, hU, displacement]
  congr 2
  simp only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

end QuantumNLS.Prop021DisplacementR129
#print axioms QuantumNLS.Prop021DisplacementR129.displacement_ray_hasDerivAt
#print axioms QuantumNLS.Prop021DisplacementR129.displacement_covariance

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021DisplacementR129"].any
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
