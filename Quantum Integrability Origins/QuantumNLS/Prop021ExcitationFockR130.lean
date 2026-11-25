import QuantumNLS.Prop021ExcitationR130
import QuantumNLS.Prop021SectorTransferR128
import QuantumNLS.Prop021QuadraticR130
import QuantumNLS.Prop021ManyBodySelfAdjointR129
import QuantumNLS.Ext005MomentEnergyR108
import QuantumNLS.Ext006NumberPhase

/-! The physical maximal direct-sum excitation root, its exact number-sector
commutation, and domination by the actual number expectation. Weyl
commutation is a separate obligation, not a supplied premise here. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 10000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal
namespace QuantumNLS.Prop021ExcitationFockR130
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop021ExcitationR130 Ext005Moments Ext006NumberPhase
variable {L : ℝ} [Fact (0 < L)]

/-- Literal maximal direct sum of the nonnegative sector excitation roots. -/
def root (u : L2T L) : Fock L →ₗ.[ℂ] Fock L := block (excitationRoot u)

/-- Literal dGamma(1-|u><u|), with the source average placement. -/
def D (u : L2T L) : Fock L →ₗ.[ℂ] Fock L := block (excitation u)

/-- No smaller domain is substituted for either maximal operator. -/
theorem root_selfAdjoint (u : L2T L) : IsSelfAdjoint (root u) :=
  Prop021ManyBodySelfAdjointR129.block_selfAdjoint (excitationRoot u)
    (fun n => (excitationRoot_positive u n).isSelfAdjoint.adjoint_eq)

theorem D_selfAdjoint (u : L2T L) (hu : ‖u‖=1) : IsSelfAdjoint (D u) :=
  Prop021ManyBodySelfAdjointR129.block_selfAdjoint (excitation u)
    (fun n => (excitation_positive u hu n).isSelfAdjoint.adjoint_eq)

lemma number_summable (x : Fock L) (hx : x ∈ momentDomain (L := L) 1) :
    Summable (fun n : ℕ => (n:ℝ)*‖x n‖^2) := by
  have hs := (momentDomain_iff 1 x).mp hx
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => by simp only [momentWeight,pow_one]; nlinarith [sq_nonneg ‖x n‖]) hs

/-- The source number expectation agrees with the real sector sum whenever
the first moment has been proved finite. -/
theorem numberExpectation_eq (x : Fock L) (hx : x ∈ momentDomain (L := L) 1) :
    numberExpectation (fun n => (n:ℝ≥0∞)) x =
      ENNReal.ofReal (∑' n : ℕ, (n:ℝ)*‖x n‖^2) := by
  rw [numberExpectation, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (number_summable x hx)]
  apply tsum_congr
  intro n
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  simp

/-- Every first-number-moment vector belongs to the ACTUAL maximal
excitation-root domain. This includes the evolving quadratic vacuum. -/
theorem moment_mem_root (u : L2T L) (hu : ‖u‖=1) (x : Fock L)
    (hx : x ∈ momentDomain (L := L) 1) : x ∈ (root u).domain := by
  change Memℓp (fun n => excitationRoot u n (x n)) 2
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun n => excitationRoot_bound u hu n (x n)) (number_summable x hx)

/-- Domination by the printed number expectation, not by number plus one. -/
theorem root_number_bound (u : L2T L) (hu : ‖u‖=1) (x : Fock L)
    (hx : x ∈ momentDomain (L := L) 1) :
    ‖root u ⟨x,moment_mem_root u hu x hx⟩‖^2 ≤
      (numberExpectation (fun n => (n:ℝ≥0∞)) x).toReal := by
  rw [numberExpectation_eq x hx, ENNReal.toReal_ofReal (tsum_nonneg (fun _ => by positivity))]
  have he := (lp.hasSum_norm (p := 2) (by norm_num) (root u ⟨x,moment_mem_root u hu x hx⟩))
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at he
  rw [← he.tsum_eq]
  exact he.summable.tsum_le_tsum (fun n => excitationRoot_bound u hu n (x n))
    (number_summable x hx)

/-- Every sector projection preserves the full maximal root domain and
commutes with the actual unbounded root. -/
theorem root_projection (u : L2T L) (N : ℕ) (x : (root u).domain) :
    root u ⟨projection L N x,projection_mem_blockDomain (excitationRoot u) N x⟩ =
      projection L N (root u x) := block_commutes (excitationRoot u) N x

/-- The root of the projected vector cannot increase the full root norm. -/
theorem root_projected_bound (u : L2T L) (N : ℕ) (x : (root u).domain) :
    ‖root u ⟨projection L N x,projection_mem_blockDomain (excitationRoot u) N x⟩‖ ≤
      ‖root u x‖ := by
  rw [root_projection]
  exact projection_norm_le L N _

/-- The exact N-sector contraction is the root of D_N divided by sqrt(N). -/
theorem normalized_root (u : L2T L) (N : ℕ) (hN : 1 ≤ N) (x : HN L N) :
    contraction u N x = (Real.sqrt (N:ℝ))⁻¹ • excitationRoot u N x := by
  have hs : Real.sqrt (N:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega)))
  have hr : (Real.sqrt (N:ℝ):ℂ) • contraction u N x =
      Real.sqrt (N:ℝ) • contraction u N x :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.sqrt (N:ℝ)) (contraction u N x)).symm
  change contraction u N x = (Real.sqrt (N:ℝ))⁻¹ • ((Real.sqrt (N:ℝ):ℂ) • contraction u N x)
  rw [hr,smul_smul,inv_mul_cancel₀ hs,one_smul]

open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022VariationalR123
open Prop021QuadraticBindingR129 Prop021QuadraticR130
variable (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (hs : ∀ m, (B m).adjoint = B m)
    (u₀ : Prop001.Sphere (L2T L))
local notation "u" => profile B M A hA hB hs u₀
local notation "ξ" => fluctuation B M A hM hA hB hs u₀

/-- Domain membership of the actual evolving vacuum for the excitation
root at the actual moving condensate. Both moment and unit-norm premises
are discharged by the constructed quadratic and classical evolutions. -/
theorem actual_vacuum_mem_root (t : ℝ) : ξ t ∈ (root (u t)).domain := by
  have hu := (profile_spec B M A hA hB hs u₀).2.2.1 t
  have hx := (fluctuation_initial_norm_smooth B M A hM hA hB hs u₀).2.2.1 t
  exact moment_mem_root (u t) hu (ξ t)
    ((Prop021DisplacementR129.common_domain (ξ t)).mp hx 1)

/-- The actual root on the actual vacuum, with a proved graph-domain lift. -/
def vacuumRoot (t : ℝ) : Fock L :=
  root (u t) ⟨ξ t,actual_vacuum_mem_root B M A hM hA hB hs u₀ t⟩

/-- Uniform excitation bound for the same vacuum as in the strong
quadratic equation and exact original-beta identity. -/
theorem vacuumRoot_bound (T P : ℝ) (hT : 0 ≤ T) (hP : 1 ≤ P)
    (hS : ∀ r q : ℝ, |r| ≤ T → |q| ≤ T →
      ‖(flow B M A hA hB hs u₀ r q).toContinuousLinearMap‖ ≤ P)
    (t : ℝ) (ht : |t| ≤ T) :
    ‖vacuumRoot B M A hM hA hB hs u₀ t‖^2 ≤
      Prop021RatesR128.numberParameter (Prop022FactorialMajorantR115.pairMajorant A) T M P-1 := by
  have hu := (profile_spec B M A hA hB hs u₀).2.2.1 t
  have hx := (fluctuation_initial_norm_smooth B M A hM hA hB hs u₀).2.2.1 t
  have hnum := root_number_bound (u t) hu (ξ t)
    ((Prop021DisplacementR129.common_domain (ξ t)).mp hx 1)
  exact hnum.trans (quadratic_depletion B M A hM hA hB hs u₀ T P hT hP hS t ht)

end QuantumNLS.Prop021ExcitationFockR130
#print axioms QuantumNLS.Prop021ExcitationFockR130.root_selfAdjoint
#print axioms QuantumNLS.Prop021ExcitationFockR130.D_selfAdjoint
#print axioms QuantumNLS.Prop021ExcitationFockR130.moment_mem_root
#print axioms QuantumNLS.Prop021ExcitationFockR130.root_number_bound
#print axioms QuantumNLS.Prop021ExcitationFockR130.root_projection
#print axioms QuantumNLS.Prop021ExcitationFockR130.actual_vacuum_mem_root
#print axioms QuantumNLS.Prop021ExcitationFockR130.vacuumRoot_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021ExcitationFockR130"].any
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
