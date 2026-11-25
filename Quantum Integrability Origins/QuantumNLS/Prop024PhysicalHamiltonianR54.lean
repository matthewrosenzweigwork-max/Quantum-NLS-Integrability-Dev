import QuantumNLS.Ext025B3PhysicalSectors
import QuantumNLS.PhysicalPlacements
import QuantumNLS.PlacementConsistency
import QuantumNLS.GenericUAdjoint
import QuantumNLS.Prop022FactorialCoefficientsR115

/-! Round 54 PROP-024: the fixed-N factorial interaction on the actual
physical Fock space.  The finite-sector placement is the existing physical
DEF-041 placement, and the full operator is its maximal Hilbert direct sum.
This module supplies the concrete Hamiltonian interface needed for the
subsequent Weyl/Wick comparison; it makes no translation claim. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.Prop024PhysicalHamiltonianR54

attribute [local instance] InnerProductSpace.complexToReal

open BetheCoefficientTransform Ext025B3PhysicalSectors PhysicalTensor
open PhysicalPlacements KernelDefinition GenericUAdjoint
open Prop022FactorialCoefficientsR115

variable {L : ℝ} [Fact (0 < L)]

/-- The source falling-factorial coefficient `(N)_m/N^m`. -/
def fallingScale (N n m : ℕ) : ℝ :=
  (n.descFactorial m : ℝ) / (N : ℝ) ^ m

/-- The exact bounded restriction of the printed interaction `H_N` to the
`n`-particle sector.  The external mean-field parameter `N` is held fixed
while `n` ranges over the Fock direct sum. -/
def interactionSector (N n : ℕ)
    (B : ∀ m, HN L m →L[ℂ] HN L m) : HN L n →L[ℂ] HN L n :=
  (N : ℂ) • ∑ k : Fin n,
    ((fallingScale N n (k.val + 1) : ℝ) : ℂ) •
      physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1))

/-- `H_N` on the completed physical Fock space.  Its domain is exactly the
maximal direct-sum domain for the actual bounded sector operators. -/
def interaction (N : ℕ) (B : ∀ m, HN L m →L[ℂ] HN L m) : Fock L →ₗ.[ℂ] Fock L :=
  Ext025B3PhysicalSectors.block (fun n => interactionSector N n B)

theorem fallingScale_nonneg (N n m : ℕ) : 0 ≤ fallingScale N n m := by
  unfold fallingScale
  positivity

/-- The physical placement preserves adjoints, by its identified generic
placement representation. -/
theorem physicalQ_adjoint (n m : ℕ) (hm : m ≤ n)
    (A : HN L m →L[ℂ] HN L m) :
    (physicalQ_N_p L n m hm A).adjoint = physicalQ_N_p L n m hm A.adjoint := by
  change (KernelDefinition.physicalU_N_r L n m hm A).adjoint =
    KernelDefinition.physicalU_N_r L n m hm A.adjoint
  rw [PlacementConsistency.physicalU_N_r_eq_genericU_N_r L n m hm A,
    GenericUAdjoint.adjoint_genericU_N_r,
    PlacementConsistency.physicalU_N_r_eq_genericU_N_r L n m hm A.adjoint]

/-- Self-adjoint interaction kernels produce self-adjoint sector
restrictions, with the source falling-factorial coefficients. -/
theorem interactionSector_selfAdjoint (N n : ℕ)
    (B : ∀ m, HN L m →L[ℂ] HN L m)
    (hB : ∀ m, (B m).adjoint = B m) :
    IsSelfAdjoint (interactionSector N n B) := by
  unfold interactionSector
  apply IsSelfAdjoint.smul (by simp [isSelfAdjoint_iff])
  exact isSelfAdjoint_sum (R := HN L n →L[ℂ] HN L n)
    (x := fun k : Fin n =>
      ((fallingScale N n (k.val + 1) : ℝ) : ℂ) •
        physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1)))
    Finset.univ (fun k _ =>
      (show IsSelfAdjoint ((fallingScale N n (k.val + 1) : ℝ) : ℂ) from by
        simp [isSelfAdjoint_iff]).smul
        (show IsSelfAdjoint
          (physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1))) from by
            change (physicalQ_N_p L n (k.val + 1) (by omega)
              (B (k.val + 1))).adjoint = _
            rw [physicalQ_adjoint]
            exact congrArg
              (physicalQ_N_p L n (k.val + 1) (by omega))
              (hB (k.val + 1))))

/-- Operator comparison on each physical sector, with the exact source
falling-factorial weights. -/
theorem interactionSector_norm_le (N n : ℕ)
    (B : ∀ m, HN L m →L[ℂ] HN L m) :
    ‖interactionSector N n B‖ ≤
      (N : ℝ) * ∑ k : Fin n,
        fallingScale N n (k.val + 1) * ‖B (k.val + 1)‖ := by
  have hterm (k : Fin n) (x : HN L n) :
      ‖(((fallingScale N n (k.val + 1) : ℝ) : ℂ) •
          physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1))) x‖ ≤
        (fallingScale N n (k.val + 1) * ‖B (k.val + 1)‖) * ‖x‖ := by
    rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fallingScale_nonneg N n (k.val + 1))]
    calc
      fallingScale N n (k.val + 1) *
          ‖physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1)) x‖ ≤
        fallingScale N n (k.val + 1) *
          (‖physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1))‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _)
          (fallingScale_nonneg N n (k.val + 1))
      _ ≤ fallingScale N n (k.val + 1) *
          (‖B (k.val + 1)‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (norm_physicalQ_N_p_le L n (k.val + 1) (by omega) (B (k.val + 1)))
            (norm_nonneg x)) (fallingScale_nonneg N n (k.val + 1))
      _ = _ := by ring
  unfold interactionSector
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    apply mul_nonneg (Nat.cast_nonneg N)
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (fallingScale_nonneg N n (k.val + 1))
      (norm_nonneg (B (k.val + 1))))
  intro x
  change ‖(((N : ℂ) •
      (∑ k : Fin n,
        ((fallingScale N n (k.val + 1) : ℝ) : ℂ) •
          physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1)))) x)‖ ≤ _
  rw [smul_apply, norm_smul, Complex.norm_natCast]
  rw [sum_apply]
  calc
    (N : ℝ) * ‖∑ k : Fin n,
        (((fallingScale N n (k.val + 1) : ℝ) : ℂ) •
          physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1))) x‖ ≤
        (N : ℝ) * ∑ k : Fin n,
          ‖(((fallingScale N n (k.val + 1) : ℝ) : ℂ) •
            physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1))) x‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sum_le (Finset.univ : Finset (Fin n)) (fun k : Fin n =>
          (((fallingScale N n (k.val + 1) : ℝ) : ℂ) •
            physicalQ_N_p L n (k.val + 1) (by omega) (B (k.val + 1))) x))
        (Nat.cast_nonneg N)
    _ ≤ (N : ℝ) * ∑ k : Fin n,
          (fallingScale N n (k.val + 1) * ‖B (k.val + 1)‖) * ‖x‖ := by
      gcongr with k
      exact hterm k x
    _ = ((N : ℝ) * ∑ k : Fin n,
          fallingScale N n (k.val + 1) * ‖B (k.val + 1)‖) * ‖x‖ := by
      rw [← Finset.sum_mul]
      ring

/-- Exact maximal-domain membership criterion for the full physical
interaction. -/
theorem interaction_mem_domain_iff (N : ℕ)
    (B : ∀ m, HN L m →L[ℂ] HN L m) (x : Fock L) :
    x ∈ (interaction N B).domain ↔
      Memℓp (fun n => interactionSector N n B (x n)) 2 := by
  change Memℓp (fun n => interactionSector N n B (x n)) 2 ↔ _
  exact Iff.rfl

/-- Every homogeneous finite-sector vector belongs to the maximal domain;
this is the finite-cutoff starting point for the full translated-vector
domain argument. -/
theorem projection_mem_interaction_domain (N n : ℕ)
    (B : ∀ m, HN L m →L[ℂ] HN L m) (x : Fock L) :
    projection L n x ∈ (interaction N B).domain :=
  Ext025B3PhysicalSectors.projection_mem_blockDomain
    (fun j => interactionSector N j B) n x

/-- The interaction acts sectorwise exactly as the printed bounded
restriction, with no hidden extension beyond its maximal domain. -/
@[simp] theorem interaction_apply_sector (N : ℕ)
    (B : ∀ m, HN L m →L[ℂ] HN L m)
    (x : (interaction N B).domain) (n : ℕ) :
    interaction N B x n = interactionSector N n B (x.val n) := by
  change Ext025B3PhysicalSectors.block (fun j => interactionSector N j B) x n = _
  exact Ext025B3PhysicalSectors.block_apply
    (fun j => interactionSector N j B) x n

end QuantumNLS.Prop024PhysicalHamiltonianR54

#print axioms QuantumNLS.Prop024PhysicalHamiltonianR54.interactionSector
#print axioms QuantumNLS.Prop024PhysicalHamiltonianR54.interactionSector_selfAdjoint
#print axioms QuantumNLS.Prop024PhysicalHamiltonianR54.interaction_mem_domain_iff
#print axioms QuantumNLS.Prop024PhysicalHamiltonianR54.projection_mem_interaction_domain
#print axioms QuantumNLS.Prop024PhysicalHamiltonianR54.interactionSector_norm_le

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop024PhysicalHamiltonianR54." ||
        n.toString.startsWith "_private.QuantumNLS.Prop024PhysicalHamiltonianR54." then
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
  Lean.logInfo m!"R54 physical Hamiltonian aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."

