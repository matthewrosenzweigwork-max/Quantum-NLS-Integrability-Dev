import QuantumNLS.Ext005PhysicalNumberFormR114
import QuantumNLS.GenericUAdjoint

/-! Symmetry of the actual assembled physical quadratic form, derived from
the source one-body self-adjointness and the placement/adjoint definitions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005PhysicalSymmetryR114
open Ext005PhysicalNumberFormR114 Ext005PhysicalHalfPairR114 Ext005QuadraticEnergyR108
open Ext005Moments Ext005FormScaleR109 Ext025B3PhysicalSectors BetheCoefficientTransform
open TensorCarrier TensorPlacements PhysicalTensor
variable {L : ℝ} [Fact (0 < L)]

lemma cast_adjoint {m n : ℕ} (h : m = n)
    (a : SymSector ℂ (L2T L) m →L[ℂ] SymSector ℂ (L2T L) m) :
    (PhysicalPlacements.castSymSectorOperator L h a).adjoint =
      PhysicalPlacements.castSymSectorOperator L h a.adjoint := by
  cases h
  rfl

lemma physicalQ_adjoint (n p : ℕ) (hp : p ≤ n)
    (a : HN L p →L[ℂ] HN L p) :
    (PhysicalPlacements.physicalQ_N_p L n p hp a).adjoint =
      PhysicalPlacements.physicalQ_N_p L n p hp a.adjoint := by
  unfold PhysicalPlacements.physicalQ_N_p
  rw [cast_adjoint]
  congr 1
  rw [← KernelDefinition.U_N_r_eq_Q_N_p, GenericUAdjoint.adjoint_U_N_r,
    KernelDefinition.U_N_r_eq_Q_N_p]

lemma numberBlock_adjoint (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) :
    (numberBlock a n).adjoint = numberBlock a.adjoint n := by
  unfold numberBlock
  split_ifs with hn
  · rw [map_smulₛₗ, physicalQ_adjoint]
    simp only [map_natCast]
  · exact map_zero _

lemma numberContinuous_symmetric (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (u v : Fock L) :
    starRingEnd ℂ (numberContinuous a u v) = numberContinuous a v u := by
  rw [numberContinuous_offDiagonal, numberContinuous_offDiagonal, Complex.conj_tsum]
  apply tsum_congr
  intro n
  rw [inner_conj_symm]
  have hs := (numberBlock a n).adjoint_inner_left (embedding 1 v n) (embedding 1 u n)
  rw [numberBlock_adjoint, ha] at hs
  exact hs

lemma quadraticContinuous_symmetric (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (b : HN L 2) (u v : Fock L) :
    starRingEnd ℂ (quadraticContinuous a b u v) = quadraticContinuous a b v u := by
  change starRingEnd ℂ (numberContinuous a u v + halfPair b u v) =
    numberContinuous a v u + halfPair b v u
  rw [map_add, numberContinuous_symmetric a ha, halfPair_symmetric]

/-- The full static form retains the actual physical first-moment estimate. -/
lemma quadraticContinuous_diagonal_bound (a : HN L 1 →L[ℂ] HN L 1)
    (b : HN L 2) (u : Fock L) :
    ‖quadraticContinuous a b u u‖ ≤ (‖a‖ + ‖b‖) * ‖u‖ ^ 2 := by
  rw [quadraticContinuous_diagonal]
  have hb := quadraticForm_bound a b ⟨embedding 1 u, embedding_mem 1 u⟩
  exact hb.trans_eq (congrArg (fun r : ℝ => (‖a‖ + ‖b‖) * r) (energy_embedding 1 u))

end QuantumNLS.Ext005PhysicalSymmetryR114
#print axioms QuantumNLS.Ext005PhysicalSymmetryR114.physicalQ_adjoint
#print axioms QuantumNLS.Ext005PhysicalSymmetryR114.quadraticContinuous_symmetric
#print axioms QuantumNLS.Ext005PhysicalSymmetryR114.quadraticContinuous_diagonal_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalSymmetryR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalSymmetryR114." then
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
  Lean.logInfo m!"R114 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
