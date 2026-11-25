import QuantumNLS.BetheTwoParticleAction

/-! The actual completed-tensor degree-one placement in the interacting
two-particle sector. The normalized P₂ average and coefficient 2c are
proved from their existing definitions. Its coordinate slice action remains
to be identified with the integrals in BetheTwoParticleAction. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.BetheTwoParticlePlacement
open TensorCarrier TensorPlacements BethePhysicalTransfer

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem symProj_two_apply (w : HilbertTensorPower ℂ H 2) :
    symProj ℂ H 2 w = (2 : ℂ)⁻¹ • (w +
      (permRep ℂ H 2 (Equiv.swap 0 1) : HilbertTensorPower ℂ H 2 →L[ℂ] _) w) := by
  rw [symProj_eq_factorial_average]
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hn : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  simp [hu, Finset.sum_pair hn, Nat.factorial]

/-- The actual normalized degree-one placement is precisely the half sum
of its two completed-tensor outputs on a symmetric input. -/
theorem placement_one_two (A : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1)
    (v : SymSector ℂ H 2) :
    (totalPlacement 2 1 (by omega) A v : HilbertTensorPower ℂ H 2) =
      (2 : ℂ)⁻¹ • (firstPlacement (q := 1) A v.1 +
        (permRep ℂ H 2 (Equiv.swap 0 1) : HilbertTensorPower ℂ H 2 →L[ℂ] _)
          (firstPlacement (q := 1) A v.1)) := by
  change ((placement (q := 1) A v) : HilbertTensorPower ℂ H 2) = _
  simp only [placement, ContinuousLinearMap.comp_apply, Submodule.adjoint_subtypeL,
    Submodule.coe_orthogonalProjectionOnto_apply, ← symProj_eq_starProjection]
  change symProj ℂ H 2 (firstPlacement (q := 1) A v.1) = _
  exact symProj_two_apply _

end

/-- The actual physical degree-one term on the constructed interacting wave.
No action formula is an input. The slice-integral identification is not
asserted by this structural normalization theorem. -/
theorem degree_one_sourceWave (L : ℝ) [Fact (0 < L)] {c : ℝ} (hc : 0 < c)
    {n : Fin 2 → ℤ} (hn : Antitone n) (z : ℂ) :
    ((transferTerm L 2 c z (1 : Fin 3)) (BetheFiniteNAction.physicalWave L hc hn) :
        HilbertTensorPower ℂ (PhysicalTensor.L2T L) 2) =
      (c : ℂ) • (firstPlacement (q := 1) (physicalKernel L 1 z)
          (BetheFiniteNAction.physicalWave L hc hn).1 +
        (permRep ℂ (PhysicalTensor.L2T L) 2 (Equiv.swap 0 1) :
          HilbertTensorPower ℂ (PhysicalTensor.L2T L) 2 →L[ℂ] _)
          (firstPlacement (q := 1) (physicalKernel L 1 z)
            (BetheFiniteNAction.physicalWave L hc hn).1)) := by
  simp only [transferTerm, Fin.val_one, zero_lt_one, ↓reduceIte,
    pow_one, Nat.descFactorial, Nat.cast_mul, Complex.ofReal_mul,
    smul_apply, Submodule.coe_smul]
  rw [placement_one_two, smul_smul]
  congr 1
  norm_num
  ring

/-- Exact half averaging of the computed physical top-degree raw output.
Together with BFNA1 this fixes the factor multiplying the chamber integral. -/
theorem physicalKernel_two (L : ℝ) [Fact (0 < L)] (z : ℂ)
    (v : SymSector ℂ (PhysicalTensor.L2T L) 2) :
    (physicalKernel L 2 z v : HilbertTensorPower ℂ (PhysicalTensor.L2T L) 2) =
      let w := (PhysicalTensor.physUnitary (L := L) (N := 2)).symm
        (BetheTransferOperators.rawOperator L 2 z (positionInclusion L 2 v))
      (2 : ℂ)⁻¹ • (w + (permRep ℂ (PhysicalTensor.L2T L) 2 (Equiv.swap 0 1) :
        HilbertTensorPower ℂ (PhysicalTensor.L2T L) 2 →L[ℂ] _) w) := by
  have hU : (PhysicalTensor.physUnitary (L := L) (N := 2)).toContinuousLinearEquiv.toContinuousLinearMap.adjoint =
      (PhysicalTensor.physUnitary (L := L) (N := 2)).symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    (PhysicalTensor.physUnitary (L := L) (N := 2)).adjoint_eq_symm
  simp only [physicalKernel, positionInclusion, ContinuousLinearMap.adjoint_comp,
    hU, ContinuousLinearMap.comp_apply]
  rw [Submodule.adjoint_subtypeL, Submodule.coe_orthogonalProjectionOnto_apply,
    ← symProj_eq_starProjection, symProj_two_apply]
  rfl

end QuantumNLS.BetheTwoParticlePlacement

#print axioms QuantumNLS.BetheTwoParticlePlacement.placement_one_two
#print axioms QuantumNLS.BetheTwoParticlePlacement.degree_one_sourceWave

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheTwoParticlePlacement.degree_one_sourceWave]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BethePhysicalTransfer.transferTerm,
      ``QuantumNLS.BethePhysicalTransfer.totalPlacement,
      ``QuantumNLS.BethePhysicalTransfer.physicalKernel,
      ``QuantumNLS.TensorPlacements.firstPlacement,
      ``QuantumNLS.TensorCarrier.htmap,
      ``QuantumNLS.BetheFiniteNAction.physicalWave] do
    unless seen.contains n do throwError "Missing literal route ingredient: {n}"
  for n in seen do
    if n.toString.startsWith "QuantumNLS.BetheOneParticleAction." then
      throwError "Unexpected one-particle action dependency: {n}"
  Lean.logInfo m!"BetheTwoParticlePlacement literal route PASS: {seen.size} transitive constants; author support only, full physical transfer eigenrelation remains open."

#print axioms QuantumNLS.BetheTwoParticlePlacement.symProj_two_apply
#print axioms QuantumNLS.BetheTwoParticlePlacement.physicalKernel_two
