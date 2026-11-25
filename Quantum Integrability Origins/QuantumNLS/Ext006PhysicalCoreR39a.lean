import QuantumNLS.Ext006PairOccupationR39a
import QuantumNLS.Ext006PhysicalApproximationR38a
import QuantumNLS.Ext006PhysFockCoord
import QuantumNLS.Ext006KernelHilbertSchmidt

/-! The physical pair-creation block equals two literal occupation-core creators
on every occupation ket, retaining the mass-L Fourier convention. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006PhysicalCoreR39a
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Occupation OccupationUnitary Ext006PhysFockCoord Ext006KernelHilbertSchmidt
open Ext006PairPowerWick Ext006PhysicalNormBridge.PairTensor
open Ext006PhysicalNormBridge.CreationFormula Ext006PhysicalApproximationR38a
open Ext006SymmetricConcatR39a Ext006PairOccupationR39a
variable {L : ℝ} [Fact (0 < L)]

/-- Actual physical occupation ket in its single particle sector. -/
def sectorKet {N : ℕ} (m : Arr N) : HN L N :=
  (physicalOccupation L N).symm (lp.single 2 m 1)

lemma U3_sectorKet {N : ℕ} (m : Arr N) :
    TensorFourier.U3 L N (sectorKet (L := L) m) = basisVector m := by
  apply (U4 N).injective
  change physicalOccupation L N (sectorKet m) = U4 N (basisVector m)
  simp [sectorKet]

lemma fourier_physicalBasis (i : ℤ) :
    Fourier.fourierL2 L (physicalBasis L i) = oneBasis i := by
  change (physicalBasis L).repr (physicalBasis L i) = _
  rw [HilbertBasis.repr_self, oneBasis_apply]

/-- Literal finite physical pair tensors have the expected ordered Fourier factors. -/
lemma fourier_basisPair (i j : ℤ) :
    TensorFourier.fourierTensor L 2
      (basisPair (physicalBasis L) i j : HilbertTensorPower ℂ (L2T L) 2) =
      symProduct (modePair i j) := by
  have hraw : (twoIso (E := L2T L)).symm
      (htmul (physicalBasis L i) (physicalBasis L j)) =
      ((ptprod ![physicalBasis L i, physicalBasis L j] : AlgTensorPower ℂ (L2T L) 2) :
        HilbertTensorPower ℂ (L2T L) 2) := by
    apply (twoIso (E := L2T L)).injective
    rw [LinearIsometryEquiv.apply_symm_apply, twoIso_ptprod]
    rfl
  change TensorFourier.fourierTensor L 2
    ((physSector L 2).starProjection ((twoIso (E := L2T L)).symm
      (htmul (physicalBasis L i) (physicalBasis L j)))) = _
  rw [← symProj_eq_starProjection, hraw, TensorFourier.fourierTensor_symProj,
    TensorFourier.fourierTensor_ptprod]
  unfold symProduct productVector
  simp only [tensorMultilinear_apply]
  congr 3
  funext a
  fin_cases a <;> simp [modePair, fourier_physicalBasis]

/-- Fourier transport of the literal physical creation formula. -/
lemma fourier_creation (b : HN L 2) (N : ℕ) (x : HN L N) :
    TensorFourier.fourierTensor L (2+N)
      (Ext005PairSector.creation b N x : HilbertTensorPower ℂ (L2T L) (2+N)) =
      (Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) : ℂ) •
        symProj ℂ OneParticle (2+N)
          (concat (TensorFourier.fourierTensor L 2 b) (TensorFourier.fourierTensor L N x)) := by
  rw [creation_eq_projection]
  change TensorFourier.fourierTensor L (2+N)
    ((Real.sqrt (((N : ℝ)+1)*((N : ℝ)+2)) : ℂ) •
      (physSector L (2+N)).starProjection (concat
        (b : HilbertTensorPower ℂ (L2T L) 2)
        (x : HilbertTensorPower ℂ (L2T L) N))) = _
  rw [map_smul, ← symProj_eq_starProjection, TensorFourier.fourierTensor_symProj,
    tensorPower_concat]

/-- Two-mode physical action, with both multiplicity factors explicitly proved. -/
theorem creation_basisPair_sectorKet {N : ℕ} (m : Arr N) (i j : ℤ) :
    Ext005PairSector.creation (basisPair (physicalBasis L) i j) N (sectorKet m) =
      ((Real.sqrt ((m.1 j : ℝ)+1) : ℂ) * (Real.sqrt (((m.1+e j) i : ℝ)+1) : ℂ)) •
        sectorKet (pairMode m i j) := by
  apply (TensorFourier.U3 L (2+N)).injective
  apply Subtype.ext
  change TensorFourier.fourierTensor L (2+N) _ =
    TensorFourier.fourierTensor L (2+N) _
  rw [fourier_creation, fourier_basisPair, Submodule.coe_smul, map_smul]
  have h1 : TensorFourier.fourierTensor L N (sectorKet (L := L) m : HilbertTensorPower ℂ (L2T L) N) = occupationVector m :=
    congrArg Subtype.val (U3_sectorKet (L := L) m)
  have h2 : TensorFourier.fourierTensor L (2+N) (sectorKet (L := L) (pairMode m i j) : HilbertTensorPower ℂ (L2T L) (2+N)) =
      occupationVector (pairMode m i j) :=
    congrArg Subtype.val (U3_sectorKet (L := L) (pairMode m i j))
  rw [h1, h2]
  exact two_mode_creation m i j

/-- The finite-support physical core ket really is the sector occupation tensor. -/
theorem physCore_ket_sector {N : ℕ} (m : Arr N) :
    physCore (L := L) (ket m.1) = inclusion L N (sectorKet m) := by
  classical
  apply (Phi (L := L)).injective
  rw [physCore_ket, LinearIsometryEquiv.apply_symm_apply]
  apply lp.ext
  funext v
  change (lp.single 2 m.1 (1 : ℂ) : Ext006VacuumRecurrence.Fock) v = Ext006PhysicalVacuum.coefficient
    (inclusion L N (sectorKet m)) v
  by_cases h : total v = N
  · subst N
    simp only [Ext006PhysicalVacuum.coefficient]
    have hi : (inclusion L (total v) (sectorKet (L := L) m)) (total v) = sectorKet m :=
      lp.single_apply_self _ _ _
    rw [hi]
    change (lp.single 2 m.1 (1 : ℂ) : Ext006VacuumRecurrence.Fock) v =
      occupationCoefficient (freeBasis L (total v)) (sectorKet m) ⟨v,rfl⟩
    rw [occupationCoefficient_free]
    simp [sectorKet, lp.single_apply, Pi.single_apply, Subtype.ext_iff]
  · have hz : (inclusion L N (sectorKet m)) (total v) = 0 := by
      exact lp.single_apply_ne _ _ _ h
    simp only [Ext006PhysicalVacuum.coefficient, hz, map_zero, lp.coeFn_zero,
      Pi.zero_apply]
    apply lp.single_apply_ne
    intro hvm
    exact h ((congrArg total hvm).trans m.2)

/-- Equality with TWO literal frozen CCR core creators; no core action is a premise. -/
theorem physical_pair_core_ket {N : ℕ} (m : Arr N) (i j : ℤ) :
    inclusion L (2+N)
      (Ext005PairSector.creation (basisPair (physicalBasis L) i j) N (sectorKet m)) =
      physCore (L := L) (Cre i (Cre j (ket m.1))) := by
  simp only [creation_basisPair_sectorKet, map_smul, Cre_ket, smul_smul]
  exact congrArg (fun x : Fock L =>
    ((Real.sqrt ((m.1 j : ℝ)+1) : ℂ) * (Real.sqrt (((m.1+e j) i : ℝ)+1) : ℂ)) • x)
    (physCore_ket_sector (L := L) (pairMode m i j)).symm

end QuantumNLS.Ext006PhysicalCoreR39a

#print axioms QuantumNLS.Ext006PhysicalCoreR39a.fourier_basisPair

#print axioms QuantumNLS.Ext006PhysicalCoreR39a.creation_basisPair_sectorKet

#print axioms QuantumNLS.Ext006PhysicalCoreR39a.physCore_ket_sector

#print axioms QuantumNLS.Ext006PhysicalCoreR39a.physical_pair_core_ket

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalCoreR39a." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Round39a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
