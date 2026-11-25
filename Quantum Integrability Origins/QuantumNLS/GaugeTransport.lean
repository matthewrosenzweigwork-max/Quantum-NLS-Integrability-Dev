import QuantumNLS.OccupationConjugacy

/-!
Generic supplied-phase transport for DEF-025/026, report
3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
Source: chapters/definitions.tex:151–159 and
chapters/core/occupation_transfers.tex:2–9.

The phase is supplied on exactly Arr N. It is not a selected Bethe gauge.
The coefficient convention is D_q^* E D_q, so the coefficient unitary
intertwining the ungauged collective operator with that shift is D_q^* U4.
The physical realization uses the already constructed U3 and U4. No Bethe
wavefunction, U5, completeness theorem, or target-selection assertion occurs.
In particular U3 followed by U4 is the Fourier occupation map, not an
identification with interacting Bethe coefficients. That identification needs
the independently constructed complete normalized Bethe basis (U5); selecting
one sequence before all profiles additionally needs R-D51987CA in
chapters/core/GAUGE_RETARGETING.tex:239–365 and its quantum inputs.
-/

noncomputable section
open scoped InnerProductSpace ComplexConjugate Classical
open QuantumNLS.TensorCarrier QuantumNLS.Occupation QuantumNLS.OccupationUnitary

namespace QuantumNLS.GaugeTransport
open OccupationHilbert OccupationConjugacy

section Phase
variable (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1)

/-- The existing concrete diagonal multiplier, requiring phases only in this sector. -/
def phase : H N →L[ℂ] H N :=
  gauge N (extendSectorGauge N q) (extendSectorGauge_unit N q hq)

@[simp] theorem phase_apply (v : H N) (m : Arr N) :
    phase N q hq v m = q m * v m := by simp [phase]

theorem phase_norm_le : ‖phase N q hq‖ ≤ 1 := gauge_norm_le _ _ _

include hq in
theorem conj_phase_unit (m : Arr N) :
    Complex.normSq ((starRingEnd ℂ) (q m)) = 1 := by simpa using hq m

@[simp] theorem phase_conj_phase (v : H N) :
    phase N (fun m => (starRingEnd ℂ) (q m)) (conj_phase_unit N q hq)
      (phase N q hq v) = v := by
  apply lp.ext
  funext m
  simp only [phase_apply]
  rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (q m)), Complex.mul_conj, hq m]
  simp

@[simp] theorem phase_phase_conj (v : H N) :
    phase N q hq
      (phase N (fun m => (starRingEnd ℂ) (q m)) (conj_phase_unit N q hq) v) = v := by
  apply lp.ext
  funext m
  simp only [phase_apply]
  rw [← mul_assoc, Complex.mul_conj, hq m]
  simp

theorem phase_norm (v : H N) : ‖phase N q hq v‖ = ‖v‖ := by
  have hc (r : Arr N → ℂ) (hr : ∀ m, Complex.normSq (r m) = 1) (w : H N) :
      ‖phase N r hr w‖ ≤ ‖w‖ := by
    calc
      _ ≤ ‖phase N r hr‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right (phase_norm_le N r hr) (norm_nonneg _)
      _ = _ := one_mul _
  apply le_antisymm (hc q hq v)
  simpa only [phase_conj_phase] using
    hc (fun m => (starRingEnd ℂ) (q m)) (conj_phase_unit N q hq) (phase N q hq v)

/-- A constructed diagonal unitary on the complete occupation Hilbert carrier. -/
def phaseUnitary : H N ≃ₗᵢ[ℂ] H N where
  toLinearEquiv :=
    { (phase N q hq).toLinearMap with
      invFun := phase N (fun m => (starRingEnd ℂ) (q m)) (conj_phase_unit N q hq)
      left_inv := phase_conj_phase N q hq
      right_inv := phase_phase_conj N q hq }
  norm_map' := phase_norm N q hq

@[simp] theorem phaseUnitary_apply (v : H N) :
    phaseUnitary N q hq v = phase N q hq v := rfl

@[simp] theorem phaseUnitary_symm_apply (v : H N) :
    (phaseUnitary N q hq).symm v =
      phase N (fun m => (starRingEnd ℂ) (q m)) (conj_phase_unit N q hq) v := rfl

theorem phase_conj_eq_gauge :
    phase N (fun m => (starRingEnd ℂ) (q m)) (conj_phase_unit N q hq) =
      gauge N (fun m => (starRingEnd ℂ) (extendSectorGauge N q m))
        (unitGauge_conj (extendSectorGauge_unit N q hq)) := by
  ext v m
  simp

/-- The supplied-phase conjugacy is with the existing gauged shifts, not a new shift. -/
theorem phaseUnitary_conjugacy (a b : ℤ) :
    (phaseUnitary N q hq).symm.conjStarAlgEquiv (E N a b) = sectorEq N q hq a b := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, phaseUnitary_apply, phaseUnitary_symm_apply,
    sectorEq, OccupationHilbert.Eq, mul_apply_eq_comp]
  rw [phase_conj_eq_gauge N q hq]
  rfl

theorem phaseUnitary_adjoint :
    (phaseUnitary N q hq : H N →L[ℂ] H N).adjoint =
      (phaseUnitary N q hq).symm := (phaseUnitary N q hq).adjoint_eq_symm

end Phase

section Boson
variable (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1)

/-- Actual supplied-phase rephasing on the completed symmetric tensor sector. -/
def bosonPhase : Boson N ≃ₗᵢ[ℂ] Boson N :=
  ((U4 N).trans (phaseUnitary N q hq)).trans (U4 N).symm

theorem bosonPhase_basis (m : Arr N) :
    bosonPhase N q hq (basisVector m) = q m • basisVector m := by
  apply (U4 N).injective
  simp only [bosonPhase, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, U4_basisVector, map_smul,
    phaseUnitary_apply]
  rw [phase, gauge_single, extendSectorGauge_apply, mul_one, ← lp.single_smul]
  simp

/-- U4 with the inverse diagonal rephasing, matching q(m) conj(q(destination)). -/
def gaugedU4 : Boson N ≃ₗᵢ[ℂ] H N :=
  (U4 N).trans (phaseUnitary N q hq).symm

theorem gaugedU4_basis (m : Arr N) :
    gaugedU4 N q hq (basisVector m) = lp.single 2 m ((starRingEnd ℂ) (q m)) := by
  simp only [gaugedU4, LinearIsometryEquiv.trans_apply, U4_basisVector,
    phaseUnitary_symm_apply, phase, gauge_single, extendSectorGauge_apply, mul_one]

/-- Consequence of the proved U4 collective conjugacy and concrete diagonal unitary. -/
theorem gaugedU4_collective (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) (ψ : Boson (1 + n)) :
    gaugedU4 (1 + n) q hq (collective n a b ψ) =
      sectorEq (1 + n) q hq a b (gaugedU4 (1 + n) q hq ψ) := by
  have he := congrArg (fun A : H (1 + n) →L[ℂ] H (1 + n) =>
    A (gaugedU4 (1 + n) q hq ψ)) (phaseUnitary_conjugacy (1 + n) q hq a b)
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, gaugedU4, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, U4_collective] using he

theorem gaugedU4_conjugacy (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) :
    (gaugedU4 (1 + n) q hq).conjStarAlgEquiv (collective n a b) =
      sectorEq (1 + n) q hq a b := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.apply_symm_apply] using
      gaugedU4_collective n q hq a b ((gaugedU4 (1 + n) q hq).symm v)

end Boson

section Physical
open PhysicalTensor
variable (L : ℝ) [Fact (0 < L)]

/-- The physical Fourier mode matrix unit, before taking tensor placements. -/
def physicalMatrixUnit (a b : ℤ) : L2T L →L[ℂ] L2T L :=
  (Fourier.fourierL2 L).symm.conjStarAlgEquiv (matrixUnit a b)

theorem fourier_physicalMatrixUnit (a b : ℤ) (v : L2T L) :
    Fourier.fourierL2 L (physicalMatrixUnit L a b v) =
      matrixUnit a b (Fourier.fourierL2 L v) := by
  simp [physicalMatrixUnit]

/-- This is literally the rank-one operator between inverse Fourier basis modes. -/
theorem physicalMatrixUnit_rankOne (a b : ℤ) :
    physicalMatrixUnit L a b = InnerProductSpace.rankOne ℂ
      ((Fourier.fourierL2 L).symm (oneBasis b))
      ((Fourier.fourierL2 L).symm (oneBasis a)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply (Fourier.fourierL2 L).injective
  rw [fourier_physicalMatrixUnit]
  simp only [matrixUnit, InnerProductSpace.rankOne_apply, map_smul,
    LinearIsometryEquiv.apply_symm_apply]
  congr 1
  have h := (Fourier.fourierL2 L).inner_map_map
    ((Fourier.fourierL2 L).symm (oneBasis a)) v
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

/-- Literal bounded physical one-body placement in slot i. -/
def physicalSlot (n : ℕ) (i : Fin (1 + n)) (a b : ℤ) :
    HilbertTensorPower ℂ (L2T L) (1 + n) →L[ℂ] HilbertTensorPower ℂ (L2T L) (1 + n) :=
  (permHilbertIsometry (Equiv.swap 0 i)).conjStarAlgEquiv
    (TensorFourier.oneBodyPlacement n (physicalMatrixUnit L a b))

theorem fourier_physicalSlot (n : ℕ) (i : Fin (1 + n)) (a b : ℤ)
    (v : HilbertTensorPower ℂ (L2T L) (1 + n)) :
    TensorFourier.fourierTensor L (1 + n) (physicalSlot L n i a b v) =
      slot n i (matrixUnit a b) (TensorFourier.fourierTensor L (1 + n) v) := by
  have hm : (Fourier.fourierL2 L).conjStarAlgEquiv (physicalMatrixUnit L a b) =
      matrixUnit a b := by
    apply ContinuousLinearMap.ext
    intro v
    simp [physicalMatrixUnit]
  simp only [physicalSlot, slot, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [TensorFourier.tensorPower_permHilbert, TensorFourier.tensorPower_oneBodyPlacement,
    TensorFourier.tensorPower_permHilbert_symm, hm]

/-- Unprojected sum of the actual physical slot operators. -/
def physicalTotal (n : ℕ) (a b : ℤ) :
    HilbertTensorPower ℂ (L2T L) (1 + n) →L[ℂ] HilbertTensorPower ℂ (L2T L) (1 + n) :=
  ∑ i, physicalSlot L n i a b

theorem fourier_physicalTotal (n : ℕ) (a b : ℤ)
    (v : HilbertTensorPower ℂ (L2T L) (1 + n)) :
    TensorFourier.fourierTensor L (1 + n) (physicalTotal L n a b v) =
      totalPlacement n a b (TensorFourier.fourierTensor L (1 + n) v) := by
  simp only [physicalTotal, totalPlacement, sum_apply, map_sum, fourier_physicalSlot]

theorem physicalTotal_mem (n : ℕ) (a b : ℤ) (v : physSector L (1 + n)) :
    physicalTotal L n a b v.1 ∈ SymSector ℂ (L2T L) (1 + n) := by
  apply (TensorFourier.tensorPower_mem_symSector_iff (Fourier.fourierL2 L) _).mp
  rw [fourier_physicalTotal]
  exact totalPlacement_mem n a b (TensorFourier.U3 L (1 + n) v)

/-- Exactly N⁻¹ times the physical slot sum, restricted to the symmetric sector. -/
def physicalCollective (n : ℕ) (a b : ℤ) :
    physSector L (1 + n) →L[ℂ] physSector L (1 + n) :=
  (((1 + n : ℕ) : ℂ)⁻¹) •
    ((physicalTotal L n a b).comp (SymSector ℂ (L2T L) (1 + n)).subtypeL).codRestrict
      (SymSector ℂ (L2T L) (1 + n)) (physicalTotal_mem L n a b)

/-- U3 transports the independently constructed literal physical collective. -/
theorem U3_physicalCollective (n : ℕ) (a b : ℤ) (v : physSector L (1 + n)) :
    TensorFourier.U3 L (1 + n) (physicalCollective L n a b v) =
      collective n a b (TensorFourier.U3 L (1 + n) v) := by
  apply Subtype.ext
  change TensorFourier.fourierTensor L (1 + n)
    ((((1 + n : ℕ) : ℂ)⁻¹) • physicalTotal L n a b v.1) =
      (((1 + n : ℕ) : ℂ)⁻¹) •
        totalPlacement n a b (TensorFourier.fourierTensor L (1 + n) v.1)
  rw [map_smul, fourier_physicalTotal]

theorem physicalOccupation_collective (n : ℕ) (a b : ℤ) (v : physSector L (1 + n)) :
    physicalOccupation L (1 + n) (physicalCollective L n a b v) =
      E (1 + n) a b (physicalOccupation L (1 + n) v) := by
  change U4 (1 + n) (TensorFourier.U3 L (1 + n) (physicalCollective L n a b v)) = _
  rw [U3_physicalCollective, U4_collective]
  rfl

/-- The actual inverse-Fourier normalized occupation basis in the physical sector. -/
def physicalBasisVector {N : ℕ} (m : Arr N) : physSector L N :=
  (TensorFourier.U3 L N).symm (basisVector m)

@[simp] theorem physicalOccupation_basis {N : ℕ} (m : Arr N) :
    physicalOccupation L N (physicalBasisVector L m) = lp.single 2 m 1 := by
  simp [physicalOccupation, physicalBasisVector]

variable (N : ℕ) (q : Arr N → ℂ) (hq : ∀ m, Complex.normSq (q m) = 1)

/-- The constructed phase unitary transported to the actual physical sector via U3/U4. -/
def physicalPhase : physSector L N ≃ₗᵢ[ℂ] physSector L N :=
  ((physicalOccupation L N).trans (phaseUnitary N q hq)).trans
    (physicalOccupation L N).symm

/-- The gauged physical coefficient unitary; its supplied phases are arbitrary. -/
def gaugedPhysicalOccupation : physSector L N ≃ₗᵢ[ℂ] H N :=
  (TensorFourier.U3 L N).trans (gaugedU4 N q hq)

theorem gaugedPhysicalOccupation_apply (v : physSector L N) (m : Arr N) :
    gaugedPhysicalOccupation L N q hq v m =
      (starRingEnd ℂ) (q m) * physicalOccupation L N v m := by
  simp [gaugedPhysicalOccupation, gaugedU4, physicalOccupation]

theorem physicalPhase_apply (v : physSector L N) (m : Arr N) :
    physicalOccupation L N (physicalPhase L N q hq v) m =
      q m * physicalOccupation L N v m := by
  simp [physicalPhase]

theorem physicalOccupation_phase (v : physSector L N) :
    physicalOccupation L N (physicalPhase L N q hq v) =
      phaseUnitary N q hq (physicalOccupation L N v) := by
  simp [physicalPhase]

theorem physicalOccupation_phase_symm (v : physSector L N) :
    physicalOccupation L N ((physicalPhase L N q hq).symm v) =
      (phaseUnitary N q hq).symm (physicalOccupation L N v) := by
  simp [physicalPhase, LinearIsometryEquiv.symm_trans]

theorem physicalPhase_basis (m : Arr N) :
    physicalPhase L N q hq (physicalBasisVector L m) = q m • physicalBasisVector L m := by
  apply (physicalOccupation L N).injective
  rw [physicalOccupation_phase, physicalOccupation_basis, map_smul, physicalOccupation_basis]
  simp only [phaseUnitary_apply, phase, gauge_single, extendSectorGauge_apply, mul_one]
  rw [← lp.single_smul]
  simp

/-- Complete physical intertwining, using both actual U3 and proved U4 conjugacy. -/
theorem gaugedPhysicalOccupation_collective (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) (v : physSector L (1 + n)) :
    gaugedPhysicalOccupation L (1 + n) q hq (physicalCollective L n a b v) =
      sectorEq (1 + n) q hq a b (gaugedPhysicalOccupation L (1 + n) q hq v) := by
  change gaugedU4 (1 + n) q hq
    (TensorFourier.U3 L (1 + n) (physicalCollective L n a b v)) = _
  rw [U3_physicalCollective, gaugedU4_collective]
  rfl

theorem gaugedPhysicalOccupation_conjugacy (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) :
    (gaugedPhysicalOccupation L (1 + n) q hq).conjStarAlgEquiv
      (physicalCollective L n a b) = sectorEq (1 + n) q hq a b := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.apply_symm_apply] using
      gaugedPhysicalOccupation_collective L n q hq a b
        ((gaugedPhysicalOccupation L (1 + n) q hq).symm v)

/-- Pull the supplied diagonal rephasing back to the physical collective operator. -/
def physicalGaugedCollective (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) :
    physSector L (1 + n) →L[ℂ] physSector L (1 + n) :=
  (physicalPhase L (1 + n) q hq).symm.conjStarAlgEquiv (physicalCollective L n a b)

/-- The original physical occupation unitary carries the rephased operator to sectorEq. -/
theorem physicalOccupation_gaugedCollective (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) (v : physSector L (1 + n)) :
    physicalOccupation L (1 + n) (physicalGaugedCollective L n q hq a b v) =
      sectorEq (1 + n) q hq a b (physicalOccupation L (1 + n) v) := by
  simp only [physicalGaugedCollective, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, physicalOccupation_phase_symm,
    physicalOccupation_collective, physicalOccupation_phase]
  exact congrArg (fun A : H (1 + n) →L[ℂ] H (1 + n) =>
    A (physicalOccupation L (1 + n) v)) (phaseUnitary_conjugacy (1 + n) q hq a b)

/-- Source phase ratio, donor, factorial coefficient and empty-donor case on the physical basis. -/
theorem physicalGaugedCollective_basis (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) (m : Arr (1 + n)) :
    physicalGaugedCollective L n q hq a b (physicalBasisVector L m) =
      if hd : DonorOK a m.1 then
        (q m * (starRingEnd ℂ) (q (shiftArr a b m hd)) * (coef (1 + n) a b m.1 : ℂ)) •
          physicalBasisVector L (shiftArr a b m hd) else 0 := by
  apply (physicalOccupation L (1 + n)).injective
  rw [physicalOccupation_gaugedCollective, physicalOccupation_basis, sectorEq_single]
  split_ifs with hd
  · rw [map_smul, physicalOccupation_basis, ← lp.single_smul]
    simp
  · simp

theorem physicalGaugedCollective_norm_le (n : ℕ) (q : Arr (1 + n) → ℂ)
    (hq : ∀ m, Complex.normSq (q m) = 1) (a b : ℤ) :
    ‖physicalGaugedCollective L n q hq a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  calc
    ‖physicalGaugedCollective L n q hq a b v‖ =
        ‖physicalOccupation L (1 + n) (physicalGaugedCollective L n q hq a b v)‖ :=
      ((physicalOccupation L (1 + n)).norm_map _).symm
    _ = ‖sectorEq (1 + n) q hq a b (physicalOccupation L (1 + n) v)‖ := by
      rw [physicalOccupation_gaugedCollective]
    _ ≤ ‖sectorEq (1 + n) q hq a b‖ * ‖physicalOccupation L (1 + n) v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖v‖ := by
      rw [(physicalOccupation L (1 + n)).norm_map]
      exact mul_le_mul_of_nonneg_right (sectorEq_norm_le _ _ _ _ _) (norm_nonneg _)

end Physical

end QuantumNLS.GaugeTransport

/-! Kernel axiom audit for every declaration in this module. -/
#print axioms QuantumNLS.GaugeTransport.phase
#print axioms QuantumNLS.GaugeTransport.phase_apply
#print axioms QuantumNLS.GaugeTransport.phase_norm_le
#print axioms QuantumNLS.GaugeTransport.conj_phase_unit
#print axioms QuantumNLS.GaugeTransport.phase_conj_phase
#print axioms QuantumNLS.GaugeTransport.phase_phase_conj
#print axioms QuantumNLS.GaugeTransport.phase_norm
#print axioms QuantumNLS.GaugeTransport.phaseUnitary
#print axioms QuantumNLS.GaugeTransport.phaseUnitary_apply
#print axioms QuantumNLS.GaugeTransport.phaseUnitary_symm_apply
#print axioms QuantumNLS.GaugeTransport.phase_conj_eq_gauge
#print axioms QuantumNLS.GaugeTransport.phaseUnitary_conjugacy
#print axioms QuantumNLS.GaugeTransport.phaseUnitary_adjoint
#print axioms QuantumNLS.GaugeTransport.bosonPhase
#print axioms QuantumNLS.GaugeTransport.bosonPhase_basis
#print axioms QuantumNLS.GaugeTransport.gaugedU4
#print axioms QuantumNLS.GaugeTransport.gaugedU4_basis
#print axioms QuantumNLS.GaugeTransport.gaugedU4_collective
#print axioms QuantumNLS.GaugeTransport.gaugedU4_conjugacy
#print axioms QuantumNLS.GaugeTransport.physicalMatrixUnit
#print axioms QuantumNLS.GaugeTransport.fourier_physicalMatrixUnit
#print axioms QuantumNLS.GaugeTransport.physicalMatrixUnit_rankOne
#print axioms QuantumNLS.GaugeTransport.physicalSlot
#print axioms QuantumNLS.GaugeTransport.fourier_physicalSlot
#print axioms QuantumNLS.GaugeTransport.physicalTotal
#print axioms QuantumNLS.GaugeTransport.fourier_physicalTotal
#print axioms QuantumNLS.GaugeTransport.physicalTotal_mem
#print axioms QuantumNLS.GaugeTransport.physicalCollective
#print axioms QuantumNLS.GaugeTransport.U3_physicalCollective
#print axioms QuantumNLS.GaugeTransport.physicalOccupation_collective
#print axioms QuantumNLS.GaugeTransport.physicalBasisVector
#print axioms QuantumNLS.GaugeTransport.physicalOccupation_basis
#print axioms QuantumNLS.GaugeTransport.physicalPhase
#print axioms QuantumNLS.GaugeTransport.gaugedPhysicalOccupation
#print axioms QuantumNLS.GaugeTransport.gaugedPhysicalOccupation_apply
#print axioms QuantumNLS.GaugeTransport.physicalPhase_apply
#print axioms QuantumNLS.GaugeTransport.physicalOccupation_phase
#print axioms QuantumNLS.GaugeTransport.physicalOccupation_phase_symm
#print axioms QuantumNLS.GaugeTransport.physicalPhase_basis
#print axioms QuantumNLS.GaugeTransport.gaugedPhysicalOccupation_collective
#print axioms QuantumNLS.GaugeTransport.gaugedPhysicalOccupation_conjugacy
#print axioms QuantumNLS.GaugeTransport.physicalGaugedCollective
#print axioms QuantumNLS.GaugeTransport.physicalOccupation_gaugedCollective
#print axioms QuantumNLS.GaugeTransport.physicalGaugedCollective_basis
#print axioms QuantumNLS.GaugeTransport.physicalGaugedCollective_norm_le
