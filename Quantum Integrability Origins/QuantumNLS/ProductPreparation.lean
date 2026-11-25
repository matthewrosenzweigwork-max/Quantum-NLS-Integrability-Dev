/-
QuantumNLS.ProductPreparation — the constructive product and parameter portion
of DEF-003 on the physical L²(T_L) carrier.

This module deliberately treats a unit-mass limiting measure as an explicit
input to the mass-rescaling map.  It does not construct such a measure or claim
that a sequence converges to it.
-/
import QuantumNLS.PhysicalTensor

open scoped InnerProductSpace
open MeasureTheory
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor

noncomputable section

namespace QuantumNLS.ProductPreparation

variable {L : ℝ} [Fact (0 < L)]

/-- The physical mass `m = ‖u‖₂²`. -/
def physicalMass (u : L2T L) : ℝ := ‖u‖ ^ 2

/-- A profile with positive mass, together with its physical coupling.

The particle number is supplied separately, so this datum describes the full
family of preparations as `N` varies. -/
structure PositiveMassPreparation where
  profile : L2T L
  coupling : ℝ
  mass_pos : 0 < physicalMass profile
  coupling_pos : 0 < coupling

namespace PositiveMassPreparation

variable (P : PositiveMassPreparation (L := L))

/-- The source's unit-field normalization `u / √m`, with real scalar action. -/
def unitProfile : L2T L :=
  (Real.sqrt (physicalMass P.profile))⁻¹ • P.profile

theorem sqrt_mass_eq_norm : Real.sqrt (physicalMass P.profile) = ‖P.profile‖ := by
  rw [physicalMass, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem norm_unitProfile : ‖P.unitProfile‖ = 1 := by
  have hsqrt : 0 < Real.sqrt (physicalMass P.profile) := Real.sqrt_pos.2 P.mass_pos
  rw [unitProfile, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hsqrt.le), P.sqrt_mass_eq_norm]
  have hnorm : ‖P.profile‖ ≠ 0 := by
    intro h
    have hm : physicalMass P.profile = 0 := by simp [physicalMass, h]
    exact (ne_of_gt P.mass_pos) hm
  exact inv_mul_cancel₀ hnorm

theorem mass_unitProfile : physicalMass P.unitProfile = 1 := by
  simp [physicalMass, P.norm_unitProfile]

/-- The literal `N`-fold product tensor, included in the symmetric sector. -/
def bosonicProduct (N : ℕ) (v : L2T L) : SymSector ℂ (L2T L) N :=
  ⟨htpow N v, htpow_mem_symSector N v⟩

theorem norm_bosonicProduct_eq (N : ℕ) (v : L2T L) :
    ‖bosonicProduct (L := L) N v‖ = ‖v‖ ^ N := by
  change ‖(htpow N v : HilbertTensorPower ℂ (L2T L) N)‖ = ‖v‖ ^ N
  exact norm_htpow N v

theorem norm_bosonicProduct (N : ℕ) (v : L2T L) (hv : ‖v‖ = 1) :
    ‖bosonicProduct (L := L) N v‖ = 1 := by
  rw [norm_bosonicProduct_eq, hv]
  simp

/-- The normalized bosonic product state for a positive-mass physical profile. -/
def productState (N : ℕ) : SymSector ℂ (L2T L) N :=
  bosonicProduct N P.unitProfile

theorem norm_productState (N : ℕ) : ‖P.productState N‖ = 1 :=
  norm_bosonicProduct N P.unitProfile P.norm_unitProfile

/-- The product state is represented on physical configuration space by the
literal product of its normalized one-particle fields. -/
theorem productState_wavefunction (N : ℕ) :
    ((PhysicalTensor.physEmbed (L := L) (N := N)
      (P.productState N : HilbertTensorPower ℂ (L2T L) N)) :
        (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      fun x => ∏ j, P.unitProfile (x j) := by
  change ((PhysicalTensor.physEmbed (L := L) (N := N)
      (htpow N P.unitProfile : HilbertTensorPower ℂ (L2T L) N)) :
        (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      fun x => ∏ j, P.unitProfile (x j)
  exact PhysicalTensor.coeFn_physEmbed_htpow (N := N) P.unitProfile

/-- Effective coupling for the normalized profile: `κ m`. -/
def effectiveCoupling : ℝ := P.coupling * physicalMass P.profile

/-- Microscopic coupling at particle number `N`: `κ m / N`. -/
def microscopicCoupling (N : ℕ) : ℝ := P.effectiveCoupling / (N : ℝ)

theorem microscopicCoupling_eq_source (N : ℕ) :
    P.microscopicCoupling N = P.coupling * physicalMass P.profile / (N : ℝ) := rfl

theorem effectiveCoupling_pos : 0 < P.effectiveCoupling :=
  mul_pos P.coupling_pos P.mass_pos

theorem microscopicCoupling_pos {N : ℕ} (hN : 0 < N) :
    0 < P.microscopicCoupling N := by
  apply div_pos P.effectiveCoupling_pos
  exact_mod_cast hN

end PositiveMassPreparation

/-- DEF-003's full-mass scaling operation for a profile of arbitrary mass.

This operation accepts a candidate scalar measure as input and returns its
mass-rescaled measure; it makes no assertion that the candidate limit exists. -/
def fullMassMeasure (u : L2T L) (unitLimit : Measure ℝ) : Measure ℝ :=
  if physicalMass u = 0 then 0 else ENNReal.ofReal (physicalMass u) • unitLimit

theorem fullMassMeasure_of_mass_zero {u : L2T L} (unitLimit : Measure ℝ)
    (hm : physicalMass u = 0) : fullMassMeasure (L := L) u unitLimit = 0 := by
  simp [fullMassMeasure, hm]

theorem fullMassMeasure_zero (unitLimit : Measure ℝ) :
    fullMassMeasure (L := L) (0 : L2T L) unitLimit = 0 := by
  apply fullMassMeasure_of_mass_zero
  simp [physicalMass]

theorem fullMassMeasure_eq_scaled {u : L2T L} (unitLimit : Measure ℝ)
    (hm : 0 < physicalMass u) :
    fullMassMeasure (L := L) u unitLimit = ENNReal.ofReal (physicalMass u) • unitLimit := by
  simp [fullMassMeasure, ne_of_gt hm]

end QuantumNLS.ProductPreparation

#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.norm_unitProfile
#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.mass_unitProfile
#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.norm_bosonicProduct_eq
#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.norm_bosonicProduct
#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.norm_productState
#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.productState_wavefunction
#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.microscopicCoupling_eq_source
#print axioms QuantumNLS.ProductPreparation.PositiveMassPreparation.microscopicCoupling_pos
#print axioms QuantumNLS.ProductPreparation.fullMassMeasure_of_mass_zero
#print axioms QuantumNLS.ProductPreparation.fullMassMeasure_zero
#print axioms QuantumNLS.ProductPreparation.fullMassMeasure_eq_scaled
