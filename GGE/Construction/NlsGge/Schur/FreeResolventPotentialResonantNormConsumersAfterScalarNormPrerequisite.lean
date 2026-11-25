import NlsGge.Schur.FreeResolventPotentialVectorNormPrerequisites
import NlsGge.Schur.FreeResolventAdjointCoordinateMinimalPrerequisite
import NlsGge.Schur.FreeResolventComplexNormMulSqPrerequisite
import NlsGge.Schur.FreeResolventPotentialColumnEnergy
import NlsGge.Schur.FreeResolventReflectedPotentialColumnEnergy
import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries
import NlsGge.Schur.FreeResolventParityComponentZeros
import NlsGge.Schur.FreeResolventParityComponentNormSquareSummable
import NlsGge.Schur.FreeResolventTsumRemoveZeroCoordinate
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators ENNReal InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

private theorem parityPairVector_unit (n : ℤ) (i : Bool × Sector n) :
    ‖parityPairVector n i‖ = 1 := by
  rw [← (parityPairRepr n).norm_map, parityPairRepr_vector]
  simp

/-- The first actual resonant DVP column has the exact scalar Fourier energy
controlled by the checked unreflected physical H¹ column estimate. -/
theorem freeResolventPotentialColumn_false_resonant_norm_sq_le_from_prerequisites
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, resonantIndex n))‖ ^ 2 ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 := by
  let x := freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
    (parityPairVector n (false, resonantIndex n))
  let y := parityPairRepr n x
  have hnorm : ‖x‖ ^ 2 = ∑' i : Bool × Sector n, ‖y i‖ ^ 2 := by
    simpa only [y] using parityPair_norm_sq_eq_tsum_repr_prerequisite n x
  have hcoef (m : Sector n) :
      y (true, m) = freeResolventCoeff n z m *
        physicalFourier u₁ ((m.val + n) / 2) := by
    change parityPairRepr n x (true, m) =
      freeResolventCoeff n z m * physicalFourier u₁ ((m.val + n) / 2)
    rw [parityPairRepr_inner]
    simpa [x, resonantIndex] using freeResolventPotentialColumn_upper_entry
      u₁ u₂ hu₁ hu₂ n z hz m (resonantIndex n)
  have hzero (m : Sector n) : y (false, m) = 0 := by
    change parityPairRepr n
      (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, resonantIndex n))) (false, m) = 0
    exact freeResolventPotentialColumn_false_resonant_false_component_zero
      u₁ u₂ hu₁ hu₂ n z hz m
  have hcoeffsum : Summable (fun m : Sector n => ‖y (true, m)‖ ^ 2) := by
    simpa only [y] using
      parityPairRepr_component_normSq_summable n x true
  have hsum_restrict :
      (∑' m : Sector n, ‖y (true, m)‖ ^ 2) =
        ∑' m : {m : Sector n // m ≠ resonantIndex n}, ‖y (true, m.val)‖ ^ 2 := by
    have hnres : ‖y (true, resonantIndex n)‖ ^ 2 = 0 := by
      rw [hcoef]
      simp [freeResolventCoeff]
    exact tsum_eq_tsum_subtype_ne_of_zero
      (fun m : Sector n => ‖y (true, m)‖ ^ 2) hcoeffsum
      (resonantIndex n) hnres
  have henergy :
      ‖x‖ ^ 2 =
        ∑' m : {m : Sector n // m ≠ resonantIndex n},
          ‖freeResolventCoeff n z m.val‖ ^ 2 *
            ‖physicalFourier u₁ ((m.val + n) / 2)‖ ^ 2 := by
    have hfull : Summable (fun i : Bool × Sector n => ‖y i‖ ^ 2) := by
      have hs := (lp.memℓp (y : lp (fun _ : Bool × Sector n => ℂ) 2)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
    rw [hnorm, hfull.tsum_prod, tsum_fintype]
    simp only [Fintype.sum_bool, hzero]
    rw [hsum_restrict]
    simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), tsum_zero, add_zero, zero_add]
    apply tsum_congr
    intro m
    rw [hcoef m]
    exact complex_norm_mul_sq_prerequisite _ _
  rw [henergy]
  exact freeResolventPotentialColumnEnergy_bound u₁ hu₁ n hn z hz

/-- The independent reflected resonant DVP column is controlled by the
reflected physical H¹ coefficient energy. -/
theorem freeResolventPotentialColumn_true_resonant_norm_sq_le_from_prerequisites
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, resonantIndex n))‖ ^ 2 ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 := by
  let x := freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
    (parityPairVector n (true, resonantIndex n))
  let y := parityPairRepr n x
  have hnorm : ‖x‖ ^ 2 = ∑' i : Bool × Sector n, ‖y i‖ ^ 2 := by
    simpa only [y] using parityPair_norm_sq_eq_tsum_repr_prerequisite n x
  have hcoef (m : Sector n) :
      y (false, m) = freeResolventCoeff n z m *
        physicalFourier u₂ (-(m.val + n) / 2) := by
    change parityPairRepr n x (false, m) =
      freeResolventCoeff n z m * physicalFourier u₂ (-(m.val + n) / 2)
    rw [parityPairRepr_inner]
    simpa [x, resonantIndex] using freeResolventPotentialColumn_lower_entry
      u₁ u₂ hu₁ hu₂ n z hz m (resonantIndex n)
  have hzero (m : Sector n) : y (true, m) = 0 := by
    change parityPairRepr n
      (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, resonantIndex n))) (true, m) = 0
    exact freeResolventPotentialColumn_true_resonant_true_component_zero
      u₁ u₂ hu₁ hu₂ n z hz m
  have hcoeffsum : Summable (fun m : Sector n => ‖y (false, m)‖ ^ 2) := by
    simpa only [y] using
      parityPairRepr_component_normSq_summable n x false
  have hsum_restrict :
      (∑' m : Sector n, ‖y (false, m)‖ ^ 2) =
        ∑' m : {m : Sector n // m ≠ resonantIndex n}, ‖y (false, m.val)‖ ^ 2 := by
    have hnres : ‖y (false, resonantIndex n)‖ ^ 2 = 0 := by
      rw [hcoef]
      simp [freeResolventCoeff]
    exact tsum_eq_tsum_subtype_ne_of_zero
      (fun m : Sector n => ‖y (false, m)‖ ^ 2) hcoeffsum
      (resonantIndex n) hnres
  have henergy :
      ‖x‖ ^ 2 =
        ∑' m : {m : Sector n // m ≠ resonantIndex n},
          ‖freeResolventCoeff n z m.val‖ ^ 2 *
            ‖physicalFourier u₂ (-(m.val + n) / 2)‖ ^ 2 := by
    have hfull : Summable (fun i : Bool × Sector n => ‖y i‖ ^ 2) := by
      have hs := (lp.memℓp (y : lp (fun _ : Bool × Sector n => ℂ) 2)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
    rw [hnorm, hfull.tsum_prod, tsum_fintype]
    simp only [Fintype.sum_bool, hzero]
    rw [hsum_restrict]
    simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), tsum_zero, add_zero, zero_add]
    apply tsum_congr
    intro m
    rw [hcoef m]
    exact complex_norm_mul_sq_prerequisite _ _
  rw [henergy]
  exact freeResolventReflectedPotentialColumnEnergy_bound u₂ hu₂ n hn z hz

/-- The first actual resonant PVD row, represented by the adjoint vector of
the actual PVD operator, has the exact unreflected scalar coefficient energy. -/
theorem resonantPotentialFreeResolventRow_true_resonant_adjoint_norm_sq_le_from_prerequisites
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint
        (parityPairVector n (true, resonantIndex n))‖ ^ 2 ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₁ hu₁‖ ^ 2 := by
  let T := resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz
  let r := T.adjoint (parityPairVector n (true, resonantIndex n))
  let y := parityPairRepr n r
  have hnorm : ‖r‖ ^ 2 = ∑' i : Bool × Sector n, ‖y i‖ ^ 2 := by
    simpa only [y] using parityPair_norm_sq_eq_tsum_repr_prerequisite n r
  have hcoef (m : Sector n) :
      ‖y (false, m)‖ ^ 2 =
        ‖freeResolventCoeff n z m *
          physicalFourier u₁ ((m.val + n) / 2)‖ ^ 2 := by
    change ‖parityPairRepr n r (false, m)‖ ^ 2 =
      ‖freeResolventCoeff n z m *
        physicalFourier u₁ ((m.val + n) / 2)‖ ^ 2
    have hval : parityPairRepr n r (false, m) =
        star (inner ℂ (parityPairVector n (true, resonantIndex n))
          (T (parityPairVector n (false, m)))) :=
      parityPair_adjoint_repr_coordinate_prerequisite n T
        (false, m) (true, resonantIndex n)
    have hEntry := resonantPotentialFreeResolventRow_upper_entry
      u₁ u₂ hu₁ hu₂ n z hz (resonantIndex n) m
    have hfreq : ((resonantIndex n).val + m.val) / 2 = (m.val + n) / 2 := by
      simp [resonantIndex, add_comm]
    rw [hval, hEntry]
    simp only [if_true]
    rw [hfreq]
    simp only [norm_star, norm_mul, mul_pow]
    ring
  have hzero (m : Sector n) : y (true, m) = 0 := by
    change parityPairRepr n r (true, m) = 0
    have hval : parityPairRepr n r (true, m) =
        star (inner ℂ (parityPairVector n (true, resonantIndex n))
          (T (parityPairVector n (true, m)))) :=
      parityPair_adjoint_repr_coordinate_prerequisite n T
        (true, m) (true, resonantIndex n)
    have hEntry : inner ℂ (parityPairVector n (true, resonantIndex n))
        (T (parityPairVector n (true, m))) = 0 := by
      exact resonantPotentialFreeResolventRow_true_true_entry_zero
        u₁ u₂ hu₁ hu₂ n z hz (resonantIndex n) m
    rw [hval, hEntry]
    simp
  have hcoeffsum : Summable (fun m : Sector n => ‖y (false, m)‖ ^ 2) := by
    simpa only [y] using
      parityPairRepr_component_normSq_summable n r false
  have hsum_restrict :
      (∑' m : Sector n, ‖y (false, m)‖ ^ 2) =
        ∑' m : {m : Sector n // m ≠ resonantIndex n}, ‖y (false, m.val)‖ ^ 2 := by
    have hnres : ‖y (false, resonantIndex n)‖ ^ 2 = 0 := by
      rw [hcoef]
      simp [freeResolventCoeff]
    exact tsum_eq_tsum_subtype_ne_of_zero
      (fun m : Sector n => ‖y (false, m)‖ ^ 2) hcoeffsum
      (resonantIndex n) hnres
  have henergy :
      ‖r‖ ^ 2 =
        ∑' m : {m : Sector n // m ≠ resonantIndex n},
          ‖freeResolventCoeff n z m.val‖ ^ 2 *
            ‖physicalFourier u₁ ((m.val + n) / 2)‖ ^ 2 := by
    have hfull : Summable (fun i : Bool × Sector n => ‖y i‖ ^ 2) := by
      have hs := (lp.memℓp (y : lp (fun _ : Bool × Sector n => ℂ) 2)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
    rw [hnorm, hfull.tsum_prod, tsum_fintype]
    simp only [Fintype.sum_bool, hzero]
    rw [hsum_restrict]
    simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), tsum_zero, add_zero, zero_add]
    apply tsum_congr
    intro m
    rw [hcoef m]
    exact complex_norm_mul_sq_prerequisite _ _
  rw [henergy]
  exact freeResolventPotentialColumnEnergy_bound u₁ hu₁ n hn z hz

/-- The reflected actual resonant PVD row is controlled by the independent
second field and the reflected physical H¹ coefficient energy. -/
theorem resonantPotentialFreeResolventRow_false_resonant_adjoint_norm_sq_le_from_prerequisites
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (hn : n ≠ 0) (z : ℂ) (hz : z ∈ spectralDisk n) :
    ‖(resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz).adjoint
        (parityPairVector n (false, resonantIndex n))‖ ^ 2 ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u₂ hu₂‖ ^ 2 := by
  let T := resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz
  let r := T.adjoint (parityPairVector n (false, resonantIndex n))
  let y := parityPairRepr n r
  have hnorm : ‖r‖ ^ 2 = ∑' i : Bool × Sector n, ‖y i‖ ^ 2 := by
    simpa only [y] using parityPair_norm_sq_eq_tsum_repr_prerequisite n r
  have hcoef (m : Sector n) :
      ‖y (true, m)‖ ^ 2 =
        ‖freeResolventCoeff n z m *
          physicalFourier u₂ (-(m.val + n) / 2)‖ ^ 2 := by
    change ‖parityPairRepr n r (true, m)‖ ^ 2 =
      ‖freeResolventCoeff n z m *
        physicalFourier u₂ (-(m.val + n) / 2)‖ ^ 2
    have hval : parityPairRepr n r (true, m) =
        star (inner ℂ (parityPairVector n (false, resonantIndex n))
          (T (parityPairVector n (true, m)))) :=
      parityPair_adjoint_repr_coordinate_prerequisite n T
        (true, m) (false, resonantIndex n)
    have hEntry := resonantPotentialFreeResolventRow_lower_entry
      u₁ u₂ hu₁ hu₂ n z hz (resonantIndex n) m
    rw [hval, hEntry]
    simp only [if_true]
    rw [show -((resonantIndex n).val + m.val) / 2 = -(m.val + n) / 2 by
      simp [resonantIndex, add_comm]]
    simp only [norm_star, norm_mul, mul_pow]
    ring
  have hzero (m : Sector n) : y (false, m) = 0 := by
    change parityPairRepr n r (false, m) = 0
    have hval : parityPairRepr n r (false, m) =
        star (inner ℂ (parityPairVector n (false, resonantIndex n))
          (T (parityPairVector n (false, m)))) :=
      parityPair_adjoint_repr_coordinate_prerequisite n T
        (false, m) (false, resonantIndex n)
    have hEntry : inner ℂ (parityPairVector n (false, resonantIndex n))
        (T (parityPairVector n (false, m))) = 0 := by
      exact resonantPotentialFreeResolventRow_false_false_entry_zero
        u₁ u₂ hu₁ hu₂ n z hz (resonantIndex n) m
    rw [hval, hEntry]
    simp
  have hcoeffsum : Summable (fun m : Sector n => ‖y (true, m)‖ ^ 2) := by
    simpa only [y] using
      parityPairRepr_component_normSq_summable n r true
  have hsum_restrict :
      (∑' m : Sector n, ‖y (true, m)‖ ^ 2) =
        ∑' m : {m : Sector n // m ≠ resonantIndex n}, ‖y (true, m.val)‖ ^ 2 := by
    have hnres : ‖y (true, resonantIndex n)‖ ^ 2 = 0 := by
      rw [hcoef]
      simp [freeResolventCoeff]
    exact tsum_eq_tsum_subtype_ne_of_zero
      (fun m : Sector n => ‖y (true, m)‖ ^ 2) hcoeffsum
      (resonantIndex n) hnres
  have henergy :
      ‖r‖ ^ 2 =
        ∑' m : {m : Sector n // m ≠ resonantIndex n},
          ‖freeResolventCoeff n z m.val‖ ^ 2 *
            ‖physicalFourier u₂ (-(m.val + n) / 2)‖ ^ 2 := by
    have hfull : Summable (fun i : Bool × Sector n => ‖y i‖ ^ 2) := by
      have hs := (lp.memℓp (y : lp (fun _ : Bool × Sector n => ℂ) 2)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs
    rw [hnorm, hfull.tsum_prod, tsum_fintype]
    simp only [Fintype.sum_bool, hzero]
    rw [hsum_restrict]
    simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), tsum_zero, add_zero, zero_add]
    apply tsum_congr
    intro m
    rw [hcoef m]
    exact complex_norm_mul_sq_prerequisite _ _
  rw [henergy]
  exact freeResolventReflectedPotentialColumnEnergy_bound u₂ hu₂ n hn z hz


end NlsGge.Schur
