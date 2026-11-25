import LiebLiniger.FixedPeriod.Quantum.WickContractionNorm
import LiebLiniger.FixedPeriod.Quantum.TransferCoefficientOperator

/-!
# Q2-028: polynomial growth for the actual transfer contraction kernels

The guarded contraction is the Q2-025 tensor kernel, transported only across
proved sector-index equalities. Unavailable orders are exactly zero, as in the
source. Both source operator orders use the SAME actual physical coefficient
transferCoefficientOperator L ζ r. The constant is fixed from p,q alone before
ζ,r,j or B are chosen. No growth estimate is supplied as a hypothesis.
-/
noncomputable section
open MeasureTheory
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem norm_sectorCast_precomp {a b c : ℕ} (h : a = b)
    (A : SymmetricSector μ b →L[ℂ] SymmetricSector μ c) :
    ‖A ∘L (symmetricSectorCast μ h).toLinearIsometry.toContinuousLinearMap‖ = ‖A‖ := by
  subst b
  change ‖A ∘L ContinuousLinearMap.id ℂ _‖ = ‖A‖
  rw [ContinuousLinearMap.comp_id]

private theorem norm_sectorCast_postcomp {a b c : ℕ} (h : b = c)
    (A : SymmetricSector μ a →L[ℂ] SymmetricSector μ b) :
    ‖(symmetricSectorCast μ h).toLinearIsometry.toContinuousLinearMap ∘L A‖ = ‖A‖ := by
  subst c
  change ‖ContinuousLinearMap.id ℂ _ ∘L A‖ = ‖A‖
  rw [ContinuousLinearMap.id_comp]

/-- Original-degree source contraction, with precisely zero for unavailable
orders. The nonzero branch is the concrete Q2-025 operator with equality-only
sector transports, preserving the first-j-output/last-j-input slot order. -/
def sourceDerivativeContractionKernel {pb qb pc qc : ℕ}
    (A1 : SymmetricSector μ pb →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ qc) (j : ℕ) :
    SymmetricSector μ (pb + pc - j) →L[ℂ] SymmetricSector μ (qb + qc - j) :=
  if hj : j ≤ min pb qc then
    let B1 := A1 ∘L (symmetricSectorCast μ (show (pb - j) + j = pb by omega)).toLinearIsometry.toContinuousLinearMap
    let B2 := (symmetricSectorCast μ (show qc = j + (qc - j) by omega)).toLinearIsometry.toContinuousLinearMap ∘L A2
    (symmetricSectorCast μ (show qb + (qc - j) = qb + qc - j by omega)).toLinearIsometry.toContinuousLinearMap ∘L
      tensorDerivativeContraction μ B1 B2 ∘L
      (symmetricSectorCast μ (show pb + pc - j = (pb - j) + pc by omega)).toLinearIsometry.toContinuousLinearMap
  else 0

@[simp] theorem sourceDerivativeContractionKernel_unavailable {pb qb pc qc : ℕ}
    (A1 : SymmetricSector μ pb →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ qc) (j : ℕ)
    (hj : ¬j ≤ min pb qc) : sourceDerivativeContractionKernel μ A1 A2 j = 0 := by
  simp only [sourceDerivativeContractionKernel, dif_neg hj]

/-- Source Q2-026 bound for the original-degree guarded kernel, with every
unavailable order included by its prescribed zero branch. -/
theorem norm_sourceDerivativeContractionKernel_le {pb qb pc qc : ℕ}
    (A1 : SymmetricSector μ pb →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ qc) (j : ℕ) :
    ‖sourceDerivativeContractionKernel μ A1 A2 j‖ ≤
      (pb.descFactorial j : ℝ) * (qc.descFactorial j : ℝ) * ‖A1‖ * ‖A2‖ := by
  by_cases hj : j ≤ min pb qc
  · rw [sourceDerivativeContractionKernel, dif_pos hj,
      norm_sectorCast_postcomp, norm_sectorCast_precomp]
    have hpb : pb - j + j = pb := by omega
    have hqc : j + (qc - j) = qc := by omega
    have h := (wickRealDerivativeContraction_kernel_norm μ
      (A1 ∘L (symmetricSectorCast μ hpb).toLinearIsometry.toContinuousLinearMap)
      ((symmetricSectorCast μ hqc.symm).toLinearIsometry.toContinuousLinearMap ∘L A2)).2
    simpa only [hpb, hqc, norm_sectorCast_precomp, norm_sectorCast_postcomp] using h
  · rw [sourceDerivativeContractionKernel_unavailable μ A1 A2 j hj,
      ContinuousLinearMap.opNorm_zero (E := SymmetricSector μ (pb + pc - j))
        (F := SymmetricSector μ (qb + qc - j)) (σ₁₂ := RingHom.id ℂ)]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (ContinuousLinearMap.opNorm_nonneg A1)) (ContinuousLinearMap.opNorm_nonneg A2)

/-- The same exact shifted Q2-025 tensor operator is recovered in every
available branch; no unrelated norm-bounded family is introduced. -/
theorem sourceDerivativeContractionKernel_available {pb qb pc qc : ℕ}
    (A1 : SymmetricSector μ pb →L[ℂ] SymmetricSector μ qb)
    (A2 : SymmetricSector μ pc →L[ℂ] SymmetricSector μ qc) (j : ℕ)
    (hj : j ≤ min pb qc) :
    sourceDerivativeContractionKernel μ A1 A2 j =
      (symmetricSectorCast μ (show qb + (qc - j) = qb + qc - j by omega)).toLinearIsometry.toContinuousLinearMap ∘L
        tensorDerivativeContraction μ
          (A1 ∘L (symmetricSectorCast μ (show (pb - j) + j = pb by omega)).toLinearIsometry.toContinuousLinearMap)
          ((symmetricSectorCast μ (show qc = j + (qc - j) by omega)).toLinearIsometry.toContinuousLinearMap ∘L A2) ∘L
        (symmetricSectorCast μ (show pb + pc - j = (pb - j) + pc by omega)).toLinearIsometry.toContinuousLinearMap := by
  simp only [sourceDerivativeContractionKernel, dif_pos hj]

end LiebLiniger.FixedPeriod.Quantum
namespace LiebLiniger.FixedPeriod.Quantum
variable (L : ℝ) [Fact (0 < L)]

/-- Literal source order b_(ζ,r) then b_B, on the physical length-L circle. -/
def transferContractionBefore {p q : ℕ} (ζ : ℂ) (r : ℕ)
    (B : SymmetricSector (volume : Measure (AddCircle L)) p →L[ℂ]
      SymmetricSector (volume : Measure (AddCircle L)) q) (j : ℕ) :=
  sourceDerivativeContractionKernel (volume : Measure (AddCircle L))
    (transferCoefficientOperator L ζ r) B j

/-- Literal reverse source order b_B then b_(ζ,r). -/
def transferContractionAfter {p q : ℕ} (ζ : ℂ) (r : ℕ)
    (B : SymmetricSector (volume : Measure (AddCircle L)) p →L[ℂ]
      SymmetricSector (volume : Measure (AddCircle L)) q) (j : ℕ) :=
  sourceDerivativeContractionKernel (volume : Measure (AddCircle L))
    B (transferCoefficientOperator L ζ r) j

/-- The explicit source constant is fixed before ζ,r,j and B. -/
def transferContractionConstant (p q : ℕ) : ℝ := contractionDegreeConstant (max p q)

theorem transferContractionConstant_pos (p q : ℕ) : 0 < transferContractionConstant p q := by
  unfold transferContractionConstant contractionDegreeConstant
  positivity

/-- Both actual physical orders satisfy the source polynomial growth bound.
The same actual A_(ζ,r) appears in the maps and on both right-hand sides. -/
theorem transferContraction_polynomial_bound {p q : ℕ}
    (ζ : ℂ) (r j : ℕ)
    (B : SymmetricSector (volume : Measure (AddCircle L)) p →L[ℂ]
      SymmetricSector (volume : Measure (AddCircle L)) q) (hj : j ≤ max p q) :
    ‖transferContractionBefore L ζ r B j‖ ≤
        transferContractionConstant p q * (1 + (r : ℝ)) ^ (max p q) *
          ‖transferCoefficientOperator L ζ r‖ * ‖B‖ ∧
      ‖transferContractionAfter L ζ r B j‖ ≤
        transferContractionConstant p q * (1 + (r : ℝ)) ^ (max p q) *
          ‖transferCoefficientOperator L ζ r‖ * ‖B‖ := by
  have hq := contractionCoefficient_polynomial_le r q j (max p q) hj (Nat.le_max_right p q)
  have hp : (p.descFactorial j : ℝ) * (r.descFactorial j : ℝ) ≤
      transferContractionConstant p q * (1 + (r : ℝ)) ^ (max p q) := by
    simpa only [transferContractionConstant, mul_comm] using
      contractionCoefficient_polynomial_le r p j (max p q) hj (Nat.le_max_left p q)
  constructor
  · exact (norm_sourceDerivativeContractionKernel_le _ (transferCoefficientOperator L ζ r) B j).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hq (ContinuousLinearMap.opNorm_nonneg _))
        (ContinuousLinearMap.opNorm_nonneg B))
  · calc
      _ ≤ (p.descFactorial j : ℝ) * (r.descFactorial j : ℝ) * ‖B‖ *
          ‖transferCoefficientOperator L ζ r‖ := norm_sourceDerivativeContractionKernel_le _ B _ j
      _ ≤ transferContractionConstant p q * (1 + (r : ℝ)) ^ (max p q) * ‖B‖ *
          ‖transferCoefficientOperator L ζ r‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (ContinuousLinearMap.opNorm_nonneg B))
          (ContinuousLinearMap.opNorm_nonneg _)
      _ = _ := by ring

/-- Quantifier-explicit source theorem: C_(p,q) is chosen before every spectral
parameter, transfer degree, contraction order and bounded fixed-degree kernel. -/
theorem exists_transferContraction_polynomial_bound (p q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ζ : ℂ) (r j : ℕ)
      (B : SymmetricSector (volume : Measure (AddCircle L)) p →L[ℂ]
        SymmetricSector (volume : Measure (AddCircle L)) q), j ≤ max p q →
      ‖transferContractionBefore L ζ r B j‖ ≤
          C * (1 + (r : ℝ)) ^ (max p q) * ‖transferCoefficientOperator L ζ r‖ * ‖B‖ ∧
        ‖transferContractionAfter L ζ r B j‖ ≤
          C * (1 + (r : ℝ)) ^ (max p q) * ‖transferCoefficientOperator L ζ r‖ * ‖B‖ := by
  exact ⟨transferContractionConstant p q, transferContractionConstant_pos p q,
    fun ζ r j B hj => transferContraction_polynomial_bound L ζ r j B hj⟩

end LiebLiniger.FixedPeriod.Quantum
