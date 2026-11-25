import QuantumNLS.TerraMultiRound91ProductProjection
import QuantumNLS.HaarSpectralTail

/-! Transport the physical product projection estimate to the occupation
basis and tensor sector used by the high-angle theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.BetheCoefficientTransform
open QuantumNLS.BethePhysicalTransfer QuantumNLS.HaarSpectralTail QuantumNLS.ProductEnergyPreparation
open QuantumNLS.TerraMultiRound91ProductMoment QuantumNLS.TerraMultiRound91ProductProjection
namespace QuantumNLS.TerraMultiRound91OccupationProjection
variable {L : ℝ} [Fact (0 < L)]

theorem product_position (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (N : ℕ) :
    symmetricPosition L N (HighMomentsOps.wvec N u) = ContactOperator.valSym (productForm u hu hH N) := by
  apply Subtype.ext
  change physEmbed (htpow N u) = _
  rw [physEmbed_htpow]
  exact (productForm_val u hu hH N).symm

/-- The high-angle occupation mask has the same product defect as the
physical normalized-wave energy mask. -/
theorem occupation_product_defect (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N)
    (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (E : ℝ) (hE : 0 < E)
    (P : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (bas L hκ hN m) = mask L κ N E m • bas L hκ hN m) :
    ‖HighMomentsOps.wvec N u - P (HighMomentsOps.wvec N u)‖ ^ 2 ≤
      QuantumNLS.ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) / E := by
  obtain ⟨P₀, hP₀, _, _, htransport⟩ := energyProjection_phys (L := L) hκ hN E ∅ (fun _ => 0)
  let T := symmetricPosition L N
  let Q : HN L N →L[ℂ] HN L N :=
    T.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (P₀.comp T.toContinuousLinearEquiv.toContinuousLinearMap)
  have hPQ : P = Q := by
    apply QuantumNLS.TransferNormality.ext_of_hilbertBasis (bas L hκ hN)
    intro m
    rw [hP m]
    exact (htransport m).symm
  have htrans (v : HN L N) : T (P v) = P₀ (T v) := by
    rw [hPQ]
    change T (T.symm (P₀ (T v))) = _
    exact T.apply_symm_apply _
  have hp := product_projection_defect κ hκ N (by omega) u hu hH E hE P₀ hP₀
  calc
    _ = ‖T (HighMomentsOps.wvec N u - P (HighMomentsOps.wvec N u))‖ ^ 2 := by rw [T.norm_map]
    _ = ‖ContactOperator.valSym (productForm u hu hH N) -
      P₀ (ContactOperator.valSym (productForm u hu hH N))‖ ^ 2 := by
        rw [map_sub, htrans, product_position u hu hH N]
    _ ≤ _ := hp

#print axioms product_position
#print axioms occupation_product_defect
end QuantumNLS.TerraMultiRound91OccupationProjection
