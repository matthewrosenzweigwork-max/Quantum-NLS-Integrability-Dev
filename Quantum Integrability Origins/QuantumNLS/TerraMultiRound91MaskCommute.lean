import QuantumNLS.TerraMultiRound91ProductCompression
import QuantumNLS.HighAngleRotations
import QuantumNLS.BetheSpectralCharges

/-! Spectral masks commute with both actual charge evolution and count
rotations on the whole sector, not just basis vectors. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.BetheCoefficientTransform
open QuantumNLS.BetheSpectralCharges QuantumNLS.HighAngleRotations QuantumNLS.CountRotations
namespace QuantumNLS.TerraMultiRound91MaskCommute
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem mask_evolution_commute (b : BetheBasis L N) (ev : BetheLabels.MArr N → ℝ) (t : ℝ)
    (P : HN L N →L[ℂ] HN L N) (μ : BetheLabels.MArr N → ℂ)
    (hP : ∀ m, P (b m) = μ m • b m) (v : HN L N) :
    P (evolution b ev t v) = evolution b ev t (P v) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply, HilbertDiagOp.eig_coeff b P μ hP, evolution_coord]
  ring

theorem mask_rotation_commute (b : BetheBasis L N) (θ : AngleTorus)
    (P : HN L N →L[ℂ] HN L N) (μ : BetheLabels.MArr N → ℂ)
    (hP : ∀ m, P (b m) = μ m • b m) (v : HN L N) :
    P (quantumRotation b θ v) = quantumRotation b θ (P v) := by
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply, HilbertDiagOp.eig_coeff b P μ hP, rotation_coeff]
  ring

#print axioms mask_evolution_commute
#print axioms mask_rotation_commute
end QuantumNLS.TerraMultiRound91MaskCommute
