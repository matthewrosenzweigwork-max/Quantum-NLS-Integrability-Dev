import QuantumNLS.TerraMultiRound51TaylorLeading
import QuantumNLS.TerraMultiRound49SobolevBridge

/-! The zero-shift coefficient for the four alternating physical factors
is the quartic integral. Identifying this kernel with a physical tree and
constructing the continuous polynomial remain separate. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.TerraMultiRound52Quartic
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound49SobolevBridge
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound51TaylorLeading

variable {L : ℝ} [Fact (0 < L)]

def quarticFactors (k : ℕ) (u : Ell2) : Fin 4 → Hk L k :=
  ![physicalToHk k (jEll u), physicalToHk k u,
    physicalToHk k (jEll u), physicalToHk k u]

theorem conjugate_rep {k : ℕ} (hk : 1 ≤ k) (u : Ell2) (x : AddCircle L) :
    contRep hk (physicalToHk k (jEll u)) x =
      starRingEnd ℂ (contRep hk (physicalToHk k u) x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ x => rw [physicalToHk_conj_rep hk, physicalToHk_rep hk]

theorem quartic_leading {k n : ℕ} (hk : 1 ≤ k) (u : Ell2)
    (paths : Fin 4 → Finset (Fin n)) :
    integratedCoeff (Cfun (quarticFactors (L := L) k u)) paths 0 =
      ∫ x : AddCircle L, ((‖contRep hk (physicalToHk k u) x‖ ^ 4 : ℝ) : ℂ)
        ∂(volume : Measure (AddCircle L)) := by
  rw [integratedCoeff_zero, Cfun_eq_cont hk]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Pi.zero_apply, AddCircle.coe_zero, add_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    quarticFactors, Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
  simp_rw [conjugate_rep hk u x]
  let z := contRep hk (physicalToHk k u) x
  have hz : starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  change (starRingEnd ℂ z * (z * (starRingEnd ℂ z * z))) = _
  calc
    _ = (starRingEnd ℂ z * z) * (starRingEnd ℂ z * z) := by ring
    _ = ((‖z‖ ^ 4 : ℝ) : ℂ) := by rw [hz]; push_cast; ring

#print axioms conjugate_rep
#print axioms quartic_leading
end QuantumNLS.TerraMultiRound52Quartic
