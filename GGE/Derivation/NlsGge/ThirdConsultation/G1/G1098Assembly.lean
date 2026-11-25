import NlsGge.ThirdConsultation.G1.G1098Host
import NlsGge.ThirdConsultation.G1.G1098Synth
import NlsGge.ThirdConsultation.G1.G1098RealBasis
set_option autoImplicit false
open NlsGge.Pilot

/- G1-098 SUPPORTING MODULE M5-UNIQ (proof development, AUTHOR; not reviewed).
   Partial M5 (assembly): the uniqueness half only. Any real-linear bounded operator that takes the
   prescribed values on the normalized reference family is determined by those values (density of the
   real Hilbert basis from M4 through the synthesis uniqueness lemma eq_of_basis).
   Consequently `mixedSquaredOperator u v` equals every bounded operator with the defining property.
   The existence half (bounded extension) is NOT proved here: it needs M1, M2 and M3 (see the STOP file). -/

namespace NlsGge.Atomic.G1098Assembly

open NlsGge.GKDefinitionDesign NlsGge.Atomic.G1098Basis NlsGge.Atomic.G1098Synth

noncomputable section

theorem mixedBasisVec_eq_smul (j : ℤ × Bool) :
    mixedBasisVec j = (‖mixedReference j.1 j.2‖⁻¹ : ℝ) • mixedReference j.1 j.2 := by
  unfold mixedBasisVec
  exact real_smul_of_complex_smul _ _

/-- Uniqueness on the normalized reference family (no existence assumed). -/
theorem eq_of_mixedReference (K K' : PhysicalL2 →L[ℝ] PhysicalL2)
    (hK : ∀ (n : ℤ) (minus : Bool), K (mixedReference n minus) = K' (mixedReference n minus)) :
    K = K' := by
  apply eq_of_basis mixedRealBasis K K'
  intro j
  rw [mixedRealBasis_apply, mixedBasisVec_eq_smul, map_smul, map_smul, hK]

/-- If an operator has the defining property of `mixedSquaredOperator`, the chosen operator equals it. -/
theorem mixedSquaredOperator_eq_of (u v : PhysicalL2) (A : PhysicalL2 →L[ℝ] PhysicalL2)
    (hA : ∀ (n : ℤ) (minus : Bool), A (mixedReference n minus) = mixedColumn u v n minus) :
    mixedSquaredOperator u v = A := by
  have h : ∃ B : PhysicalL2 →L[ℝ] PhysicalL2,
      ∀ n : ℤ, ∀ minus : Bool, B (mixedReference n minus) = mixedColumn u v n minus :=
    ⟨A, hA⟩
  unfold mixedSquaredOperator
  rw [dif_pos h]
  apply eq_of_mixedReference
  intro n minus
  rw [(Classical.choose_spec h) n minus, hA n minus]

end

end NlsGge.Atomic.G1098Assembly

