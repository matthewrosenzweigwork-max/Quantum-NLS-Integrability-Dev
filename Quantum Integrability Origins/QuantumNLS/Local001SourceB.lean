import QuantumNLS.Local001VectorSupB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral

theorem sourceResolvent_eq_candidate {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hL : 0 < L) (hr : 0 < r) (hsmall : r < spacing L / 2)
    {n : ℤ} {z : ℂ} (hz : OnGamma L r n z) :
    LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z =
      freeResolventCandidate L n z := by
  let hR := freeResolventCandidate_isResolvent (L := L) (κ := κ) hL hr hsmall hz
  have hex : ∃ R, LocalSpectral.IsResolvent L κ (fun _ => 0)
      (LocalSpectral.parity n) z R := ⟨freeResolventCandidate L n z, hR⟩
  rw [LocalSpectral.resolvent, dif_pos hex]
  exact LocalSpectral.IsResolvent.unique (Classical.choose_spec hex) hR


#print axioms sourceResolvent_eq_candidate

theorem sourceResolvent_norm_le {L r : ℝ} [Fact (0 < L)]
    (hL : 0 < L) (κ : ℝ) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z) :
    ‖LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z‖ ≤ r⁻¹ := by
  have hR := freeResolventCandidate_isResolvent (L := L) (κ := κ) hL hr hsmall hz
  have hEq := sourceResolvent_eq_freeDiagonal L hL κ n hr hsmall hz hR
  rw [sourceResolvent_eq_candidate (L := L) (κ := κ) hL hr hsmall hz, hEq]
  exact freeDiagonalResolvent_norm_le L hL n hr hsmall hz


#print axioms sourceResolvent_norm_le

theorem sourceResolvent_ae_sup_bound {L r : ℝ} [Fact (0 < L)]
    (hL : 0 < L) (κ : ℝ) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (f : VectorInterval L) :
    ∀ᵐ (x : ℝ) ∂μI L, ‖(LocalSpectral.resolvent L κ (fun _ => 0)
      (LocalSpectral.parity n) z f) x‖ ≤ resolventConstant L r * ‖f‖ := by
  have hR := freeResolventCandidate_isResolvent (L := L) (κ := κ) hL hr hsmall hz
  have hEq := sourceResolvent_eq_freeDiagonal L hL κ n hr hsmall hz hR
  rw [sourceResolvent_eq_candidate (L := L) (κ := κ) hL hr hsmall hz, hEq]
  simpa [resolventConstant, resolventConstantSq] using
    freeDiagonal_ae_sup_bound L hL n hr hsmall hz f

#print axioms sourceResolvent_ae_sup_bound

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
