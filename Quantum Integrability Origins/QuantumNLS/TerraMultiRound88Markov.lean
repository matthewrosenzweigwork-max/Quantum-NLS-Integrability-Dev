import QuantumNLS.Ext025B3DiagonalForms

/-! The scalar spectral Markov inequality on an actual ℓ² vector with a
finite first moment. This is a helper: the identification of the contact
form with the Bethe first moment and the physical projection are not assumed
or claimed here. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound88Markov
open QuantumNLS.OccupationHilbert QuantumNLS.Ext025B3DiagonalForms

/-- The discarded spectral weight above a strictly positive threshold is at
most the first moment divided by that threshold. No operator-domain condition
is required. -/
theorem spectral_markov {ι : Type*} (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (v : L2 ι) (hv : InFormDomain ev v) (E : ℝ) (hE : 0 < E) :
    (∑' i, if E < ev i then ‖v i‖ ^ 2 else 0) ≤ ‖formRoot ev v hv‖ ^ 2 / E := by
  classical
  have hs : Summable (fun i => ev i * ‖v i‖ ^ 2) := (formDomain_iff ev hev v).mp hv
  have hdom : Summable (fun i => ev i * ‖v i‖ ^ 2 / E) := hs.div_const E
  have hpoint : ∀ i, (if E < ev i then ‖v i‖ ^ 2 else 0) ≤ ev i * ‖v i‖ ^ 2 / E := by
    intro i
    by_cases hi : E < ev i
    · simp only [hi, ite_true]
      rw [le_div_iff₀ hE]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hi.le (sq_nonneg ‖v i‖)
    · simp only [hi, ite_false]
      exact div_nonneg (mul_nonneg (hev i) (sq_nonneg _)) hE.le
  have ht : Summable (fun i => if E < ev i then ‖v i‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity) hpoint hdom
  calc
    _ ≤ ∑' i, ev i * ‖v i‖ ^ 2 / E := ht.tsum_le_tsum hpoint hdom
    _ = (∑' i, ev i * ‖v i‖ ^ 2) / E := tsum_div_const
    _ = _ := by rw [formRoot_norm_sq ev hev v hv]

#print axioms spectral_markov
end QuantumNLS.TerraMultiRound88Markov
