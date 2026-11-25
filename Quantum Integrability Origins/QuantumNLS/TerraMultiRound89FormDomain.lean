import QuantumNLS.ContactOperator

/-! Operator-domain vectors have canonical contact-form representatives,
with the full variational identity. This is a step toward the Bethe
form-core and does not claim the product lies in the operator domain. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
namespace QuantumNLS.TerraMultiRound89FormDomain
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

/-- The operator-domain embedding and its variational form identity. -/
theorem operator_domain_form (hc : 0 ≤ c) (x : SymL2 L N)
    (hx : x ∈ (Hop (L := L) (N := N) c hc).domain) :
    ∃ y : VSym L N, valSym y = x ∧
      ∀ z : VSym L N, q c z.1 y.1 = ⟪valSym z, Hop c hc ⟨x,hx⟩⟫_ℂ := by
  have hxcopy := hx
  obtain ⟨g, hg⟩ : ∃ g : SymL2 L N, Rop c hc g = x := hxcopy
  have hT : Tinv c hc ⟨x, hx⟩ = g := Tinv_apply_of_eq hc ⟨x, hx⟩ g hg
  have hH : Hop c hc ⟨x, hx⟩ = g - x := by
    change Tinv c hc ⟨x, hx⟩ - x = g - x
    rw [hT]
  refine ⟨psi c hc g, ?_, ?_⟩
  · exact (Rop_eq_valSym_psi hc g).symm.trans hg
  · intro z
    rw [hH, ← hg]
    exact variational_of_domain hc g z

#print axioms operator_domain_form
end QuantumNLS.TerraMultiRound89FormDomain
