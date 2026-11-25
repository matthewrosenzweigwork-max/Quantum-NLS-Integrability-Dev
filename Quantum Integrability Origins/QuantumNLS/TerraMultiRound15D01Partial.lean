import QuantumNLS.D01LocalPrimitive

/-! Source: `lem:global-D01-completeness`, action-derivative calculation.
This is a partial result under exactly the reconstruction hypotheses `Hyp`.
It does not assert existence, completeness, or regularity of the flow. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.TerraMultiRound15D01Partial

open QuantumNLS.SymplecticBracket QuantumNLS.D01LocalPrimitive

/-- The pointwise action derivative, vanishing self-contraction, and compact
action segments used in the completeness proof. These hold everywhere under the printed `Hyp`. -/
theorem action_derivative_and_self_contraction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Hyp H) :
    (∀ (u : H) (n : ℤ), fderiv ℝ (fun v => S.act v n) u (S.Y u) = S.act u n) ∧
    (∀ u : H, S.abar u (S.Y u) = 0) ∧
    (∀ (u : H) (a b : ℝ), IsCompact
      (S.act ⁻¹' ((fun t : ℝ => Real.exp t • S.act u) '' Set.Icc a b))) := by
  constructor
  · intro u n
    rw [← omega_hamField, omega_swap, Hyp.Y, omega_Winv, S.abar_X, neg_neg]
  · constructor
    · intro u
      rw [← omega_Winv (S.abar u) (S.Y u)]
      exact omega_self _
    · intro u a b
      apply S.act_proper
      · exact isCompact_Icc.image (Real.continuous_exp.smul continuous_const)
      · intro x hx n
        obtain ⟨t, ht, rfl⟩ := hx
        change 0 ≤ Real.exp t * S.act u n
        exact mul_nonneg (Real.exp_pos t).le (S.act_nonneg u n)

#print axioms action_derivative_and_self_contraction

end QuantumNLS.TerraMultiRound15D01Partial
