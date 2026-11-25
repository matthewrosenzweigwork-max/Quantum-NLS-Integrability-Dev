import QuantumNLS.TerraMultiRound18Pullbacks

/-! Conditional assembly of the complete D01 flow lemma. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket
open QuantumNLS.TerraMultiRound18Flow QuantumNLS.TerraMultiRound18AnalyticFlow
open QuantumNLS.TerraMultiRound18Pullbacks
namespace QuantumNLS.TerraMultiRound19D01Full

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complete flow, its analytic inverse, and all four identities in
`global-D01-flow-identities`. The sole additional premise is the named GP-04
compact-local analytic dependence remainder. -/
theorem global_D01_completeness (S : Hyp H) (ha : GP04CompactLocalAnalyticity S) :
    ∃ F : ℝ → H → H,
      (∀ u, F 0 u = u) ∧
      (∀ u t, HasDerivAt (fun s => F s u) (S.Y (F t u)) t) ∧
      (∀ u (γ : ℝ → H), γ 0 = u →
        (∀ t, HasDerivAt γ (S.Y (γ t)) t) → ∀ t, F t u = γ t) ∧
      (∀ t s u, F (t + s) u = F t (F s u)) ∧
      (∀ t u, F (-t) (F t u) = u ∧ F t (F (-t) u) = u) ∧
      (∀ t u, AnalyticAt ℝ (F t) u) ∧
      (∀ t u, S.act (F t u) = Real.exp t • S.act u) ∧
      (∀ t u, ‖F t u‖ = Real.exp (t / 2) * ‖u‖) ∧
      (∀ t u h k, omega (fderiv ℝ (F t) u h) (fderiv ℝ (F t) u k) =
        Real.exp t * omega h k) ∧
      (∀ t u h, S.abar (F t u) (fderiv ℝ (F t) u h) =
        Real.exp t * S.abar u h) := by
  refine ⟨flow S, fun u => (flow_spec S u).1, fun u t => (flow_spec S u).2 t, ?_,
    flow_add S, flow_inverse S, analytic_initial_dependence S ha,
    fun t u => (flow_action_mass S t u).1, ?_, conformal_symplectic S ha,
    one_form_pullback S ha⟩
  · intro u γ h0 hd t
    exact flow_eq_of_sol S h0 hd t
  · intro t u
    have hs := (flow_action_mass S t u).2
    have he : Real.exp (t / 2) ^ 2 = Real.exp t := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hp : 0 ≤ Real.exp (t / 2) * ‖u‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
    have hn := norm_nonneg (flow S t u)
    nlinarith [sq_nonneg (‖flow S t u‖ - Real.exp (t / 2) * ‖u‖),
      sq_nonneg (‖flow S t u‖ + Real.exp (t / 2) * ‖u‖)]

#print axioms global_D01_completeness
end QuantumNLS.TerraMultiRound19D01Full
