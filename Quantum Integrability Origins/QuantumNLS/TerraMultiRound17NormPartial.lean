import QuantumNLS.TerraMultiRound17ActionPartial

/-! Action sequence and squared norm evolution on an existing local solution.
This does not assert existence of a global flow. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set
open QuantumNLS.D01LocalPrimitive
namespace QuantumNLS.TerraMultiRound17NormPartial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem action_and_mass_on_solution (S : Hyp H) {a b : ℝ} (hzero : (0 : ℝ) ∈ Ioo a b)
    (u : ℝ → H) (hu : ∀ t ∈ Ioo a b, HasDerivAt u (S.Y (u t)) t) :
    ∀ t ∈ Ioo a b,
      S.act (u t) = Real.exp t • S.act (u 0) ∧
      ‖u t‖ ^ 2 = Real.exp t * ‖u 0‖ ^ 2 := by
  intro t ht
  have hc := QuantumNLS.TerraMultiRound17ActionPartial.action_on_solution S hzero u hu t ht
  constructor
  · apply lp.ext
    funext n
    simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using hc n
  · rw [← S.act_mass (u t), ← S.act_mass (u 0)]
    calc
      (∑' n, S.act (u t) n) = ∑' n, Real.exp t * S.act (u 0) n := tsum_congr hc
      _ = Real.exp t * ∑' n, S.act (u 0) n :=
        (Memℓp.summable_of_one (lp.memℓp (S.act (u 0)))).tsum_mul_left (Real.exp t)

#print axioms action_and_mass_on_solution
end QuantumNLS.TerraMultiRound17NormPartial
