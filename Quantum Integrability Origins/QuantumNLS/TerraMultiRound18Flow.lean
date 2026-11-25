import QuantumNLS.TerraMultiRound18GlobalExistence
import QuantumNLS.TerraMultiRound18GlobalUniqueness

/-! The complete D01 flow and its action and mass identities, provided by
finite-horizon continuation and uniqueness. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open QuantumNLS.D01LocalPrimitive
namespace QuantumNLS.TerraMultiRound18Flow

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def flow (S : Hyp H) (t : ℝ) (u : H) : H :=
  (QuantumNLS.TerraMultiRound18GlobalExistence.exists_global S u).choose t

theorem flow_spec (S : Hyp H) (u : H) :
    flow S 0 u = u ∧ ∀ t, HasDerivAt (fun s => flow S s u) (S.Y (flow S t u)) t :=
  (QuantumNLS.TerraMultiRound18GlobalExistence.exists_global S u).choose_spec

theorem flow_eq_of_sol (S : Hyp H) {u : H} {γ : ℝ → H} (hγ0 : γ 0 = u)
    (hγ : ∀ t, HasDerivAt γ (S.Y (γ t)) t) (t : ℝ) : flow S t u = γ t := by
  have heq : (fun s => flow S s u) = γ :=
    QuantumNLS.TerraMultiRound18GlobalUniqueness.global_unique S (flow_spec S u).2 hγ
      (t₀ := 0) (by rw [(flow_spec S u).1, hγ0])
  exact congrFun heq t

theorem flow_add (S : Hyp H) (t s : ℝ) (u : H) :
    flow S (t + s) u = flow S t (flow S s u) := by
  have hd : ∀ r, HasDerivAt (fun r => flow S (r + s) u) (S.Y (flow S (r + s) u)) r :=
    fun r => HasDerivAt.comp_add_const r s ((flow_spec S u).2 (r + s))
  exact (flow_eq_of_sol S (γ := fun r => flow S (r + s) u) (by simp only [zero_add]) hd t).symm

theorem flow_inverse (S : Hyp H) (t : ℝ) (u : H) :
    flow S (-t) (flow S t u) = u ∧ flow S t (flow S (-t) u) = u := by
  constructor
  · rw [← flow_add, neg_add_cancel, (flow_spec S u).1]
  · rw [← flow_add, add_neg_cancel, (flow_spec S u).1]

theorem flow_action_mass (S : Hyp H) (t : ℝ) (u : H) :
    S.act (flow S t u) = Real.exp t • S.act u ∧
      ‖flow S t u‖ ^ 2 = Real.exp t * ‖u‖ ^ 2 := by
  have h := QuantumNLS.TerraMultiRound18GlobalUniqueness.global_action_and_mass S
    (fun s => flow S s u) (flow_spec S u).2 t
  simpa only [(flow_spec S u).1] using h

#print axioms flow_spec
#print axioms flow_eq_of_sol
#print axioms flow_add
#print axioms flow_inverse
#print axioms flow_action_mass
end QuantumNLS.TerraMultiRound18Flow
