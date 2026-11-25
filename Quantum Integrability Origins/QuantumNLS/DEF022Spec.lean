import QuantumNLS.ClassicalCharges

/-! integrator-authored trusted spec for DEF-022 (definitions.tex:133-135), Riccati charges.
For smooth L-periodic u: v₁ = u, v_{J+1} = −i∂ₓv_J + κ ū Σ_{a=1}^{J-1} v_a v_{J-a} (written with
J = j+1), I_j = ∫_{T_L} ū v_j (one period, mass-L Lebesgue), and the three printed particular cases. -/

open ComplexConjugate
open QuantumNLS.ClassicalCharges

namespace QuantumNLS.DEF022Spec

def Spec : Prop :=
  ∀ (L κ : ℝ) (u : ℝ → ℂ), SmoothPeriodic L u →
    vseq κ u 1 = u ∧
    (∀ j : ℕ, vseq κ u (j + 2) = fun x =>
        -Complex.I * deriv (vseq κ u (j + 1)) x + (κ : ℂ) * conj (u x) *
          ∑ a ∈ Finset.Icc 1 j, vseq κ u a x * vseq κ u (j + 1 - a) x) ∧
    (∀ j : ℕ, charge L κ u j = ∫ x in (0 : ℝ)..L, conj (u x) * vseq κ u j x) ∧
    charge L κ u 1 = ((∫ x in (0 : ℝ)..L, ‖u x‖ ^ 2 : ℝ) : ℂ) ∧
    charge L κ u 2 = (∫ x in (0 : ℝ)..L, conj (u x) * (-Complex.I * deriv u x)) ∧
    charge L κ u 3 = ((∫ x in (0 : ℝ)..L, (‖deriv u x‖ ^ 2 + κ * ‖u x‖ ^ 4) : ℝ) : ℂ)

theorem spec : Spec := by
  intro L κ u hu
  exact ⟨vseq_one κ u, vseq_succ κ u, fun j => rfl, charge_one L κ u, charge_two L κ u,
    charge_three L κ hu⟩

end QuantumNLS.DEF022Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.DEF022Spec.spec
  IO.println s!"DEF022Spec.spec axioms: {ax}"
