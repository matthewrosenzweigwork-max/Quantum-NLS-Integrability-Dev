import QuantumNLS.TransferSeparationOnShell

/-! integrator-authored trusted spec for R-533B0EC6 `basis:lem:separation` (periodic_basis.tex:399-404).
s_q(z) = ∏_j (1 + ic/(z − q_j)) + e^{iLz} ∏_j (1 − ic/(z − q_j)) (basis:eq:spectralfunction).
For c > 0 (and L > 0): (1) two real rapidity tuples whose transfer functions agree off their real poles
have the same multiset; (2) if both are on shell (distinct rapidities solving the Bethe equations
e^{iLq_j} = ∏_{k≠j} (q_j − q_k + ic)/(q_j − q_k − ic), as the source requires) with different
multisets, their values differ at some real x, which may be chosen outside any finite set and away from
the poles. All objects written out here. -/

namespace QuantumNLS.R533Spec

noncomputable def s (L c : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (∏ j, (1 + Complex.I * c / (z - q j))) + Complex.exp (Complex.I * L * z) * ∏ j, (1 - Complex.I * c / (z - q j))

def onShell (L c : ℝ) {N : ℕ} (q : Fin N → ℝ) : Prop :=
  Function.Injective q ∧ ∀ j : Fin N, Complex.exp (Complex.I * L * q j) =
    ∏ k ∈ Finset.univ.erase j, (((q j : ℂ) - q k + Complex.I * c) / ((q j : ℂ) - q k - Complex.I * c))

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ), 0 < L → 0 < c →
    (∀ p q : Fin N → ℝ, (∀ z : ℂ, (∀ j, z ≠ p j) → (∀ j, z ≠ q j) → s L c p z = s L c q z) →
      Multiset.map p Finset.univ.val = Multiset.map q Finset.univ.val) ∧
    (∀ p q : Fin N → ℝ, onShell L c p → onShell L c q →
      Multiset.map p Finset.univ.val ≠ Multiset.map q Finset.univ.val →
      ∀ F : Finset ℝ, ∃ x : ℝ, x ∉ F ∧ (∀ j, x ≠ p j ∧ x ≠ q j) ∧ s L c p x ≠ s L c q x)

theorem spec : Spec := by
  intro N L c hL hc
  obtain ⟨h1, h2⟩ := QuantumNLS.TransferSeparationOnShell.basis_lem_separation_literal (N := N) hL hc
  refine ⟨fun p q h => h1 p q fun z hz => ?_, fun p q hp hq hne F => h2 p q hp hq hne F⟩
  obtain ⟨hp, hq⟩ := QuantumNLS.TransferSeparation.not_mem_poles hz
  exact h z hp hq

end QuantumNLS.R533Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R533Spec.spec
  IO.println s!"R533Spec.spec axioms: {ax}"
