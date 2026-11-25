import QuantumNLS.HighRootLocalization

/-! integrator-authored trusted spec for R-9A585DC2 `QG:prop:high-root-localization`
(core/QUANTUM_GAUGE_COMPONENTS.tex:144-154 with QG:eq:our-bethe, ω = 2π/L, c = κ/N). Fix L, κ, E > 0.
There are constants C_E, R_E (chosen from L, κ, E only, before N, the configuration and the label) such
that for every N and every on-shell configuration (strictly increasing q, nondecreasing integer labels n,
L q_j = 2π n_j + 2 Σ_{ℓ≠j} arctan((κ/N)/(q_j − q_ℓ))) with N⁻¹ Σ_j q_j² ≤ E, and every j whose label
satisfies |n_j| ≥ R_E: |q_j − ω n_j| ≤ C_E/|ω n_j|. (Per-j form of "every occurring label n with |n| ≥ R_E
and every j with n_j = n".) -/

namespace QuantumNLS.R9A58Spec

def Spec : Prop :=
  ∀ (L κ E : ℝ), 0 < L → 0 < κ → 0 < E →
    ∃ C R : ℝ, 0 < R ∧ ∀ (N : ℕ) (n : Fin N → ℤ) (q : Fin N → ℝ),
      StrictMono q → Monotone n →
      (∀ j, L * q j = 2 * Real.pi * n j +
        2 * ∑ l ∈ Finset.univ.erase j, Real.arctan ((κ / N) / (q j - q l))) →
      (N : ℝ)⁻¹ * ∑ j, q j ^ 2 ≤ E →
      ∀ j, R ≤ |(n j : ℝ)| →
        |q j - 2 * Real.pi / L * n j| ≤ C / |2 * Real.pi / L * n j|

theorem spec : Spec := by
  intro L κ E hL hκ hE
  obtain ⟨C, R, hR, h⟩ := HighRootLocalization.high_root_localization hL hκ E hE
  refine ⟨C, R, hR, fun N n q hq hn hB hEn j hj => ?_⟩
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (fun h0 => (h0 ▸ j).elim0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact h N n q ⟨div_pos hκ hN0, hq, hn, fun j => hB j⟩ hEn j hj

end QuantumNLS.R9A58Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R9A58Spec.spec
  IO.println s!"R9A58Spec.spec axioms: {ax}"
