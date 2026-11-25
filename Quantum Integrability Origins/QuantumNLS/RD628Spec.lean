import QuantumNLS.PairedPlaneLaw

/-! integrator-authored trusted spec for R-D6286EDD `intr:plane:lem:pc-product` (intrinsic/plane.tex:49).
Objects pinned by the printed formulas: g = κ/L, k_j = 2πj/L, h_j = k_j² + 2g, ω_j = k_j √(k_j² + 4g),
ζ_j = (h_j − ω_j)/(h_j + ω_j), p_* = ∏_{j≥1}(1 − ζ_j); 𝒞 = finitely supported η on ℤ∖{0};
P(η) = p_* ∏ ζ_j^{η_j} if η_j = η_{−j} for all j ≥ 1, else 0. For κ > 0 (and L > 0):
0 < ζ_j < 1, Σζ_j < ∞, the product converges to p_* with 0 < p_* < 1, and P is a probability on 𝒞. -/

open Filter Topology QuantumNLS.PairedPlaneLaw

namespace QuantumNLS.RD628Spec

open scoped Classical in

def Spec : Prop :=
  ∀ (L κ : ℝ), 0 < L → 0 < κ →
    (∀ j : ℕ+, zetaC L κ j =
      ((2 * Real.pi * (j : ℝ) / L) ^ 2 + 2 * (κ / L) -
          (2 * Real.pi * (j : ℝ) / L) * Real.sqrt ((2 * Real.pi * (j : ℝ) / L) ^ 2 + 4 * (κ / L))) /
        ((2 * Real.pi * (j : ℝ) / L) ^ 2 + 2 * (κ / L) +
          (2 * Real.pi * (j : ℝ) / L) * Real.sqrt ((2 * Real.pi * (j : ℝ) / L) ^ 2 + 4 * (κ / L)))) ∧
    pStar L κ = ∏' j : ℕ+, (1 - zetaC L κ j) ∧
    (∀ η : Config, pairedLaw L κ η =
      if (∀ j : ℕ+, η (posIdx j) = η (negIdx j)) then pStar L κ * ∏' j : ℕ+, zetaC L κ j ^ η (posIdx j)
      else 0) ∧
    (∀ j : ℕ+, 0 < zetaC L κ j ∧ zetaC L κ j < 1) ∧ Summable (zetaC L κ) ∧
    HasProd (fun j : ℕ+ => 1 - zetaC L κ j) (pStar L κ) ∧
    (0 < pStar L κ ∧ pStar L κ < 1) ∧
    (∀ η : Config, 0 ≤ pairedLaw L κ η) ∧ HasSum (pairedLaw L κ) 1

theorem spec : Spec := by
  intro L κ hL hκ
  obtain ⟨h1, h2, h3, -, h5, h6, h7, -⟩ := pc_product hL hκ
  exact ⟨fun j => rfl, rfl, fun η => rfl, h1, h2, h3, h5, h6, h7⟩

end QuantumNLS.RD628Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RD628Spec.spec
  IO.println s!"RD628Spec.spec axioms: {ax}"
