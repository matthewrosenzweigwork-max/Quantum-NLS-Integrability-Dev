import QuantumNLS.Def024CubicGradient

/-!
# DEF-024, stage C2: the order-2 Hamiltonian-flow predicate is exactly the classical cubic NLS problem

Source: `DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex:145-149`); the frozen
`HierarchyFlow.IsHamFlow` for `F = Re I_3 = hamiltonian L κ 2` (DEF-022 charge of order 3, DEF-023
equation `iu_t = −u_xx + 2κ|u|²u`); the gradient of stage C1 (`Def024CubicGradient.gradient_two`).

What is proved (`0 < L` is used only for the uniqueness of the DEF-015 gradient):
* `isHamFlow_two_iff`: a map `Φ` is an `IsHamFlow` of `Re I_3` if and only if, for every smooth
  periodic `u`, `Φ 0 u = u`, `(s, x) ↦ Φ s u (x)` is jointly `C^∞`, and for every `s` the profile
  `Φ s u` is smooth periodic with `∂_s Φ s u (x) = −i · (−∂ₓ²Φ + 2κ|Φ|²Φ)(s, x)`.

Consequence (the precise missing content of order 2): the frozen `IsHamFlow` clause for `r = 2` is
the classical smooth-in-`(s, x)` solution problem for `i∂_s u = −∂ₓ²u + 2κ|u|²u` on smooth periodic
data (global in `s`). It is NOT supplied by DEF-023 (`PhysicalCubic`, `L2Flow`): those give only
the `L²`-Duhamel solution class `C(ℝ;L²) ∩ L⁴_loc`, with no smoothness in `x` or `s`, and no
classical equation. Existence, joint smoothness, and uniqueness of an order-2 flow are therefore
NOT proved here, and this module does not assume them.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate ContDiff

namespace QuantumNLS.Def024CubicClassical

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024Gradient
  QuantumNLS.Def024CubicGradient

variable {L : ℝ}

/-- **Reduction of the order-2 `IsHamFlow` clause to the classical cubic NLS problem.** The
gradient in the frozen definition is unique on smooth periodic data (`gradient_unique`), so the
existential over `g` is replaced by `cubicGrad κ (Φ s u)`. -/
theorem isHamFlow_two_iff (hL : 0 < L) (κ : ℝ) (Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ)) :
    IsHamFlow L (hamiltonian L κ 2) Φ ↔
      ∀ u : ℝ → ℂ, SmoothPeriodic L u →
        Φ 0 u = u ∧ ContDiff ℝ ∞ (fun p : ℝ × ℝ => Φ p.1 u p.2) ∧
          ∀ s : ℝ, SmoothPeriodic L (Φ s u) ∧
            ∀ x : ℝ, HasDerivAt (fun s' => Φ s' u x) (-Complex.I * cubicGrad κ (Φ s u) x) s := by
  constructor
  · intro hΦ u hu
    obtain ⟨h0, hsm, hs⟩ := hΦ u hu
    refine ⟨h0, hsm, fun s => ?_⟩
    obtain ⟨hS, g, hg, hd⟩ := hs s
    have hgs : g = cubicGrad κ (Φ s u) := gradient_unique hL hg (cub_gradient κ hS)
    refine ⟨hS, fun x => ?_⟩
    rw [← hgs]
    exact hd x
  · intro hΦ u hu
    obtain ⟨h0, hsm, hs⟩ := hΦ u hu
    refine ⟨h0, hsm, fun s => ?_⟩
    obtain ⟨hS, hd⟩ := hs s
    exact ⟨hS, cubicGrad κ (Φ s u), cub_gradient κ hS, hd⟩

#print axioms isHamFlow_two_iff

end QuantumNLS.Def024CubicClassical
