import QuantumNLS.SymplecticBracket
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# R-C4F43CA8 `thm:root-involution`, part (2C-a): the real Poisson bracket of two summable series

Source: `source/chapters/foundations/ROOT_transfer_involution.tex:98` (the interchange of the bracket with the
infinite symbol series, used before the dominated-convergence step).

Realized inputs (frozen): `SymplecticBracket.pbR`, `pbR_eq_omega` (`{F,G} = Ω(∇F,∇G)`, unconditional),
`SymplecticBracket.gradient`, `omega`; Mathlib `hasFDerivAt_tsum_of_isPreconnected`.

Proved here (standard axioms only), for real functions on a complex Hilbert space `H` (realified through
`InnerProductSpace.complexToReal`, as in `SymplecticBracket`):
* `hasSum_inner_left'`, `hasSum_inner_right'`: `HasSum` of inner products with a convergent sum in either slot.
* `hasSum_gradient_tsum`: if the derivatives are summable on a ball `B(u,ρ)`, then the gradients of the terms
  sum (in `H`) to the SymplecticBracket.gradient of the sum.
* `pbR_tsum_tsum`: `{Σ f_n, Σ g_m}(u) = Σ_n Σ_m {f_n, g_m}(u)` (iterated sums, no product summability needed).

Remainder for the complex bracket `pbC` and the identification with `productSymbol`: part 2C-b (not here).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.RootPoissonSeries

open QuantumNLS.SymplecticBracket

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hasSum_inner_left' (a : ℕ → H) (A : H) (ha : HasSum a A) (b : H) :
    HasSum (fun n => ⟪a n, b⟫_ℂ) ⟪A, b⟫_ℂ := by
  have h1 : HasSum (fun n => ⟪b, a n⟫_ℂ) ⟪b, A⟫_ℂ := by
    simpa using (innerSL ℂ b).hasSum ha
  have h2 := h1.mapL Complex.conjCLE.toContinuousLinearMap
  simpa [inner_conj_symm] using h2

theorem hasSum_inner_right' (a : H) (b : ℕ → H) (B : H) (hb : HasSum b B) :
    HasSum (fun m => ⟪a, b m⟫_ℂ) ⟪a, B⟫_ℂ := by
  simpa using (innerSL ℂ a).hasSum hb

/-- The gradients of the terms of a series on a ball sum to the SymplecticBracket.gradient of the sum. -/
theorem hasSum_gradient_tsum (f : ℕ → H → ℝ) (F' : ℕ → H → (H →L[ℝ] ℝ)) (a : ℕ → ℝ) (u : H)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hd : ∀ n, ∀ x ∈ ball u ρ, HasFDerivAt (f n) (F' n x) x)
    (hb : ∀ n, ∀ x ∈ ball u ρ, ‖F' n x‖ ≤ a n) (ha : Summable a) (hf0 : Summable fun n => f n u) :
    HasSum (fun n => SymplecticBracket.gradient (f n) u) (SymplecticBracket.gradient (fun y => ∑' n, f n y) u) := by
  have hu : u ∈ ball u ρ := mem_ball_self hρ
  have hfs : HasFDerivAt (fun y => ∑' n, f n y) (∑' n, F' n u) u :=
    hasFDerivAt_tsum_of_isPreconnected ha isOpen_ball (convex_ball u ρ).isPreconnected
      (fun n x hx => hd n x hx) (fun n x hx => hb n x hx) hu hf0 hu
  have hF : ∀ n, fderiv ℝ (f n) u = F' n u := fun n => (hd n u hu).fderiv
  have hsumF : HasSum (fun n => F' n u) (∑' n, F' n u) :=
    (Summable.of_norm_bounded (g := a) ha (fun n => hb n u hu)).hasSum
  unfold SymplecticBracket.gradient
  rw [hfs.fderiv]
  simp only [hF]
  exact (hsumF.mapL (InnerProductSpace.toDual ℝ H).symm.toLinearIsometry.toContinuousLinearMap).const_smul (2 : ℝ)⁻¹

/-- **Interchange of the real bracket with two summable series:**
`{Σ_n f_n, Σ_m g_m}(u) = Σ_n Σ_m {f_n, g_m}(u)`, for derivatives summable on a ball around `u`. -/
theorem pbR_tsum_tsum (f g : ℕ → H → ℝ) (F' G' : ℕ → H → (H →L[ℝ] ℝ)) (a b : ℕ → ℝ) (u : H)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hfd : ∀ n, ∀ x ∈ ball u ρ, HasFDerivAt (f n) (F' n x) x)
    (hgd : ∀ m, ∀ x ∈ ball u ρ, HasFDerivAt (g m) (G' m x) x)
    (hfb : ∀ n, ∀ x ∈ ball u ρ, ‖F' n x‖ ≤ a n) (hgb : ∀ m, ∀ x ∈ ball u ρ, ‖G' m x‖ ≤ b m)
    (ha : Summable a) (hb : Summable b) (hf0 : Summable fun n => f n u)
    (hg0 : Summable fun m => g m u) :
    pbR (fun y => ∑' n, f n y) (fun y => ∑' m, g m y) u =
      ∑' n, ∑' m, pbR (f n) (g m) u := by
  have hA := hasSum_gradient_tsum f F' a u ρ hρ hfd hfb ha hf0
  have hB := hasSum_gradient_tsum g G' b u ρ hρ hgd hgb hb hg0
  rw [pbR_eq_omega]
  unfold SymplecticBracket.omega
  have h1 := hasSum_inner_left' _ _ hA (SymplecticBracket.gradient (fun y => ∑' m, g m y) u)
  have h2 := (Complex.imCLM.hasSum h1).mul_left 2
  simp only [Complex.imCLM_apply] at h2
  have h3 : ∀ n, 2 * (⟪SymplecticBracket.gradient (f n) u, SymplecticBracket.gradient (fun y => ∑' m, g m y) u⟫_ℂ).im =
      ∑' m, pbR (f n) (g m) u := by
    intro n
    have hm := hasSum_inner_right' (SymplecticBracket.gradient (f n) u) _ _ hB
    have hm2 := (Complex.imCLM.hasSum hm).mul_left 2
    simp only [Complex.imCLM_apply] at hm2
    rw [hm2.tsum_eq.symm]
    simp only [pbR_eq_omega, SymplecticBracket.omega]
  rw [← h2.tsum_eq]
  exact tsum_congr h3

end QuantumNLS.RootPoissonSeries

#print axioms QuantumNLS.RootPoissonSeries.hasSum_inner_left'
#print axioms QuantumNLS.RootPoissonSeries.hasSum_gradient_tsum
#print axioms QuantumNLS.RootPoissonSeries.pbR_tsum_tsum
