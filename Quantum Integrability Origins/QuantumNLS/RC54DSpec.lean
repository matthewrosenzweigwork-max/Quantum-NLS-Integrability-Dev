import QuantumNLS.OrderComparison

/-! integrator-authored trusted spec for R-C54DBD49 `CC:F01:comparison` (root_response/F01.tex:20-27).
T_i(x) = L x_i + 2 Σ_{j≠i} arctan((x_i − x_j)/c) (CC:F01:smooth), L, c > 0. For any x, y ∈ ℝ^N let
B = ∫₀¹ DT(x + t(y − x)) dt (entrywise: B_ik = ∫₀¹ (DT(x+t(y−x)) e_k)_i dt). Then B is symmetric positive
definite, B⁻¹ has nonnegative entries, every row and column of B⁻¹ sums to 1/L, and T(x) ≤ T(y)
componentwise implies x ≤ y componentwise. -/

open scoped Matrix

namespace QuantumNLS.RC54DSpec

noncomputable def sT {N : ℕ} (L c : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  L * x i + 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan ((x i - x j) / c)

noncomputable def sB {N : ℕ} (L c : ℝ) (x y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i k => ∫ t in (0 : ℝ)..1, fderiv ℝ (sT L c) (x + t • (y - x)) (Pi.single k 1) i

def Spec : Prop :=
  ∀ (N : ℕ) (L c : ℝ), 0 < L → 0 < c → ∀ x y : Fin N → ℝ,
    (sB L c x y)ᵀ = sB L c x y ∧ (sB L c x y).PosDef ∧
    (∀ i k, 0 ≤ (sB L c x y)⁻¹ i k) ∧
    (∀ i, ∑ k, (sB L c x y)⁻¹ i k = 1 / L) ∧
    (∀ k, ∑ i, (sB L c x y)⁻¹ i k = 1 / L) ∧
    ((∀ i, sT L c x i ≤ sT L c y i) → ∀ i, x i ≤ y i)

theorem sB_eq {N : ℕ} (L : ℝ) {c : ℝ} (hc : 0 < c) (x y : Fin N → ℝ) :
    sB L c x y = OrderComparison.avgJac L c x y := by
  ext i k
  rw [OrderComparison.avgJac_entry L hc x y i k]
  rfl

theorem spec : Spec := by
  intro N L c hL hc x y
  rw [sB_eq L hc x y]
  exact OrderComparison.order_comparison hL hc x y

end QuantumNLS.RC54DSpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.RC54DSpec.spec
  IO.println s!"RC54DSpec.spec axioms: {ax}"
