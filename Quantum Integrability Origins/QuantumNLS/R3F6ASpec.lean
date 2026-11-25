import QuantumNLS.F04Regularity
import QuantumNLS.R501Spec

/-! integrator-authored trusted spec for R-3F6AA186 `F04:lem-regular` (foundations/F04.tex:224 ff), on the
F04 Fourier-side spaces h^s (R-501CA032 conventions; `IsMild` = literal F04:eq-duhamel, pinned in R501Spec).
For κ ≥ 0 and u₀ ∈ H³, the maximal solution u is mild on all of ℝ (global), unique among mild solutions on
any interval, u ∈ C(ℝ;H³) ∩ C¹(ℝ;H¹) (H³ ↪ H¹ the identity on coefficients), mass M = ∫|u|² (of the
continuous series representative) and energy E = ∫|∂u|² + κ∫|u|⁴ (accepted ChargeEnergy.energyH1) are
constant in t, ‖u(t)‖_{H¹} ≤ K with K² = M(u₀) + E(u₀), and ‖u(t)‖_{H³} ≤ ‖u₀‖_{H³} e^{2κC_{3,L}K²|t|}. -/

open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull
open QuantumNLS.F04Regularity

namespace QuantumNLS.R3F6ASpec

variable {L : ℝ} [Fact (0 < L)]

theorem spec (κ : ℝ) (hκ : 0 ≤ κ) (u0 : h04 L 3) :
    -- pinning: the H³ → H¹ map is the identity on coefficients, S1 is the continuous series representative
    (∀ (a : h04 L 3) (n : ℤ), (m31 a).val n = a.val n) ∧
    (∀ (a : h04 L 1) (x : AddCircle L), S1 a x = seriesRep L a.val x) ∧
    -- global existence, uniqueness, regularity
    IsMild hs3 κ Set.univ u0 (umax hs3 κ u0) ∧
    (∀ (J : Set ℝ) (v : ℝ → h04 L 3), IsMild hs3 κ J u0 v → ∀ t ∈ J, v t = umax hs3 κ u0 t) ∧
    Continuous (umax hs3 κ u0) ∧
    ContDiff ℝ 1 (fun t => m31 (umax hs3 κ u0 t)) ∧
    -- conservation and bounds
    (∀ t, ∫ x, ‖S1 (m31 (umax hs3 κ u0 t)) x‖ ^ 2 = ∫ x, ‖S1 (m31 u0) x‖ ^ 2) ∧
    (∀ t, ChargeEnergy.energyH1 κ (S1 (m31 (umax hs3 κ u0 t))) = ChargeEnergy.energyH1 κ (S1 (m31 u0))) ∧
    (∀ t, ‖m31 (umax hs3 κ u0 t)‖ ≤
      Real.sqrt ((∫ x, ‖S1 (m31 u0) x‖ ^ 2) + ChargeEnergy.energyH1 κ (S1 (m31 u0)))) ∧
    (∀ t, ‖umax hs3 κ u0 t‖ ≤ ‖u0‖ * Real.exp (2 * κ * Cs L 3 *
      ((∫ x, ‖S1 (m31 u0) x‖ ^ 2) + ChargeEnergy.energyH1 κ (S1 (m31 u0))) * |t|)) := by
  obtain ⟨h1, h2, h3, h4, -, h6, h7, h8, h9, h10⟩ := lem_regular hκ u0
  rw [h8] at h9 h10
  exact ⟨fun a n => rfl, fun a x => rfl, h1, h2, h3, h4, h6, h7, h9, h10⟩

end QuantumNLS.R3F6ASpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R3F6ASpec.spec
  IO.println s!"R3F6ASpec.spec axioms: {ax}"
