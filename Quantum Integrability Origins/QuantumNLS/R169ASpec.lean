import QuantumNLS.F04Global
import QuantumNLS.R3F6ASpec

/-! integrator-authored trusted spec for R-169AABCC `F04:thm-global` (foundations/F04.tex:277 ff), on the
F04 Fourier-side spaces (R-501CA032 / R-3F6AA186 conventions; IsMild = literal F04:eq-duhamel, pinned in
R501Spec; S1 = continuous series representative, pinned in R3F6ASpec). For κ ≥ 0 and u₀ ∈ H¹:
the maximal solution is global (mild on ℝ), in C(ℝ;H¹) ∩ C¹(ℝ;H^{−1}) and solves the equation in H^{−1};
it is unique among C_tH¹ distributional solutions on ℝ and among mild solutions on any interval; mass and
energy are conserved and ‖u(t)‖²_{H¹} ≤ M(u₀) + E(u₀); the solutions from the truncated data P_N u₀
(Fourier window |n| ≤ N, pinned below) are in C(ℝ;H³) ∩ C¹(ℝ;H¹) and converge to u uniformly on [−T,T] in
H¹, as do those from any H³ data converging to u₀ in H¹; and for ‖u₀‖, ‖v₀‖ ≤ R and |t| ≤ T,
‖u(t) − v(t)‖_{H¹} ≤ exp(4κ C_{1,L} K_R² T) ‖u₀ − v₀‖_{H¹} with K_R² = R² + κ c_L² R⁴ (pinned below). -/

open Filter Topology MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.LocalWellPosedness
open QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity QuantumNLS.F04Global

namespace QuantumNLS.R169ASpec

variable {L : ℝ} [Fact (0 < L)]

theorem spec (κ : ℝ) (hκ : 0 ≤ κ) (u0 : h04 L 1) :
    -- pinning of the truncation and of K_R²
    (∀ (N : ℕ) (a : h04 L 1) (n : ℤ), (PN N a).val n = if |n| ≤ N then a.val n else 0) ∧
    (∀ R : ℝ, KR2 (L := L) κ R = R ^ 2 + κ * cL L ^ 2 * R ^ 4) ∧
    -- the theorem
    (IsMild (le_refl (1 : ℝ)) κ Set.univ u0 (umax (le_refl (1 : ℝ)) κ u0) ∧
    Continuous (umax (le_refl (1 : ℝ)) κ u0) ∧
    ContDiff ℝ 1 (fun t => ι2 1 (umax (le_refl (1 : ℝ)) κ u0 t)) ∧
    (∀ t, HasDerivAt (fun t => ι2 1 (umax (le_refl (1 : ℝ)) κ u0 t))
      (Gder (le_refl (1 : ℝ)) κ (umax (le_refl (1 : ℝ)) κ u0 t)) t) ∧
    (∀ t, Complex.I • Gder (le_refl (1 : ℝ)) κ (umax (le_refl (1 : ℝ)) κ u0 t) =
      lapOp 1 (umax (le_refl (1 : ℝ)) κ u0 t) +
        ((2 * κ : ℝ) : ℂ) • ι2 1 (Fh (le_refl (1 : ℝ)) (umax (le_refl (1 : ℝ)) κ u0 t))) ∧
    (∀ v : ℝ → h04 L 1, IsDistSol κ Set.univ v → v 0 = u0 → ∀ t, v t = umax (le_refl (1 : ℝ)) κ u0 t) ∧
    (∀ (J : Set ℝ) (v : ℝ → h04 L 1), IsMild (le_refl (1 : ℝ)) κ J u0 v →
      ∀ t ∈ J, v t = umax (le_refl (1 : ℝ)) κ u0 t) ∧
    (∀ t, ∫ x, ‖S1 (umax (le_refl (1 : ℝ)) κ u0 t) x‖ ^ 2 = ∫ x, ‖S1 u0 x‖ ^ 2) ∧
    (∀ t, ChargeEnergy.energyH1 κ (S1 (umax (le_refl (1 : ℝ)) κ u0 t)) = ChargeEnergy.energyH1 κ (S1 u0)) ∧
    (∀ t, ‖umax (le_refl (1 : ℝ)) κ u0 t‖ ^ 2 ≤ (∫ x, ‖S1 u0 x‖ ^ 2) + ChargeEnergy.energyH1 κ (S1 u0)) ∧
    (∀ N : ℕ, Continuous (umax hs3 κ (PN N u0)) ∧ ContDiff ℝ 1 (fun t => m31 (umax hs3 κ (PN N u0) t))) ∧
    (∀ T : ℝ, TendstoUniformlyOn (fun N t => m31 (umax hs3 κ (PN N u0) t))
      (umax (le_refl (1 : ℝ)) κ u0) atTop (Set.Icc (-T) T)) ∧
    (∀ w : ℕ → h04 L 3, Tendsto (fun k => m31 (w k)) atTop (𝓝 u0) → ∀ T : ℝ,
      TendstoUniformlyOn (fun k t => m31 (umax hs3 κ (w k) t)) (umax (le_refl (1 : ℝ)) κ u0)
        atTop (Set.Icc (-T) T))) ∧
    (∀ {R T : ℝ} {v0 : h04 L 1}, ‖u0‖ ≤ R → ‖v0‖ ≤ R → ∀ {t : ℝ}, |t| ≤ T →
      ‖umax (le_refl (1 : ℝ)) κ u0 t - umax (le_refl (1 : ℝ)) κ v0 t‖ ≤
        Real.exp (4 * κ * Cs L 1 * KR2 (L := L) κ R * T) * ‖u0 - v0‖) := by
  refine ⟨fun N a n => ?_, fun R => rfl, thm_global hκ u0,
    fun hu hv t ht => lipschitz_bounded hκ hu hv ht⟩
  simp only [PN_val, mem_win]

end QuantumNLS.R169ASpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R169ASpec.spec
  IO.println s!"R169ASpec.spec axioms: {ax}"
