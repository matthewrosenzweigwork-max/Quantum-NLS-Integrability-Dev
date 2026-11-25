import QuantumNLS.Local021RHeadline
/-! integrator-authored trusted spec for LOCAL-021 prop:reset-moser-covariance (terra_review r215 ACCEPT after r212 HOLD): headline statement(s) copied verbatim from Local021RHeadline (QuantumNLS.Local021Repair). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory BoundedContinuousFunction
namespace QuantumNLS.L021Spec
open QuantumNLS.Local021Repair
open QuantumNLS.D01LocalPrimitive QuantumNLS.ResetMoser
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local021
open QuantumNLS.Local021R
variable {L r : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem reset_moser_covariance_full_spec {L r : ℝ} [Fact (0 < L)] (hr : 0 < r) (hr2 : r < 2 * Real.pi / L)
    (hdiff : FullDiffeoPremise L r) :
    -- (0) the preceding exact-modulus family exists at every coupling (LOCAL-020)
    (∀ (κ : ℝ) (hκ : 0 < κ), ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
        ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)), Fam020 L κ r ρ C hκ a b rr) ∧
    -- (1) at every coupling and on every such family: a (constructed) setting with the printed conclusions
    (∀ (κ : ℝ) (hκ : 0 < κ) (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        0 < ρ → 0 ≤ C → Fam020 L κ r ρ C hκ a b rr →
        ∃ S : Setting L κ r hκ, S.ρ = ρ ∧ S.C = C ∧ S.a = a ∧ S.b = b ∧ S.rr = rr ∧ SettingProps S) ∧
    -- (2) scaling between the (constructed) settings at couplings `κ` and `κ s²`
    (∀ (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2)
        (ρA CA : ℝ) (aA : ℤ → L2T L → ℝ) (bA : ℤ → L2T L → ℂ) (rrA : L2T L → (ℤ →ᵇ ℝ))
        (ρB CB : ℝ) (aB : ℤ → L2T L → ℝ) (bB : ℤ → L2T L → ℂ) (rrB : L2T L → (ℤ →ᵇ ℝ)),
        0 < ρA → 0 ≤ CA → 0 < ρB → 0 ≤ CB → Fam020 L κ r ρA CA hκ aA bA rrA →
        Fam020 L (κ * s ^ 2) r ρB CB hκ₂ aB bB rrB →
        ∃ (SA : Setting L κ r hκ) (SB : Setting L (κ * s ^ 2) r hκ₂),
          SA.ρ = ρA ∧ SA.C = CA ∧ SA.a = aA ∧ SA.b = bA ∧ SA.rr = rrA ∧
          SB.ρ = ρB ∧ SB.C = CB ∧ SB.a = aB ∧ SB.b = bB ∧ SB.rr = rrB ∧ ScaleProps SA s hs hκ₂ SB) ∧
    -- (3) the constant `C_L`, the fixed unit-coupling chart, domains chosen by scaling, and the full fixed-ball estimate
    (∃ CL : ℝ, 0 ≤ CL ∧
      ∀ (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        0 < ρ → 0 ≤ C → Fam020 L 1 r ρ C one_pos a b rr →
        ∃ S1 : Setting L 1 r one_pos, S1.ρ = ρ ∧ S1.C = C ∧ S1.a = a ∧ S1.b = b ∧ S1.rr = rr ∧ SettingProps S1 ∧
          ∃ rs : ℝ, 0 < rs ∧ rs ≤ S1.rM ∧
            -- the chart at coupling `κ`: `Φ̂_κ(u) = κ^{-1/2} Φ_1(√κ u)` on `{√κ‖u‖ < rs}` agrees with the procedure's `Φ_κ` of every setting at coupling `κ`
            (∀ (κ : ℝ) (hκ : 0 < κ) (ρ' C' : ℝ) (a' : ℤ → L2T L → ℝ) (b' : ℤ → L2T L → ℂ) (rr' : L2T L → (ℤ →ᵇ ℝ)),
              0 < ρ' → 0 ≤ C' → Fam020 L κ r ρ' C' hκ a' b' rr' →
              ∃ S : Setting L κ r hκ, S.ρ = ρ' ∧ S.C = C' ∧ S.a = a' ∧ S.b = b' ∧ S.rr = rr' ∧ SettingProps S ∧
                ∀ u : L2T L, ‖u‖ < S.rM → Real.sqrt κ * ‖u‖ < rs → S.Phi u = PhiHat S1 κ u) ∧
            -- each fixed `L²` ball lies in the scaled domain for small `κ`, and there `‖DΦ̂_κ − 𝓕‖ ≤ C_L κ‖u‖²` (full `C¹` Fourier limit)
            (∀ ρ0 : ℝ, 0 < ρ0 → ∃ κ0 : ℝ, 0 < κ0 ∧ ∀ κ : ℝ, 0 < κ → κ < κ0 → ∀ u : L2T L, ‖u‖ < ρ0 →
              Real.sqrt κ * ‖u‖ < rs ∧ DifferentiableAt ℝ (PhiHat S1 κ) u ∧
              ‖fderiv ℝ (PhiHat S1 κ) u - Setting.Fcl L‖ ≤ CL * κ * ‖u‖ ^ 2 ∧
              ‖PhiHat S1 κ u - Setting.Fcl L u‖ ≤ CL * κ * ‖u‖ ^ 3) ∧
            -- the printed scaling `Φ_κ(su) = sΦ_{κs²}(u)` on the scaled domains
            (∀ κ : ℝ, 0 < κ → ∀ s : ℝ, 0 < s → ∀ u : L2T L, PhiHat S1 κ (s • u) = s • PhiHat S1 (κ * s ^ 2) u)) := by
  exact QuantumNLS.Local021Repair.reset_moser_covariance_full hr hr2 hdiff


/-- integrator pin: the only premise, `FullDiffeoPremise`, unfolds to this literal statement
(the printed "full analytic diffeomorphism between Hilbert balls", at unit coupling). -/
theorem FullDiffeoPremise_literal (L r : ℝ) [Fact (0 < L)] :
    QuantumNLS.Local021R.FullDiffeoPremise L r ↔
    ∀ (ρ C : ℝ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
      0 < ρ → 0 ≤ C → Fam020 L 1 r ρ C one_pos a b rr →
      ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧ ∃ η : K → K,
        AnalyticOnNhd ℝ (zetaT L 1 b rr) (ball (0 : K) R) ∧ AnalyticOnNhd ℝ η (ball (0 : K) R) ∧
        (∀ y ∈ ball (0 : K) R, η y ∈ ball (0 : K) R) ∧
        (∀ y ∈ ball (0 : K) R, zetaT L 1 b rr (η y) = y) ∧ (∀ x ∈ ball (0 : K) R, η (zetaT L 1 b rr x) = x) :=
  Iff.rfl

end QuantumNLS.L021Spec
#print axioms QuantumNLS.L021Spec.reset_moser_covariance_full_spec
#print axioms QuantumNLS.L021Spec.FullDiffeoPremise_literal
