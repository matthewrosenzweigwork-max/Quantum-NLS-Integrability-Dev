import QuantumNLS.LOCAL017HaarBounds
import QuantumNLS.LOCAL017HaarOperators
import QuantumNLS.LOCAL017HaarAngular
import QuantumNLS.ResetMoserCone

/-! LOCAL-017 item 3 consumer receipt.  The function is constructed by the
literal Haar path formula.  The earlier finite-torus periodic primitive and
the original common holomorphic complexification data are explicit stage
inputs; no annihilation, averaged differentiability or derivative bounds are
assumed.  This module does not close either of those earlier source bindings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.LOCAL017Haar
open Ext025B7LocalPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The covector required by ResetMoserAnnihilate, defined at every point,
including zero strata. -/
def beta0 (β : H → Cov) (z : H) : Cov := β z - fderiv ℝ (primitive β) z

theorem beta0_continuousOn {β : H → Cov} {R C : ℝ}
    (D : ComplexData (E := E) β R C) (hR : 0 < R) (hC : 0 ≤ C)
    (hβ : ContinuousOn β (ball 0 R)) : ContinuousOn (beta0 β) (ball 0 R) := by
  have hcd : ContDiffOn ℝ 1 (primitive β) (ball 0 R) :=
    (primitive_analytic D hR hC).contDiffOn_of_completeSpace
  exact hβ.sub (hcd.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)

/-- Exact angular differential and exact hann, with regularity derived from
GP-05.  Only the preceding finite-orbit primitive is carried as stage data. -/
theorem angular_and_hann {β : H → Cov} {R C : ℝ}
    (D : ComplexData (E := E) β R C) (hR : 0 < R) (hC : 0 ≤ C)
    (hβ : ContinuousOn β (ball 0 R))
    (hpot : ∀ z ∈ ball (0 : H) R, {n | z n ≠ 0}.Finite → Nonempty (OrbitPotential β z)) :
    (∀ z ∈ ball (0 : H) R, ∀ h ∈ ResetMoser.Tz z,
      fderiv ℝ (primitive β) z h = β z h) ∧
    (∀ z ∈ ball (0 : H) R, ∀ h ∈ ResetMoser.Tz z, beta0 β z h = 0) := by
  have ha := annihilates hβ ((primitive_analytic D hR hC).contDiffOn_of_completeSpace) hpot
  refine ⟨?_, ha⟩
  intro z hz h hh
  have he := ha z hz h hh
  exact (sub_eq_zero.mp he).symm

/-- The full source orders: quartic scalar value, cubic full first derivative,
quadratic full second derivative, and angular annihilation on the same smaller
ball. Constants are explicit; they have no support-size dependence. -/
theorem primitive_with_bounds {β : H → Cov} {R C B : ℝ}
    (D : ComplexData (E := E) β R C) (hR : 0 < R) (hC : 0 ≤ C)
    (hβ : ContinuousOn β (ball 0 R))
    (hb : ∀ z ∈ ball (0 : H) R, ‖β z‖ ≤ B * ‖z‖^3)
    (hpot : ∀ z ∈ ball (0 : H) R, {n | z n ≠ 0}.Finite → Nonempty (OrbitPotential β z)) :
    AnalyticOnNhd ℝ (primitive β) (ball 0 R) ∧
    ContinuousOn (beta0 β) (ball 0 R) ∧
    (∀ z ∈ ball (0 : H) (R/2),
      |primitive β z| ≤ B * Real.pi * ‖z‖^4 ∧
      ‖fderiv ℝ (primitive β) z‖ ≤ 64 * C * Real.pi * ‖z‖^3 ∧
      ‖iteratedFDeriv ℝ 2 (primitive β) z‖ ≤ 576 * C * Real.pi * ‖z‖^2 ∧
      ‖beta0 β z‖ ≤ (B + 64 * C * Real.pi) * ‖z‖^3) ∧
    (∀ z ∈ ball (0 : H) R, ∀ h ∈ ResetMoser.Tz z, beta0 β z h = 0) := by
  refine ⟨primitive_analytic D hR hC, beta0_continuousOn D hR hC hβ, ?_,
    (angular_and_hann D hR hC hβ hpot).2⟩
  intro z hz
  have hzR := (ball_subset_ball (by linarith : R/2 ≤ R)) hz
  have h1 := primitive_first_bound D hR hC hz
  refine ⟨primitive_bound β hb hzR, h1, primitive_second_bound D hR hC hz, ?_⟩
  calc
    ‖beta0 β z‖ ≤ ‖β z‖ + ‖fderiv ℝ (primitive β) z‖ := norm_sub_le _ _
    _ ≤ B * ‖z‖^3 + 64 * C * Real.pi * ‖z‖^3 := add_le_add (hb z hzR) h1
    _ = _ := by ring

/-- Subtracting df retains the source quadratic order of the first
covector differential. The beta differential bound is the preceding radial
stage's original bound, rather than a premise about the corrected covector. -/
theorem beta0_derivative_bound {β : H → Cov} {R C B : ℝ}
    (D : ComplexData (E := E) β R C) (hR : 0 < R) (hC : 0 ≤ C)
    (hdβ : ∀ z ∈ ball (0 : H) R, DifferentiableAt ℝ β z)
    (hb : ∀ z ∈ ball (0 : H) R, ‖fderiv ℝ β z‖ ≤ B * ‖z‖^2)
    {z : H} (hz : z ∈ ball 0 (R/2)) :
    DifferentiableAt ℝ (beta0 β) z ∧
    ‖fderiv ℝ (beta0 β) z‖ ≤ (B + 576 * C * Real.pi) * ‖z‖^2 := by
  have hzR := (ball_subset_ball (by linarith : R/2 ≤ R)) hz
  have hf : ContDiffAt ℝ 2 (primitive β) z :=
    (primitive_analytic D hR hC z hzR).contDiffAt
  have hdf : DifferentiableAt ℝ (fderiv ℝ (primitive β)) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hh := (hdβ z hzR).sub hdf
  refine ⟨hh, ?_⟩
  change ‖fderiv ℝ (β - fderiv ℝ (primitive β)) z‖ ≤ _
  rw [fderiv_sub (hdβ z hzR) hdf]
  have he : ‖fderiv ℝ (fderiv ℝ (primitive β)) z‖ =
      ‖iteratedFDeriv ℝ 2 (primitive β) z‖ := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ (primitive β)), norm_iteratedFDeriv_fderiv]
  calc
    _ ≤ ‖fderiv ℝ β z‖ + ‖fderiv ℝ (fderiv ℝ (primitive β)) z‖ := norm_sub_le _ _
    _ ≤ B * ‖z‖^2 + 576 * C * Real.pi * ‖z‖^2 := by
      rw [he]
      exact add_le_add (hb z hzR) (primitive_second_bound D hR hC hz)
    _ = _ := by ring

/-- The two radial beta definitions agree literally with the native
ResetMoser source. -/
theorem source_beta_native (S : ResetMoser.Hyp) :
    Ext025B10LocalBeta.sourceBeta S.Ω ResetMoser.omegaF = ResetMoser.betaR S := rfl

/-- Native S/Loc consumer theorem for review record's hann slot. -/
theorem reset_moser_hann (S : ResetMoser.Hyp) {ρ M C : ℝ} (hL : ResetMoser.Loc S ρ M)
    (D : ComplexData (E := E) (ResetMoser.betaR S) ρ C) (hC : 0 ≤ C)
    (hpot : ∀ z ∈ ball (0 : H) ρ, {n | z n ≠ 0}.Finite →
      Nonempty (OrbitPotential (ResetMoser.betaR S) z)) :
    ContinuousOn (beta0 (ResetMoser.betaR S)) (ball 0 ρ) ∧
    (∀ z ∈ ball (0 : H) ρ, ∀ h ∈ ResetMoser.Tz z,
      (ResetMoser.betaR S z - fderiv ℝ (primitive (ResetMoser.betaR S)) z) h = 0) := by
  have hc : ContinuousOn (ResetMoser.betaR S) (ball (0 : H) ρ) := fun z hz =>
    (ResetMoser.betaR_hasFDerivAt S hL hz).continuousAt.continuousWithinAt
  exact ⟨beta0_continuousOn D hL.ρpos hC hc, (angular_and_hann D hL.ρpos hC hc hpot).2⟩

end QuantumNLS.LOCAL017Haar
