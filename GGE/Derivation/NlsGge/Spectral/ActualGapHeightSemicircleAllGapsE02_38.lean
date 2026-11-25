import NlsGge.Spectral.ActualGapHeightSemicircleE02_38
import NlsGge.Spectral.ActualQuasimomentumGapConstantE02_38
import NlsGge.Spectral.ActualQuasimomentumEndpointSqrtGeneralE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # NEW-E01 for EVERY gap interval (campaign 38), without labels, Box or Window

Hypotheses as given: any real interval `(a,b)` on which `|Δh| > 1` and with `|Δh| = 1` at
both endpoints (this includes every bounded component of `{|Δh| > 1}`). Closed gaps are the
degenerate case `a = b`, where both sides vanish. The link to the labelled `g_n` is separate. -/

theorem actualGapHeight_ge_semicircle_interval_E02_38 (u : PhysicalL2) (a b : ℝ) (hab : a < b)
    (hgap : ∀ x ∈ Set.Ioo a b, 1 < ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖)
    (ha : ‖actualPhysicalUnitHalfTrace32 u (a:ℂ)‖ = 1)
    (hb : ‖actualPhysicalUnitHalfTrace32 u (b:ℂ)‖ = 1) :
    ∀ x ∈ Set.Icc a b, gapSemicircle a b x ≤ actualGapHeightE02_38 u x := by
  obtain ⟨m, hlim, hDa, hDb⟩ := exists_int_boundary_on_gap_E02_38 u a b hab hgap ha hb
  have hv0 : ∀ y : ℝ, ‖actualPhysicalUnitHalfTrace32 u (y:ℂ)‖ = 1 →
      actualGapHeightE02_38 u y = 0 := fun y hy =>
    (actualGapHeightE02_38_eq_zero_iff u y).mpr hy.le
  have hend : ∀ y ∈ ({a, b} : Set ℝ),
      Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (y:ℂ))
        (𝓝 ((m:ℂ)*Real.pi)) := by
    intro y hy
    rcases hy with rfl | rfl
    · have h := hlim y ⟨le_rfl, hab.le⟩
      rwa [hv0 y ha, Complex.ofReal_zero, mul_zero, add_zero] at h
    · have h := hlim y ⟨hab.le, le_rfl⟩
      rwa [hv0 y hb, Complex.ofReal_zero, mul_zero, add_zero] at h
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; simp [gapSemicircle, actualGapHeightE02_38_nonneg]
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h']; simp [gapSemicircle, actualGapHeightE02_38_nonneg]
  apply gapHeight_ge_semicircle_generic_E02_38 u m a b x ⟨h, h'⟩
  · intro y hy L hL
    have h1 := hlim y ⟨hy.1.le, hy.2.le⟩
    have : (𝓝[{z : ℂ | 0 < z.im}] (y:ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_upperHalfPlane_E02_38 (by simp))
    rw [tendsto_nhds_unique hL h1]; ring
  · exact actualQuasimomentum_sub_sq_le_of_tendsto_E02_38 u m a hDa (hend a (by simp))
  · exact actualQuasimomentum_sub_sq_le_of_tendsto_E02_38 u m b hDb (hend b (by simp))
  · exact hgap x ⟨h, h'⟩

/-- Exact action lower bound on every gap interval: `(b-a)²/4 ≤ (2/π)∫_a^b v`. -/
theorem actualGapAction_ge_sq_div_four_interval_E02_38 (u : PhysicalL2) (a b : ℝ) (hab : a < b)
    (hgap : ∀ x ∈ Set.Ioo a b, 1 < ‖actualPhysicalUnitHalfTrace32 u (x:ℂ)‖)
    (ha : ‖actualPhysicalUnitHalfTrace32 u (a:ℂ)‖ = 1)
    (hb : ‖actualPhysicalUnitHalfTrace32 u (b:ℂ)‖ = 1) :
    (b - a)^2/4 ≤ (2/Real.pi) * ∫ x in a..b, actualGapHeightE02_38 u x := by
  have hsc : Continuous (gapSemicircle a b) := by unfold gapSemicircle; fun_prop
  have hint : ∫ x in a..b, gapSemicircle a b x ≤ ∫ x in a..b, actualGapHeightE02_38 u x :=
    intervalIntegral.integral_mono_on hab.le (hsc.intervalIntegrable a b)
      (intervalIntegrable_actualGapHeightE02_38 u a b)
      (actualGapHeight_ge_semicircle_interval_E02_38 u a b hab hgap ha hb)
  rw [integral_gapSemicircle a b hab.le] at hint
  have hpi := Real.pi_pos
  calc (b - a)^2/4 = (2/Real.pi) * ((Real.pi/8) * (b-a)^2) := by field_simp; ring
    _ ≤ (2/Real.pi) * ∫ x in a..b, actualGapHeightE02_38 u x :=
      mul_le_mul_of_nonneg_left hint (by positivity)

end NlsGge.SpectralFoundations
end
