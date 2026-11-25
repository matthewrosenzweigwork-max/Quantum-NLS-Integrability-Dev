import QuantumNLS.TerraMultiRound41CauchyEventually
import QuantumNLS.RootH1RatioCauchy

/-! Scalar-level comparison to the actual L∞ ratio for a nonzero physical
field. Equality of the solutions themselves is not asserted. -/
set_option autoImplicit false
noncomputable section
open Complex
open scoped InnerProductSpace
namespace QuantumNLS.TerraMultiRound41ScalarAgreement
open QuantumNLS.PhysicalTensor QuantumNLS.FullMass QuantumNLS.CauchyUniqueness
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound41CauchyEventually QuantumNLS.RootH1RatioBounds

/-- The signed branch and the already constructed L∞ branch have the same
scalar integral at all sufficiently large positive heights for a nonzero field. -/
theorem scalar_agreement_eventually (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (κ : ℝ) (hκ : 0 < κ) (u : Ell2)
    (hu : fieldMap L a (by linarith : (0 : ℝ) ≤ a) u ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, C ≤ Y →
      ∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) u‖ ^ 2 ≤ Y)
        (r : Ell2),
        ‖r‖ ≤ 2 * ‖u‖ / Y ∧
        physicalT hLf.out ha (abs_pos.mpr hY.ne') κ u r = r ∧
        scalar L a u r = inner ℂ (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u)
          (ratioL2 hY hlog hκ.le _ hsmall) := by
  let U := fieldMap L a (by linarith : (0 : ℝ) ≤ a) u
  obtain ⟨C₀, hC₀, hc⟩ := positive_scalar_cauchy_eventually L ha κ hκ u
  refine ⟨max C₀ (max (16 * κ * ‖U‖ ^ 2) (Real.log 3 / L)),
    lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro Y hY
  have hC : C₀ ≤ Y := (le_max_left _ _).trans hY
  obtain ⟨hYpos, r, hrn, hr, hscalar⟩ := hc Y hC
  have hsmall : 16 * κ * ‖U‖ ^ 2 ≤ Y :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hlog : Real.log 3 ≤ Y * L := by
    have h := (le_max_right (16 * κ * ‖U‖ ^ 2) (Real.log 3 / L)).trans
      ((le_max_right _ _).trans hY)
    have h' := (div_le_iff₀ hLf.out).mp h
    simpa [mul_comm] using h'
  have hratio := QuantumNLS.RootH1RatioCauchy.ratio_cauchy hYpos hlog hκ U hu hsmall
  refine ⟨hYpos, hlog, hsmall, r, hrn, hr, ?_⟩
  apply mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero)
  exact hscalar.symm.trans hratio

#print axioms scalar_agreement_eventually
end QuantumNLS.TerraMultiRound41ScalarAgreement
