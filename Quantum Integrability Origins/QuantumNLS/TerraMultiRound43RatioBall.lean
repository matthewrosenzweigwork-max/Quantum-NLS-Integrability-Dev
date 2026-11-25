import QuantumNLS.TerraMultiRound40ParityEventually
import QuantumNLS.RootH1RatioContraction

/-! The Fourier small ball lies in the independent L∞ ratio ball at large
positive heights. Equality of the two nonlinear fixed-point maps is separate. -/
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped ENNReal
namespace QuantumNLS.TerraMultiRound43RatioBall
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiPointwiseRep
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound40ParityEventually
open QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioContraction

/-- At nonzero physical field, every Fourier-ball element has an L∞
representative in the independent ratio construction's ball, eventually. -/
theorem fourier_ball_in_ratio_ball (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (u : Ell2)
    (hu : fieldMap L a (by linarith : (0 : ℝ) ≤ a) u ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ Y → ∀ r : Ell2,
      ‖r‖ ≤ 2 * ‖u‖ / Y →
      ∃ s : Linfty L,
        s =ᵐ[volume] fieldMap L a (by linarith : (0 : ℝ) ≤ a) r ∧
        ‖s‖ ≤ radius Y (fieldMap L a (by linarith : (0 : ℝ) ≤ a) u) := by
  let U := fieldMap L a (by linarith : (0 : ℝ) ≤ a) u
  have hU : 0 < ‖U‖ := norm_pos_iff.mpr hu
  obtain ⟨D, hD, hbound⟩ := representative_bound hLf.out ha
  let A := D * ‖u‖ / ‖U‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨max 1 (A ^ 2), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro Y hYB r hr
  have hY : 0 < Y := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hYB)
  have hsY : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hAroot : A ≤ Real.sqrt Y := by
    have h := Real.sqrt_le_sqrt ((le_max_right 1 (A ^ 2)).trans hYB)
    simpa [Real.sqrt_sq hA] using h
  have hprod : D * ‖u‖ ≤ ‖U‖ * Real.sqrt Y := by
    have h := mul_le_mul_of_nonneg_left hAroot hU.le
    dsimp [A] at h
    have he : ‖U‖ * (D * ‖u‖ / ‖U‖) = D * ‖u‖ := by field_simp
    rwa [he] at h
  have hboundR : D * (2 * ‖u‖ / Y) ≤ radius Y U := by
    unfold radius scale
    have hsquare := Real.sq_sqrt hY.le
    calc
      D * (2 * ‖u‖ / Y) = (2 * D * ‖u‖) / Y := by ring
      _ ≤ (2 * ‖U‖) / Real.sqrt Y := by
        apply (div_le_div_iff₀ hY hsY).2
        nlinarith [mul_le_mul_of_nonneg_right hprod hsY.le]
      _ = 2 * (‖U‖ / Real.sqrt Y) := by ring
  obtain ⟨g, hgcont, hgae, hgpoint, _⟩ := fieldMap_rep L ha r
  have hg (z : AddCircle L) : ‖g z‖ ≤ D * ‖r‖ := by
    induction z using QuotientAddGroup.induction_on with
    | H t =>
      rw [hgpoint t]
      exact hbound r t
  have hb : ∀ᵐ z : AddCircle L,
      ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) r z‖ ≤ D * ‖r‖ := by
    filter_upwards [hgae] with z hz
    rw [hz]
    exact hg z
  let hm : MemLp (fieldMap L a (by linarith : (0 : ℝ) ≤ a) r) ∞ volume :=
    MemLp.of_bound (Lp.aestronglyMeasurable
    (fieldMap L a (by linarith : (0 : ℝ) ≤ a) r)) (D * ‖r‖) hb
  let s : Linfty L := hm.toLp _
  refine ⟨s, hm.coeFn_toLp, ?_⟩
  have hs : ‖s‖ ≤ D * ‖r‖ := by
    have h := Lp.norm_le_of_ae_bound (show 0 ≤ D * ‖r‖ by positivity) (by
      filter_upwards [hm.coeFn_toLp, hb] with z hz hz'
      rwa [hz])
    simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, one_mul] using h
  exact hs.trans ((mul_le_mul_of_nonneg_left hr hD.le).trans hboundR)

#print axioms fourier_ball_in_ratio_ball
end QuantumNLS.TerraMultiRound43RatioBall
