import QuantumNLS.TerraMultiRound64REG004

/-! REG-014 support: uniform identification of small Fourier-ball fixed points of the
physical Riccati map with the independently constructed ratio solution.  The accepted
identification (REG-005) has a threshold depending on the field; here the Lipschitz
estimate of the ratio map is used on a ball that is large compared with the size of
both competitors, and the threshold depends only on an upper bound for the norm. -/
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter
open scoped ENNReal
namespace QuantumNLS.Reg014Identify
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.RootH1RatioOperator QuantumNLS.RootH1RatioNonlinear
open QuantumNLS.RootH1RatioContraction QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound43FixedBridge QuantumNLS.TerraMultiRound40ParityEventually
open QuantumNLS.RiccatiPointwiseRep

/-- A bounded representative of a Fourier-ball field. -/
theorem exists_linfty_rep (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ} (ha : 1 / 2 < a) {D : ℝ}
    (hD : 0 < D) (hbound : ∀ (x : Ell2) (t : ℝ), ‖RiccatiPointwiseDisc.physRep L a x t‖ ≤ D * ‖x‖)
    (r : Ell2) :
    ∃ s : Linfty L, s =ᵐ[volume] fieldMap L a (by linarith : (0 : ℝ) ≤ a) r ∧ ‖s‖ ≤ D * ‖r‖ := by
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
  exact hs

theorem aux_contraction (κ D U σ : ℝ) (hκ : 0 < κ) (hD : 0 < D) (_hU : 0 ≤ U) (hσ : 1 ≤ σ)
    (h1 : 8 * κ * U ^ 2 ≤ σ ^ 2) (h2 : 8 * κ * D * U ^ 2 ≤ σ ^ 2) :
    κ * (2 * D * U / σ ^ 2 + 2 * U / σ) * U / σ ≤ 1 / 2 := by
  have hσ0 : 0 < σ := by linarith
  have hσ2 : σ ^ 2 ≤ σ ^ 3 := by nlinarith [sq_nonneg σ]
  have e : κ * (2 * D * U / σ ^ 2 + 2 * U / σ) * U / σ =
      (2 * κ * D * U ^ 2) / σ ^ 3 + (2 * κ * U ^ 2) / σ ^ 2 := by
    field_simp
  rw [e]
  have a : (2 * κ * D * U ^ 2) / σ ^ 3 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have b : (2 * κ * U ^ 2) / σ ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Uniform identification of every small Fourier-ball fixed point with the ratio solution. -/
theorem uniform_identification (L : ℝ) [hLf : Fact (0 < L)] {a : ℝ} (ha : 1 / 2 < a)
    (κ : ℝ) (hκ : 0 < κ) (U : ℝ) (hU : 0 ≤ U) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ x r : Ell2, ‖x‖ ≤ U → ‖r‖ ≤ 2 * ‖x‖ / Y →
      ∀ (hY : 0 < Y), physicalT hLf.out ha (abs_pos.mpr hY.ne') κ x r = r →
      ∃ (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖fieldMap L a (by linarith : (0 : ℝ) ≤ a) x‖ ^ 2 ≤ Y),
        fieldMap L a (by linarith : (0 : ℝ) ≤ a) r =
          ratioL2 hY hlog hκ.le (fieldMap L a (by linarith : (0 : ℝ) ≤ a) x) hsmall := by
  obtain ⟨D, hD, hbound⟩ := representative_bound hLf.out ha
  have hL : 0 < L := hLf.out
  refine ⟨max (max 1 (Real.log 3 / L)) (max (16 * κ * U ^ 2) (8 * κ * D * U ^ 2)),
    (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro Y hYB x r hx hrn hY hr
  have hY1 : 1 ≤ Y := ((le_max_left _ _).trans (le_max_left _ _)).trans hYB
  have hlog : Real.log 3 ≤ Y * L := by
    have h := ((le_max_right 1 (Real.log 3 / L)).trans (le_max_left _ _)).trans hYB
    have h' := (div_le_iff₀ hL).mp h
    simpa [mul_comm] using h'
  have hYU : 16 * κ * U ^ 2 ≤ Y := ((le_max_left _ _).trans (le_max_right _ _)).trans hYB
  have hYD : 8 * κ * D * U ^ 2 ≤ Y := ((le_max_right _ _).trans (le_max_right _ _)).trans hYB
  let ha0 : (0 : ℝ) ≤ a := by linarith
  let u := fieldMap L a ha0 x
  have hu : ‖u‖ ≤ U := by
    have h := (fieldMap L a ha0).le_opNorm x
    have h1 := norm_fieldMap_le L a ha0
    calc ‖u‖ ≤ ‖fieldMap L a ha0‖ * ‖x‖ := h
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ U := by linarith
  have hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y := by
    have : ‖u‖ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    nlinarith
  refine ⟨hlog, hsmall, ?_⟩
  obtain ⟨s, hs, hsn⟩ := exists_linfty_rep L ha hD hbound r
  have hmap := fieldMap_physicalT L ha hY κ x r s hs
  rw [hr] at hmap
  have hfix : ratioMap hY hlog κ u s = s := by
    apply Lp.ext
    have hae := coe_infinityResolvent hY hlog (forcing κ u s)
    filter_upwards [hae, hs] with z hz hz'
    change infinityResolvent hY hlog (forcing κ u s) z = s z
    rw [hz, ← hmap, ← hz']
  -- compare with the ratio solution
  let r₀ := ratio hY hlog hκ.le u hsmall
  have hr₀ := ratio_spec hY hlog hκ.le u hsmall
  have hσ1 : 1 ≤ Real.sqrt Y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hY1
  have hσsq : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt (by linarith)
  have hYpos : 0 < Y := by linarith
  have hsn' : ‖s‖ ≤ 2 * D * U / Real.sqrt Y ^ 2 := by
    rw [hσsq]
    have hr2 : ‖r‖ ≤ 2 * U / Y := by
      calc ‖r‖ ≤ 2 * ‖x‖ / Y := hrn
        _ ≤ 2 * U / Y := by gcongr
    calc ‖s‖ ≤ D * ‖r‖ := hsn
      _ ≤ D * (2 * U / Y) := mul_le_mul_of_nonneg_left hr2 hD.le
      _ = 2 * D * U / Y := by ring
  have hr₀n : ‖r₀‖ ≤ 2 * U / Real.sqrt Y := by
    have h := hr₀.1
    unfold radius scale at h
    calc ‖r₀‖ ≤ 2 * (‖u‖ / Real.sqrt Y) := h
      _ ≤ 2 * (U / Real.sqrt Y) := by gcongr
      _ = 2 * U / Real.sqrt Y := by ring
  have hc : κ * (‖s‖ + ‖r₀‖) * ‖u‖ / Real.sqrt Y ≤ 1 / 2 := by
    have hσpos : 0 < Real.sqrt Y := by linarith
    calc κ * (‖s‖ + ‖r₀‖) * ‖u‖ / Real.sqrt Y
        ≤ κ * (2 * D * U / Real.sqrt Y ^ 2 + 2 * U / Real.sqrt Y) * U / Real.sqrt Y := by
          gcongr
      _ ≤ 1 / 2 := aux_contraction κ D U (Real.sqrt Y) hκ hD hU hσ1
          (by rw [hσsq]; nlinarith) (by rw [hσsq]; nlinarith)
  have hdiff := ratioMap_sub_norm hY hlog hκ.le u s r₀
  rw [hfix, hr₀.2] at hdiff
  have hzero : ‖s - r₀‖ = 0 := by
    have h2 : ‖s - r₀‖ ≤ (1 / 2) * ‖s - r₀‖ :=
      hdiff.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    linarith [norm_nonneg (s - r₀)]
  have hsr : s = r₀ := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  rw [hmap, hsr]
  rfl

#print axioms exists_linfty_rep
#print axioms uniform_identification
end QuantumNLS.Reg014Identify
