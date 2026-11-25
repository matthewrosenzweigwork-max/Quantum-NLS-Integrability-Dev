import NlsGge.Birkhoff.W12Tilt38b

/-! # W12 (`D:prop:tilt`), part 3 (Birkhoff-free): `E_B`, the exact relation between the remainders

`E_B(u) = (2/π) ∫ B(2λ) v(λ;u) dλ ∈ [0,∞]` (`EB38`, the spectral energy of the weight `B`, whose
coefficient numerators are `bCoef38 c`).

W12.05 (v2 l.1859, "`R_W̃ = R_W - δ(E_B - ∑ b_n I_n)`"), as a statement about an arbitrary field
`u` whose three series converge: `remainder_tilt_identity38`.  No Birkhoff map is involved here;
the Birkhoff substitution `u = Φ⁻¹ z` is made in `W12Tilt38d`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.SpectralFoundations Filter Topology
open scoped ENNReal Real

section SpectralGeneral

/-- The spectral energy `E_B(u) = (2/π)∫ B(2λ) v(λ;u) dλ` of the reserved weight `B`
(`B(r) = weight (bCoef38 c) r = ∑_j β_{j+1} r^{2j}`), in `[0,∞]`. -/
def EB38 (c : ℕ → ℝ) (u : PhysicalL2) : ℝ≥0∞ := spectralEnergyW38 (bCoef38 c) u

theorem gapIntegral38_nonneg_general (c : ℕ → ℝ) (hnn : ∀ r, 0 ≤ weight c r) (u : PhysicalL2)
    (n : ℤ) : 0 ≤ gapIntegral38 c u n := by
  unfold gapIntegral38
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg
    (actualGapLower_le_upper38' u n) (fun x _ => ?_))
  exact mul_nonneg (hnn _) (actualGapHeightE02_38_nonneg u x)

/-- The gap decomposition of the spectral energy for a general continuous nonnegative weight. -/
theorem spectralEnergy_eq_tsum_general38 (c : ℕ → ℝ) (hW : Continuous (weight c))
    (hnn : ∀ r, 0 ≤ weight c r) (u : PhysicalL2) :
    spectralEnergyW38 c u = ∑' n : ℤ, ENNReal.ofReal (gapIntegral38 c u n) := by
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  set f : ℝ → ℝ := fun l => weight c (2 * l) * actualGapHeightE02_38 u l with hf
  have hfc : Continuous f := (hW.comp (continuous_const.mul continuous_id)).mul hv
  have hf0 : ∀ l, 0 ≤ f l := fun l =>
    mul_nonneg (hnn _) (actualGapHeightE02_38_nonneg u l)
  set G : ℤ → Set ℝ := fun n => Set.Ioo (actualGapLowerAllE02_38 u n)
    (actualGapUpperAllE02_38 u n) with hG
  have hlev : ∀ n : ℤ, ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
    intro n x hx
    have := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    rw [← this] at hx
    exact hx
  have hdisj : Pairwise (Function.onFun Disjoint G) := by
    intro n m hnm
    refine Set.disjoint_left.2 (fun l hn hm => hnm ?_)
    have h1 := hlev n l ⟨hn.1.le, hn.2.le⟩
    have h2 := hlev m l ⟨hm.1.le, hm.2.le⟩
    have : (n : ℝ) = m := mul_right_cancel₀ Real.pi_ne_zero (h1.symm.trans h2)
    exact_mod_cast this
  have hsupp : (fun l => ENNReal.ofReal (f l)).support ⊆ ⋃ n, G n := by
    intro l hl
    have hne : f l ≠ 0 := by
      intro h0; apply hl; simp [h0]
    have hv0 : actualGapHeightE02_38 u l ≠ 0 := fun h0 => hne (by simp [hf, h0])
    obtain ⟨n, hn⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u l hv0
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  have h1 : ∫⁻ l, ENNReal.ofReal (f l) = ∑' n, ∫⁻ l in G n, ENNReal.ofReal (f l) := by
    rw [← setLIntegral_eq_of_support_subset hsupp,
      lintegral_iUnion (fun n => measurableSet_Ioo) hdisj]
  have h2 : ∀ n, ENNReal.ofReal (2 / Real.pi) * ∫⁻ l in G n, ENNReal.ofReal (f l) =
      ENNReal.ofReal (gapIntegral38 c u n) := by
    intro n
    have hab := actualGapLower_le_upper38' u n
    have hint : Integrable f (volume.restrict (G n)) :=
      (hfc.continuousOn.integrableOn_Icc (a := actualGapLowerAllE02_38 u n)
        (b := actualGapUpperAllE02_38 u n)).mono_set Set.Ioo_subset_Icc_self
    have h3 : ∫⁻ l in G n, ENNReal.ofReal (f l) = ENNReal.ofReal (∫ l in G n, f l) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)).symm
    have h4 : ∫ l in G n, f l = ∫ l in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        f l := by
      rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    rw [h3, h4, ← ENNReal.ofReal_mul (by positivity)]
    rfl
  unfold spectralEnergyW38
  show ENNReal.ofReal (2 / Real.pi) * ∫⁻ l, ENNReal.ofReal (f l) = _
  rw [h1, ← ENNReal.tsum_mul_left]
  exact tsum_congr h2

variable {lower upper : ℝ}

theorem EB38_eq_tsum (c : BoundedCoefficients lower upper) (u : PhysicalL2) :
    EB38 c.val u = ∑' n : ℤ, ENNReal.ofReal (gapIntegral38 (bCoef38 c.val) u n) :=
  spectralEnergy_eq_tsum_general38 _ (continuous_weight_bCoef38 c) (weight_bCoef_nonneg38 c) u

theorem gapIntegral38_bCoef_nonneg (c : BoundedCoefficients lower upper) (u : PhysicalL2) (n : ℤ) :
    0 ≤ gapIntegral38 (bCoef38 c.val) u n :=
  gapIntegral38_nonneg_general _ (weight_bCoef_nonneg38 c) u n

end SpectralGeneral

section Relation

variable {lower upper : ℝ}

/-- `(2/π)∫_{g_n} W̃(2λ) v = (2/π)∫_{g_n} W(2λ) v - δ (2/π)∫_{g_n} B(2λ) v`. -/
theorem gapIntegral38_tilt (c : BoundedCoefficients lower upper) {δ : ℝ} (_hδ0 : 0 < δ)
    (_hδ : δ * upper < lower) (u : PhysicalL2) (n : ℤ) :
    gapIntegral38 (tiltCoef38 c.val δ) u n =
      gapIntegral38 c.val u n - δ * gapIntegral38 (bCoef38 c.val) u n := by
  have hW := weight_continuous38 (coef_lower38 c) (coef_bound38 c) (coef_upper38 c)
  have hB := continuous_weight_bCoef38 c
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hi1 : IntervalIntegrable (fun x => weight c.val (2 * x) * actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    ((hW.comp (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => weight (bCoef38 c.val) (2 * x) *
      actualGapHeightE02_38 u x) volume
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    ((hB.comp (continuous_const.mul continuous_id)).mul hv).intervalIntegrable _ _
  unfold gapIntegral38
  have e : ∀ x, weight (tiltCoef38 c.val δ) (2 * x) * actualGapHeightE02_38 u x =
      weight c.val (2 * x) * actualGapHeightE02_38 u x -
        δ * (weight (bCoef38 c.val) (2 * x) * actualGapHeightE02_38 u x) := fun x => by
    rw [weight_tiltCoef38]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_sub hi1 (hi2.const_mul δ), intervalIntegral.integral_const_mul]
  ring

theorem remainderSummand38_tilt (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (u : PhysicalL2) (n : ℤ) :
    remainderSummand38 (tiltCoef38 c.val δ) u n =
      remainderSummand38 c.val u n - δ * (gapIntegral38 (bCoef38 c.val) u n -
        bRate38 c.val n * actualGapActionAllE02_38 u n) := by
  unfold remainderSummand38
  rw [gapIntegral38_tilt c hδ0 hδ, fullWeightRate_tilt38]
  ring

/-- **W12.05 (v2 l.1859): `R_W̃ = R_W - δ (E_B - ∑ b_n I_n)`.** For a field `u` for which the
remainder series of `W` and `W̃ = W - δ B` and the action series `∑ b_n I_n(u)` converge,
`E_B(u) < ∞` and the identity holds (Lean's `toReal` of the finite extended energy). -/
theorem remainder_tilt_identity38 (c : BoundedCoefficients lower upper) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ * upper < lower) (u : PhysicalL2)
    (h1 : Summable (fun n : ℤ => remainderSummand38 c.val u n))
    (h2 : Summable (fun n : ℤ => remainderSummand38 (tiltCoef38 c.val δ) u n))
    (h3 : Summable (fun n : ℤ => bRate38 c.val n * actualGapActionAllE02_38 u n)) :
    EB38 c.val u ≠ ⊤ ∧
    remainder38 (tiltCoef38 c.val δ) u = remainder38 c.val u -
      δ * ((EB38 c.val u).toReal - ∑' n : ℤ, bRate38 c.val n * actualGapActionAllE02_38 u n) := by
  set gB : ℤ → ℝ := fun n => gapIntegral38 (bCoef38 c.val) u n with hgB
  set bI : ℤ → ℝ := fun n => bRate38 c.val n * actualGapActionAllE02_38 u n with hbI
  have hg0 : ∀ n, 0 ≤ gB n := gapIntegral38_bCoef_nonneg c u
  set d : ℤ → ℝ := fun n => gB n - bI n with hd
  have hdd : ∀ n, d n = (remainderSummand38 c.val u n -
      remainderSummand38 (tiltCoef38 c.val δ) u n) / δ := by
    intro n
    rw [remainderSummand38_tilt c hδ0 hδ]
    simp only [hd, hgB, hbI]
    field_simp
    ring
  have hds : Summable d := by
    have := (h1.sub h2).div_const δ
    exact this.congr (fun n => (hdd n).symm)
  have hgs : Summable gB := by
    have := hds.add h3
    exact this.congr (fun n => by simp only [hd, hbI]; ring)
  have hE : EB38 c.val u = ∑' n, ENNReal.ofReal (gB n) := EB38_eq_tsum c u
  have hEfin : EB38 c.val u ≠ ⊤ := by
    rw [hE, ← ENNReal.ofReal_tsum_of_nonneg hg0 hgs]; exact ENNReal.ofReal_ne_top
  refine ⟨hEfin, ?_⟩
  have hEr : (EB38 c.val u).toReal = ∑' n, gB n := by
    rw [hE, ← ENNReal.ofReal_tsum_of_nonneg hg0 hgs, ENNReal.toReal_ofReal (tsum_nonneg hg0)]
  rw [hEr]
  have hsplit : ∑' n, gB n - ∑' n, bI n = ∑' n, d n := by
    rw [← hgs.tsum_sub h3]
  rw [hsplit]
  unfold remainder38
  have : ∀ n, remainderSummand38 (tiltCoef38 c.val δ) u n =
      remainderSummand38 c.val u n - δ * d n := fun n => by
    rw [remainderSummand38_tilt c hδ0 hδ]
  simp_rw [this]
  rw [h1.tsum_sub (hds.mul_left δ), tsum_mul_left]

end Relation

end NlsGge.Birkhoff
end
