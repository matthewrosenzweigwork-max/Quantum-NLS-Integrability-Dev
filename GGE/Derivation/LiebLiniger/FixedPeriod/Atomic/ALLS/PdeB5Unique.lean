import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB5Rebase

/-! # Track B, package 2: short-time uniqueness of `L⁴`-Duhamel solutions

Two continuous `L²` trajectories with the same datum at `0`, `L⁴([0,δ₀] × 𝕋)` spacetime
representatives (slices a.e. on `[0,δ₀]`) and the actual `H⁻¹` Duhamel identity on `[0,δ₀]` agree on
some `[0,ε]`, `ε > 0` (`duhamel_unique_short`). Proof: the difference is the Duhamel output of
`N(U) - N(U')`; by uniqueness and the bounds for every output,
`‖U - U'‖_{L⁴([0,ε]×𝕋)} ≤ K ε^{1/16} 3 (‖U‖² + ‖U'‖²) ‖U - U'‖_{L⁴([0,ε]×𝕋)} ≤ ½ ‖U - U'‖`, so the
difference vanishes; then the trace bound gives `u = u'` on `[0,ε]`. Here `ε` depends on the `L⁴`
norms of the two representatives (not only on the data), as in the standard argument.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped ENNReal NNReal

attribute [local instance] isProbabilityMeasure_spatialMeasure

theorem slabMeasure_mono {ε δ : ℝ} (h : ε ≤ δ) : slabMeasure ε ≤ slabMeasure δ := by
  rw [slabMeasure_eq, slabMeasure_eq]
  exact Measure.restrict_mono (Set.prod_mono (Set.Icc_subset_Icc le_rfl h) le_rfl) le_rfl

/-- A small time with `ε^{1/16} B ≤ 1/2`. -/
theorem exists_small_time {B : ℝ≥0∞} (hB : B ≠ ⊤) {δ0 : ℝ} (hδ0 : 0 < δ0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ0 ∧ tf ε * B ≤ 2⁻¹ := by
  set Q : ℝ := (2 * B).toReal with hQ
  have hQ0 : 0 ≤ Q := ENNReal.toReal_nonneg
  have h1Q : 0 < 1 + Q := by linarith
  set e : ℝ := ((1 + Q)⁻¹) ^ 16 with he
  have he0 : 0 < e := by positivity
  refine ⟨min δ0 e, lt_min hδ0 he0, min_le_left _ _, ?_⟩
  have htf : tf (min δ0 e) ≤ ENNReal.ofReal ((1 + Q)⁻¹) := by
    refine ENNReal.ofReal_le_ofReal ?_
    calc (min δ0 e) ^ (1 / 16 : ℝ) ≤ e ^ (1 / 16 : ℝ) :=
          Real.rpow_le_rpow (le_min hδ0.le he0.le) (min_le_right _ _) (by norm_num)
      _ = (1 + Q)⁻¹ := by
          rw [he, show (1 / 16 : ℝ) = ((16 : ℕ) : ℝ)⁻¹ by norm_num,
            Real.pow_rpow_inv_natCast (by positivity) (by norm_num)]
  rw [ENNReal.le_inv_iff_mul_le]
  have h2B : 2 * B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hB
  calc tf (min δ0 e) * B * 2 = tf (min δ0 e) * (2 * B) := by ring
    _ ≤ ENNReal.ofReal ((1 + Q)⁻¹) * ENNReal.ofReal Q := by
        rw [hQ, ENNReal.ofReal_toReal h2B]; gcongr
    _ = ENNReal.ofReal ((1 + Q)⁻¹ * Q) := (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_mul_le_iff₀ h1Q, mul_one]
        linarith

theorem eq_zero_of_le_half {x : ℝ≥0∞} (hx : x ≠ ⊤) (h : x ≤ 2⁻¹ * x) : x = 0 := by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hx) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h'
  have h0 : x.toReal = 0 := le_antisymm (by linarith [ENNReal.toReal_nonneg (a := x)])
    ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff x).1 h0 with h1 | h1
  · exact h1
  · exact absurd h1 hx

/-- **Short-time uniqueness** of `L⁴`-Duhamel solutions with equal data. -/
theorem duhamel_unique_short {δ0 : ℝ} (hδ0 : 0 < δ0) (hδ01 : δ0 ≤ 1) {u u' : ℝ → PhysicalL2}
    {U U' : ℝ × PhysicalCircle → ℂ}
    (hU : MemLp U 4 (slabMeasure δ0)) (hU' : MemLp U' 4 (slabMeasure δ0))
    (hsU : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ0)),
      (fun x => U (t, x)) =ᵐ[spatialMeasure] (u t : PhysicalCircle → ℂ))
    (hsU' : ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ0)),
      (fun x => U' (t, x)) =ᵐ[spatialMeasure] (u' t : PhysicalCircle → ℂ))
    (h0 : u 0 = u' 0)
    (hD : ∀ t ∈ Set.Icc 0 δ0, l2ToHm1 (u t) = freeProp (-1) t (l2ToHm1 (u 0)) + duhH (cubF U) t)
    (hD' : ∀ t ∈ Set.Icc 0 δ0,
      l2ToHm1 (u' t) = freeProp (-1) t (l2ToHm1 (u' 0)) + duhH (cubF U') t) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ0 ∧ ∀ t ∈ Set.Icc 0 ε, u t = u' t := by
  obtain ⟨K, hK, hbd⟩ := duhOut_bound
  set a : ℝ≥0∞ := eLpNorm U 4 (slabMeasure δ0)
  set a' : ℝ≥0∞ := eLpNorm U' 4 (slabMeasure δ0)
  have hB : K * (3 * (a ^ 2 + a' ^ 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top hK (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hU.ne, ENNReal.pow_ne_top hU'.ne⟩))
  obtain ⟨ε, hε, hεδ, hsmall⟩ := exists_small_time hB hδ0
  refine ⟨ε, hε, hεδ, ?_⟩
  have hmono := slabMeasure_mono hεδ
  have hUe : MemLp U 4 (slabMeasure ε) := (eLpNorm_mono_measure _ hmono).trans_lt hU
  have hUe' : MemLp U' 4 (slabMeasure ε) := (eLpNorm_mono_measure _ hmono).trans_lt hU'
  have hF : MemLp (cubF U) (4 / 3) (slabMeasure ε) := memLp_cubic hUe
  have hF' : MemLp (cubF U') (4 / 3) (slabMeasure ε) := memLp_cubic hUe'
  have hG : MemLp (cubF U - cubF U') (4 / 3) (slabMeasure ε) := hF.sub hF'
  have hout := duhPair_spec hε (hεδ.trans hδ01) hG
  set v := (duhPair ε (cubF U - cubF U')).1
  set w := (duhPair ε (cubF U - cubF U')).2
  have hsub : ∀ t ∈ Set.Icc 0 ε, v t = u t - u' t := by
    intro t ht
    have htδ : t ∈ Set.Icc 0 δ0 := ⟨ht.1, ht.2.trans hεδ⟩
    refine l2ToHm1_injective ?_
    rw [hout.ident t ht, map_sub, hD t htδ, hD' t htδ, h0,
      duhH_sub (integrable_of_memLp_slab hF) (integrable_of_memLp_slab hF') ht]
    abel
  have hrestr : ∀ {P : ℝ → Prop}, (∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 δ0)), P t) →
      ∀ᵐ t ∂((volume : Measure ℝ).restrict (Set.Icc 0 ε)), P t := fun h =>
    ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl hεδ) h
  have hwU : w =ᵐ[slabMeasure ε] U - U' := by
    refine ae_eq_of_slices (hout.aesm.mono_measure (slabMeasure_le ε))
      (hUe.aestronglyMeasurable.sub hUe'.aestronglyMeasurable) ?_
    have hw := ae_restrict_of_ae (s := Set.Icc 0 ε) hout.slice
    filter_upwards [hw, hrestr hsU, hrestr hsU', ae_restrict_mem measurableSet_Icc]
      with t h1 h2 h3 ht
    rw [hsub t ht] at h1
    filter_upwards [h1, h2, h3, Lp.coeFn_sub (u t) (u' t)] with x hx1 hx2 hx3 hx4
    rw [hx1, hx4, Pi.sub_apply, Pi.sub_apply, ← hx2, ← hx3]
  set x : ℝ≥0∞ := eLpNorm (U - U') 4 (slabMeasure ε) with hxdef
  have hGx : eLpNorm (cubF U - cubF U') (4 / 3) (slabMeasure ε) ≤
      3 * (a ^ 2 + a' ^ 2) * x := by
    refine (eLpNorm_cubic_sub_le hUe.aestronglyMeasurable hUe'.aestronglyMeasurable).trans ?_
    gcongr
    · exact eLpNorm_mono_measure _ hmono
    · exact eLpNorm_mono_measure _ hmono
  have hxx : x ≤ 2⁻¹ * x := by
    calc x = eLpNorm w 4 (slabMeasure ε) := (eLpNorm_congr_ae hwU).symm
      _ ≤ K * tf ε * eLpNorm (cubF U - cubF U') (4 / 3) (slabMeasure ε) :=
          (hbd ε hε (hεδ.trans hδ01) _ _ _ hG hout).2
      _ ≤ K * tf ε * (3 * (a ^ 2 + a' ^ 2) * x) := emL hGx
      _ = tf ε * (K * (3 * (a ^ 2 + a' ^ 2))) * x := by ring
      _ ≤ 2⁻¹ * x := emR hsmall
  have hx0 : x = 0 := eq_zero_of_le_half
    ((eLpNorm_sub_le (by norm_num)).trans_lt
      (ENNReal.add_lt_top.2 ⟨hUe, hUe'⟩)).ne hxx
  have hG0 : eLpNorm (cubF U - cubF U') (4 / 3) (slabMeasure ε) = 0 :=
    le_antisymm (hGx.trans (by rw [hx0, mul_zero])) bot_le
  intro t ht
  have hv := (hbd ε hε (hεδ.trans hδ01) _ _ _ hG hout).1 t ht
  rw [hG0, mul_zero, nonpos_iff_eq_zero, enorm_eq_zero] at hv
  rw [hsub t ht] at hv
  exact sub_eq_zero.1 hv

end LiebLiniger.FixedPeriod.ALLS.PdeB
