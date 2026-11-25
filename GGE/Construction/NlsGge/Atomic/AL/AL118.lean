import Mathlib
import NlsGge.Hierarchy.ALTilt38
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.Hierarchy.ALPositiveDecompositions38

                                                                                                  
                                                                                       
                                                                                                                           
set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core NlsGge.Pilot
namespace NlsGge.ThirdConsultation.AL
noncomputable section

namespace al118Aux

theorem q_le_G {L : ℕ} [NeZero L] (hL : 3 ≤ L) {α : ZMod L → ℂ} (hα : IsALField38 α) {h : ℝ}
    (hh : h = (L : ℝ)⁻¹) :
    ∑ k : ZMod L, (1 + alOmega38 h k.valMinAbs ^ 4) * ‖ZMod.dft α k‖ ^ 2 ≤ alTiltG38 h α := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hM : ∑ i, ‖α i‖ ^ 2 ≤ alMass38 L α := by
    rw [← alMd_eq_alMass38, alMd_split]
    have : 0 ≤ ∑ j, alEll (alR α j) :=
      Finset.sum_nonneg fun j _ => alEll_nonneg (by unfold alR; positivity)
        (alR_lt_one α hα j)
    have e : ∑ j, alR α j = ∑ i, ‖α i‖ ^ 2 := rfl
    linarith
  have hK : ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 ≤ alK38 α 2 := by
    rw [alK38_two_eq_alKd hL hα, alKd_squares]
    have h1 : 0 ≤ ∑ j, (alR α (j + 1) - alR α j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have h2 : 0 ≤ ∑ j, alR α j * ‖α (j + 1) - α (j - 1)‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (by unfold alR; positivity) (by positivity)
    have h4 : 0 ≤ ∑ j, (-Real.log (1 - alR α j) - alR α j - (1 / 2) * alR α j ^ 2) :=
      Finset.sum_nonneg fun j _ => alEll_sq_nonneg (by unfold alR; positivity)
        (alR_lt_one α hα j)
    refine le_add_of_le_of_nonneg (le_add_of_le_of_nonneg (le_add_of_le_of_nonneg
      (le_add_of_le_of_nonneg le_rfl ?_) ?_) ?_) ?_
    · exact mul_nonneg (by norm_num) h1
    · exact h2
    · positivity
    · exact mul_nonneg (by norm_num) h4
  have hP := sum_norm_sq_eq_dft38 α hh
  have hD := alDelta_parseval38 2 α
  rw [sum_shift_alDelta38] at hD
  have hG : alTiltG38 h α = h⁻¹ * alMass38 L α + (h⁻¹) ^ 5 * alK38 α 2 := by
    unfold alTiltG38 alQ38
    rw [alMomentK38_eq_alK38, alMomentK38_eq_alK38, alK38_zero]; simp
  have hhL : (L : ℝ)⁻¹ = h := hh.symm
  rw [hG]
  have a1 : h⁻¹ * ∑ i, ‖α i‖ ^ 2 ≤ h⁻¹ * alMass38 L α :=
    mul_le_mul_of_nonneg_left hM (by positivity)
  have a2 : (h⁻¹) ^ 5 * ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 ≤
      (h⁻¹) ^ 5 * alK38 α 2 := mul_le_mul_of_nonneg_left hK (by positivity)
  have b1 : h⁻¹ * ∑ i, ‖α i‖ ^ 2 = ∑ k : ZMod L, ‖ZMod.dft α k‖ ^ 2 := by
    rw [hP]; field_simp
  have b2 : (h⁻¹) ^ 5 * ∑ j, ‖α (j + 1) - 2 * α j + α (j - 1)‖ ^ 2 =
      ∑ k : ZMod L, alOmega38 h k.valMinAbs ^ 4 * ‖ZMod.dft α k‖ ^ 2 := by
    rw [hD, hhL, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Real.pi * (k.valMinAbs : ℝ) / L = Real.pi * k.valMinAbs * h := by rw [hh]; ring
    unfold alOmega38
    rw [this]
    have : h ≠ 0 := hh0.ne'
    field_simp
    ring
  have : ∑ k : ZMod L, (1 + alOmega38 h k.valMinAbs ^ 4) * ‖ZMod.dft α k‖ ^ 2 =
      ∑ k : ZMod L, ‖ZMod.dft α k‖ ^ 2 +
        ∑ k : ZMod L, alOmega38 h k.valMinAbs ^ 4 * ‖ZMod.dft α k‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  linarith

theorem half_le_q {L : ℕ} [NeZero L] {α : ZMod L → ℂ} {h : ℝ} (hh : h = (L : ℝ)⁻¹) :
    (1 / 2 : ℝ) * alH2Sq38 α ≤
      ∑ k : ZMod L, (1 + alOmega38 h k.valMinAbs ^ 4) * ‖ZMod.dft α k‖ ^ 2 := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh0 : 0 < h := by rw [hh]; positivity
  unfold alH2Sq38
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : |((k.valMinAbs : ℤ) : ℝ)| * h ≤ 1 / 2 := by
    have h1 := ZMod.natAbs_valMinAbs_le k
    have h2 : ((k.valMinAbs.natAbs : ℕ) : ℝ) ≤ (L : ℝ) / 2 := by
      have : (k.valMinAbs.natAbs : ℝ) * 2 ≤ L := by
        have := Nat.div_mul_le_self L 2
        exact_mod_cast le_trans (Nat.mul_le_mul_right 2 h1) this
      linarith
    have h3 : |((k.valMinAbs : ℤ) : ℝ)| = (k.valMinAbs.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    rw [h3, hh]
    rw [← div_eq_mul_inv, div_le_iff₀ hLr]; linarith
  have hω := alOmega_abs_ge38 hh0 hk
  set x : ℝ := ((k.valMinAbs : ℤ) : ℝ) with hx
  set ω := alOmega38 h k.valMinAbs with hωd
  have h4 : (4 * |x|) ^ 4 ≤ |ω| ^ 4 := pow_le_pow_left₀ (by positivity) hω 4
  have h5 : |x| ^ 4 = x ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  have h6 : |ω| ^ 4 = ω ^ 4 := by rw [pow_abs, abs_of_nonneg (by positivity)]
  rw [mul_pow, h5, h6] at h4
  have h7 : (1 + x ^ 2) ^ 2 ≤ 2 * (1 + ω ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg x]
  have : 0 ≤ ‖ZMod.dft α k‖ ^ 2 := by positivity
  nlinarith

theorem h2_eq_interp (N : ℕ) (û : ZMod (2 * N + 1) → ℂ) :
    (∑ k : ZMod (2 * N + 1), (1 + ((k.valMinAbs : ℤ) : ℝ) ^ 2) ^ 2 * ‖û k‖ ^ 2) =
      ‖alQ4Interp38 2 N û‖ ^ 2 := by
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) N →
      sobolevModeWeight 2 n * ‖alQ4Ext38 N û n‖ ^ 2 = 0 := by
    intro n hn
    have : ¬ |n| ≤ (N : ℤ) := fun h => hn (Finset.mem_Icc.2 (abs_le.1 h))
    simp [alQ4Ext38, this]
  have hsum : Summable (fun n : ℤ => sobolevModeWeight 2 n * ‖alQ4Ext38 N û n‖ ^ 2) :=
    summable_of_ne_finset_zero hsupp
  unfold alQ4Interp38
  rw [seqRealization_norm_sq38 _ _ hsum, tsum_eq_sum hsupp,
    ← sum_valMinAbs_eq_Icc38 N (fun n => sobolevModeWeight 2 n * ‖alQ4Ext38 N û n‖ ^ 2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := valMinAbs_mem_Icc38 N k
  have habs : |k.valMinAbs| ≤ (N : ℤ) := abs_le.2 (Finset.mem_Icc.1 hk)
  have hext : alQ4Ext38 N û k.valMinAbs = û k := by
    simp [alQ4Ext38, habs]
  have hw : sobolevModeWeight 2 k.valMinAbs = (1 + ((k.valMinAbs : ℤ) : ℝ) ^ 2) ^ 2 := by
    unfold sobolevModeWeight japaneseBracket
    rw [Real.rpow_eq_pow, show (2 * (2 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show Real.sqrt (1 + ((k.valMinAbs : ℤ) : ℝ) ^ 2) ^ 4 =
        (Real.sqrt (1 + ((k.valMinAbs : ℤ) : ℝ) ^ 2) ^ 2) ^ 2 by ring, Real.sq_sqrt (by positivity)]
  rw [hext, hw]

end al118Aux

theorem al118 (N : ℕ) (hN : 2 ≤ N) (alpha : ZMod (2 * N + 1) → ℂ)
    (halpha : IsALField38 alpha) :
    let h : ℝ := alMeshStep38 N
    let q : ℝ := ∑ k : ZMod (2 * N + 1),
      (1 + alOmega38 h k.valMinAbs ^ 4) * ‖ZMod.dft alpha k‖ ^ 2
    alH2Sq38 alpha = ‖alQ4Interp38 2 N (ZMod.dft alpha)‖ ^ 2 ∧
    alTiltG38 h alpha = alMd alpha / h + alKd alpha / h ^ 5 ∧
    q ≤ alTiltG38 h alpha ∧ (1 / 2 : ℝ) * alH2Sq38 alpha ≤ q := by
  intro h q
  have hL3 : 3 ≤ 2 * N + 1 := by omega
  have hh : h = ((2 * N + 1 : ℕ) : ℝ)⁻¹ := by
    show alMeshStep38 N = _
    unfold alMeshStep38
    push_cast
    rw [one_div]
  refine ⟨al118Aux.h2_eq_interp N (ZMod.dft alpha), ?_, al118Aux.q_le_G hL3 halpha hh,
    al118Aux.half_le_q hh⟩
  have hG : alTiltG38 h alpha = h⁻¹ * alMass38 (2 * N + 1) alpha + (h⁻¹) ^ 5 * alK38 alpha 2 := by
    unfold alTiltG38 alQ38
    rw [alMomentK38_eq_alK38, alMomentK38_eq_alK38, alK38_zero]; simp
  rw [hG, alK38_two_eq_alKd hL3 halpha, ← alMd_eq_alMass38, div_eq_inv_mul, div_eq_inv_mul, inv_pow]

end
end NlsGge.ThirdConsultation.AL
