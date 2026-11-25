import Mathlib
import NlsGge.GK38.AbelianNullGapRoots
import NlsGge.GK38.AbelianDirectionSeries
import NlsGge.GK38.AbelianJacobianNumerator
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.Analysis.RegularizedDeterminant.RealHilbertSchmidt
import NlsGge.Atomic.G2.G2046

/- G2-055 PROOF01 (proof development, AUTHOR; not reviewed). Statement verbatim from STATEMENTS/G2.md G2-055;
   `linearizedPsi` verbatim from DEFINITIONS/G2.lean.md; `gapSegment` is hosted by landed G2-046 (imported).  Route: clause 1 `variation_entire`; clause 3 `null_direction_gap_roots`; clause 2 from
   `variation_hasSum` + `variation_unit_column` + `numerator_factor` (column_r = N/(sigma_r - z)) and an l2 summability of 1/(sigma_r - z). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def linearizedPsi (n : ℤ) (s h : P2Space38 n) (z : ℂ) : ℂ :=
  p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) z

namespace G2055Aux
open NlsGge.GK38.P4NumeratorVariation

theorem sigma_extend (n : ℤ) (s : P2Space38 n) (r : P2Index38 n) :
    Lib.sigmaOf (p2Extend38 n s) r.1 = countingCenter38 r.1 + s r := by
  simp [Lib.sigmaOf, countingCenter38]

theorem psi_hasSum (n : ℤ) (s h : P2Space38 n) (z : ℂ)
    (hz : ∀ r : P2Index38 n, countingCenter38 r.1 + s r - z ≠ 0) :
    HasSum (fun r : P2Index38 n => p2Numerator38 n s z * (h r / (countingCenter38 r.1 + s r - z)))
      (linearizedPsi n s h z) := by
  have hS := variation_hasSum n (p2Extend38 n s) (p2Extend38 n h) z
  set f : ℤ → ℂ := fun r => if hr : r = n then 0 else
        p2Extend38 n h r * p3NumeratorColumn38 n r (p2Extend38 n s) z with hf
  have hterm : ∀ r : ℤ, p4NumeratorVariation38 n (p2Extend38 n s)
      (lp.single 2 r (p2Extend38 n h r)) z = f r := by
    intro r
    by_cases hr : r = n
    · subst hr
      rw [hf]
      simp only [dite_true, p2Extend_self38]
      rw [← variationCLM_apply, lp.single_zero, map_zero]
    · rw [hf]
      simp only [hr, dite_false]
      have hu := variation_unit_column n r hr (p2Extend38 n s) z
      rw [← variationCLM_apply]
      have : lp.single 2 r (p2Extend38 n h r) = (p2Extend38 n h r) • (lp.single 2 r (1 : ℂ) : Lib.L2Seq) := by
        rw [← lp.single_smul]; simp
      rw [this, map_smul, variationCLM_apply, hu, smul_eq_mul]
  have hS' : HasSum f (p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) z) := by
    have e : (fun r : ℤ => p4NumeratorVariation38 n (p2Extend38 n s)
        (lp.single 2 r (p2Extend38 n h r)) z) = f := funext hterm
    rw [e] at hS
    exact hS
  have hsub : HasSum (f ∘ Subtype.val : P2Index38 n → ℂ)
      (p4NumeratorVariation38 n (p2Extend38 n s) (p2Extend38 n h) z) := by
    refine (Function.Injective.hasSum_iff Subtype.val_injective (fun x hx => ?_)).2 hS'
    by_cases hxn : x = n
    · rw [hf]; simp [hxn]
    · exact absurd ⟨⟨x, hxn⟩, rfl⟩ hx
  have e2 : (fun r : P2Index38 n => p2Numerator38 n s z * (h r / (countingCenter38 r.1 + s r - z))) =
      (f ∘ Subtype.val) := by
    funext r
    have hr := r.2
    have hσ : Lib.sigmaOf (p2Extend38 n s) r.1 - z ≠ 0 := by
      rw [sigma_extend]; exact hz r
    have hnf := NlsGge.GK38.P3JacobianColumns.numerator_factor n r.1 hr (p2Extend38 n s) z
    have hcol : p3NumeratorColumn38 n r.1 (p2Extend38 n s) z =
        p2FullNumerator38 n (p2Extend38 n s) z / (Lib.sigmaOf (p2Extend38 n s) r.1 - z) := by
      rw [eq_div_iff hσ, mul_comm]; exact hnf.symm
    simp only [Function.comp, hf, hr, dite_false, p2Extend_at38]
    rw [hcol, sigma_extend]
    unfold p2Numerator38
    ring
  rw [e2]
  exact hsub

theorem inv_sq_summable (n : ℤ) (s : P2Space38 n) (z : ℂ)
    (hz : ∀ r : P2Index38 n, countingCenter38 r.1 + s r - z ≠ 0) :
    Summable (fun r : P2Index38 n => ‖(1 : ℂ) / (countingCenter38 r.1 + s r - z)‖ ^ 2) := by
  have hs : Summable (fun r : P2Index38 n => ‖s r‖ ^ 2) :=
    (NlsGge.Analysis.RegularizedDeterminant.memLp_two_iff _).1 s.2
  have ht := tendsto_order.1 hs.tendsto_cofinite_zero |>.2 1 one_pos
  set K0 : ℕ := ⌈2 * (1 + ‖z‖) / Real.pi⌉₊ + 1 with hK0
  have hg : Summable (fun r : P2Index38 n => (4 / Real.pi ^ 2) * (1 / ((r.1 : ℝ)) ^ 2)) := by
    have h1 : Summable (fun m : ℤ => 1 / ((m : ℝ)) ^ 2) :=
      Real.summable_one_div_int_pow.2 (by norm_num)
    exact (h1.comp_injective Subtype.val_injective).mul_left _
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Filter.eventually_cofinite]
  have hfin1 : {r : P2Index38 n | ¬ (‖s r‖ ^ 2 < 1)}.Finite := by
    simpa [Filter.eventually_cofinite] using ht
  have hfin2 : {r : P2Index38 n | ¬ ((K0 : ℤ) ≤ |r.1|)}.Finite := by
    refine ((Set.finite_Icc (-(K0 : ℤ)) (K0 : ℤ)).preimage
      (Subtype.val_injective.injOn)).subset (fun r hr => ?_)
    simp only [Set.mem_setOf_eq, not_le] at hr
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> [skip; skip] <;> (rw [abs_lt] at hr; omega)
  refine (hfin1.union hfin2).subset (fun r hr => ?_)
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  simp only [Set.mem_setOf_eq, not_not] at hcon
  obtain ⟨hs1, hK⟩ := hcon
  simp only [Set.mem_setOf_eq] at hr
  apply hr
  have hsr : ‖s r‖ ≤ 1 := by nlinarith [norm_nonneg (s r)]
  have hKr : (K0 : ℝ) ≤ |(r.1 : ℝ)| := by
    have : ((K0 : ℤ) : ℝ) ≤ ((|r.1| : ℤ) : ℝ) := by exact_mod_cast hK
    simpa using this
  have hK1 : (1 : ℝ) ≤ |(r.1 : ℝ)| := by
    have : (1 : ℝ) ≤ (K0 : ℝ) := by rw [hK0]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * (1 + ‖z‖) / Real.pi⌉₊]
    linarith
  have hKz : 2 * (1 + ‖z‖) / Real.pi ≤ (K0 : ℝ) := by
    rw [hK0]; push_cast
    linarith [Nat.le_ceil (2 * (1 + ‖z‖) / Real.pi)]
  have hpr : 2 * (1 + ‖z‖) ≤ Real.pi * |(r.1 : ℝ)| := by
    have h1 : 2 * (1 + ‖z‖) / Real.pi ≤ |(r.1 : ℝ)| := hKz.trans hKr
    rw [div_le_iff₀ Real.pi_pos] at h1
    linarith
  have hcc : ‖countingCenter38 r.1‖ = Real.pi * |(r.1 : ℝ)| := by
    simp [countingCenter38, norm_mul, abs_of_pos Real.pi_pos, mul_comm]
  have hlow : Real.pi * |(r.1 : ℝ)| ≤ ‖countingCenter38 r.1 + s r - z‖ + ‖s r‖ + ‖z‖ := by
    rw [← hcc]
    calc ‖countingCenter38 r.1‖ = ‖(countingCenter38 r.1 + s r - z) - s r + z‖ := by ring_nf
      _ ≤ ‖(countingCenter38 r.1 + s r - z) - s r‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖countingCenter38 r.1 + s r - z‖ + ‖s r‖ + ‖z‖ := by
          have := norm_sub_le (countingCenter38 r.1 + s r - z) (s r)
          linarith
  set a : ℝ := ‖countingCenter38 r.1 + s r - z‖ with ha
  have ha2 : Real.pi * |(r.1 : ℝ)| / 2 ≤ a := by linarith
  have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_div, norm_one, ← ha, div_pow, one_pow]
  have hr2 : ((r.1 : ℝ)) ^ 2 = |(r.1 : ℝ)| ^ 2 := (sq_abs _).symm
  rw [hr2]
  have hpos : 0 < |(r.1 : ℝ)| := lt_of_lt_of_le one_pos hK1
  rw [show 4 / Real.pi ^ 2 * (1 / |(r.1 : ℝ)| ^ 2) = 1 / (Real.pi * |(r.1 : ℝ)| / 2) ^ 2 by
    field_simp; norm_num]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) ha2 2)

theorem psi_summable (n : ℤ) (s h : P2Space38 n) (z : ℂ)
    (hz : ∀ r : P2Index38 n, countingCenter38 r.1 + s r - z ≠ 0) :
    Summable (fun r : P2Index38 n => h r / (countingCenter38 r.1 + s r - z)) := by
  have hh : Summable (fun r : P2Index38 n => ‖h r‖ ^ 2) :=
    (NlsGge.Analysis.RegularizedDeterminant.memLp_two_iff _).1 h.2
  have hw := inv_sq_summable n s z hz
  refine Summable.of_norm_bounded ((hh.add hw).mul_left (1 / 2 : ℝ)) (fun r => ?_)
  have : h r / (countingCenter38 r.1 + s r - z) = h r * ((1 : ℂ) / (countingCenter38 r.1 + s r - z)) := by
    ring
  rw [this, norm_mul]
  nlinarith [sq_nonneg (‖h r‖ - ‖(1 : ℂ) / (countingCenter38 r.1 + s r - z)‖)]

end G2055Aux

open G2055Aux in
theorem G2_055 (n : ℤ) (s h : P2Space38 n) :
    AnalyticOnNhd ℂ (linearizedPsi n s h) Set.univ ∧
    (∀ z : ℂ, (∀ r : P2Index38 n, countingCenter38 r.1+s r-z ≠ 0) →
      Summable (fun r : P2Index38 n => h r/(countingCenter38 r.1+s r-z)) ∧
      linearizedPsi n s h z = p2Numerator38 n s z *
        ∑' r : P2Index38 n, h r/(countingCenter38 r.1+s r-z)) ∧
    (p2RealSeq38 n s → p2RealSeq38 n h → ∀ u : PhysicalL2,
      (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (realSlice u,t)) s) h=0 →
      ∀ m : P2Index38 n, ∃ x : ℝ,
        (x : ℂ) ∈ gapSegment (realSlice u) m.1 ∧ linearizedPsi n s h (x : ℂ)=0) := by
  refine ⟨NlsGge.GK38.P4NumeratorVariation.variation_entire n (p2Extend38 n s) (p2Extend38 n h),
    fun z hz => ⟨psi_summable n s h z hz, ?_⟩, ?_⟩
  · rw [← (psi_hasSum n s h z hz).tsum_eq, tsum_mul_left]
  · intro hs hh u hnull m
    obtain ⟨x, hx, h0⟩ := NlsGge.GK38.P4NumeratorVariation.null_direction_gap_roots n u s h hs hh hnull m
    exact ⟨x, hx, h0⟩


end
end NlsGge.GKDefinitionDesign
