                                                                                                                                                                                                                                                             
                                                                             
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Sobolev.SourceEmbeddings
import Mathlib

                                           
                                        
                                                                                        
                                                 
                                                                                           
                                                                  
                                            
                                                                 
                                                                                  
                                                    
                                                                                     

open MeasureTheory Filter Topology
open scoped BigOperators
open NlsGge.Pilot

namespace NlsGge.ThirdConsultation.F

/-- Copied verbatim from DEFINITIONS/F.lean.md lines 64-67. -/
noncomputable def weightedTail (r : ℝ) (N : ℕ) (y : SobolevHilbert r) : ℝ :=
  ∑' n : ℤ, if N < n.natAbs then
    sobolevModeWeight r n *
      ‖(show WeightedHilbert (sobolevModeWeight r) from y) n‖ ^ 2 else 0

section Aux

variable (r : ℝ)

theorem hwpos (n : ℤ) : 0 ≤ sobolevModeWeight r n :=
  ((sobolevModeWeightPositive r).out n).le

theorem sobolev_hasSum (y : SobolevHilbert r) :
    HasSum (fun n : ℤ => sobolevModeWeight r n *
      ‖(show WeightedHilbert (sobolevModeWeight r) from y) n‖ ^ 2)
      (‖(show WeightedHilbert (sobolevModeWeight r) from y)‖ ^ 2) :=
  weightedHilbert_hasSum (sobolevModeWeight r) (show WeightedHilbert (sobolevModeWeight r) from y)

theorem term_summable (N : ℕ) (y : SobolevHilbert r) :
    Summable (fun n : ℤ => if N < n.natAbs then sobolevModeWeight r n *
      ‖(show WeightedHilbert (sobolevModeWeight r) from y) n‖ ^ 2 else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (sobolev_hasSum r y).summable
  · split_ifs <;> first | exact mul_nonneg (hwpos r n) (sq_nonneg _) | exact le_rfl
  · split_ifs <;> first | exact le_rfl | exact mul_nonneg (hwpos r n) (sq_nonneg _)

theorem weightedTail_nonneg (N : ℕ) (y : SobolevHilbert r) : 0 ≤ weightedTail r N y := by
  unfold weightedTail
  apply tsum_nonneg
  intro n
  split_ifs <;> first | exact mul_nonneg (hwpos r n) (sq_nonneg _) | exact le_rfl

theorem weightedTail_le_norm_sq (N : ℕ) (y : SobolevHilbert r) :
    weightedTail r N y ≤ ‖(show WeightedHilbert (sobolevModeWeight r) from y)‖ ^ 2 := by
  unfold weightedTail
  rw [← (sobolev_hasSum r y).tsum_eq]
  refine Summable.tsum_le_tsum (fun n => ?_) (term_summable r N y) (sobolev_hasSum r y).summable
  split_ifs <;> first | exact le_rfl | exact mul_nonneg (hwpos r n) (sq_nonneg _)

theorem sq_norm_add_le' (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  nlinarith [mul_self_le_mul_self (norm_nonneg _) h, sq_nonneg (‖a‖ - ‖b‖)]

theorem ite_triangle (p : Prop) [Decidable p] (w : ℝ) (hw : 0 ≤ w) (a b : ℂ) :
    (if p then w * ‖a‖ ^ 2 else 0) ≤
      2 * (if p then w * ‖b‖ ^ 2 else 0) + 2 * (if p then w * ‖a - b‖ ^ 2 else 0) := by
  split_ifs
  · have h := sq_norm_add_le' b (a - b)
    have e : b + (a - b) = a := by ring
    rw [e] at h
    nlinarith [mul_le_mul_of_nonneg_left h hw]
  · norm_num

theorem weightedTail_triangle (N : ℕ) (y z : SobolevHilbert r) :
    weightedTail r N y ≤ 2 * weightedTail r N z + 2 * weightedTail r N (y - z) := by
  have hz' : Summable (fun n : ℤ => 2 * (if N < n.natAbs then sobolevModeWeight r n *
      ‖(show WeightedHilbert (sobolevModeWeight r) from z) n‖ ^ 2 else 0)) :=
    (term_summable r N z).mul_left 2
  have hd' : Summable (fun n : ℤ => 2 * (if N < n.natAbs then sobolevModeWeight r n *
      ‖(show WeightedHilbert (sobolevModeWeight r) from (y - z)) n‖ ^ 2 else 0)) :=
    (term_summable r N (y - z)).mul_left 2
  unfold weightedTail
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add hz' hd']
  refine Summable.tsum_le_tsum (fun n => ?_) (term_summable r N y) (hz'.add hd')
  exact ite_triangle _ (sobolevModeWeight r n) (hwpos r n) _ _

theorem weightedTail_tendsto_zero (y : SobolevHilbert r) :
    Tendsto (fun N : ℕ => weightedTail r N y) atTop (𝓝 0) := by
  have key := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (n : ℤ) => if N < n.natAbs then sobolevModeWeight r n *
      ‖(show WeightedHilbert (sobolevModeWeight r) from y) n‖ ^ 2 else 0)
    (g := fun _ : ℤ => (0 : ℝ))
    (bound := fun n : ℤ => sobolevModeWeight r n *
      ‖(show WeightedHilbert (sobolevModeWeight r) from y) n‖ ^ 2)
    (sobolev_hasSum r y).summable ?_ ?_
  · simpa [weightedTail] using key
  · intro n
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    simp [not_lt.mpr hN]
  · refine Eventually.of_forall (fun N n => ?_)
    split_ifs
    · exact (Real.norm_of_nonneg (mul_nonneg (hwpos r n) (sq_nonneg _))).le
    · rw [norm_zero]
      exact mul_nonneg (hwpos r n) (sq_nonneg _)

end Aux

/-- Uniform square tails, general Sobolev order `r`. -/
theorem f007_gen (r : ℝ) (zseq : ℕ → SobolevHilbert r) (z : SobolevHilbert r)
    (hz : Tendsto zseq atTop (𝓝 z)) :
    (∀ N : ℕ, BddAbove (Set.range (fun k : ℕ => weightedTail r N (zseq k)))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, weightedTail r N (zseq k) < ε) ∧
    Tendsto (fun N : ℕ => ⨆ k : ℕ, weightedTail r N (zseq k)) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun k => ‖zseq k - z‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hz
  have hsq : Tendsto (fun k => ‖zseq k - z‖ ^ 2) atTop (𝓝 0) := by
    simpa using hnorm.pow 2
  have hE : ∀ N k, weightedTail r N (zseq k) ≤
      2 * weightedTail r N z + 2 * ‖zseq k - z‖ ^ 2 := by
    intro N k
    have h1 := weightedTail_triangle r N (zseq k) z
    have h2 : weightedTail r N (zseq k - z) ≤ ‖zseq k - z‖ ^ 2 :=
      weightedTail_le_norm_sq r N (zseq k - z)
    linarith
  have hbdd : BddAbove (Set.range fun k => ‖zseq k - z‖ ^ 2) := hsq.bddAbove_range
  obtain ⟨B, hB⟩ := hbdd
  have hev : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ k : ℕ, weightedTail r N (zseq k) < ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1
      (hsq.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 8 from div_pos hε (by norm_num))))
    have hz0 : ∀ᶠ N in atTop, weightedTail r N z < ε / 4 :=
      (tendsto_order.1 (weightedTail_tendsto_zero r z)).2 (ε / 4) (div_pos hε (by norm_num))
    have hfin : ∀ᶠ N in atTop, ∀ k ∈ Finset.range K, weightedTail r N (zseq k) < ε := by
      rw [Filter.eventually_all_finset]
      intro k _
      exact (tendsto_order.1 (weightedTail_tendsto_zero r (zseq k))).2 ε hε
    filter_upwards [hz0, hfin] with N hN0 hNfin k
    by_cases hk : k < K
    · exact hNfin k (Finset.mem_range.2 hk)
    · have hk' : K ≤ k := not_lt.1 hk
      have h1 := hE N k
      have h2 := hK k hk'
      linarith
  refine ⟨?_, ?_, ?_⟩
  · intro N
    refine ⟨2 * weightedTail r N z + 2 * B, ?_⟩
    rintro _ ⟨k, rfl⟩
    show weightedTail r N (zseq k) ≤ _
    have h1 := hE N k
    have h2 : ‖zseq k - z‖ ^ 2 ≤ B := hB (Set.mem_range_self k)
    linarith
  · intro ε hε
    exact (hev ε hε).exists
  · rw [tendsto_order]
    constructor
    · intro a ha
      exact Eventually.of_forall fun N =>
        lt_of_lt_of_le ha (Real.iSup_nonneg fun k => weightedTail_nonneg r N (zseq k))
    · intro b hb
      filter_upwards [hev (b / 2) (half_pos hb)] with N hN
      have hle : (⨆ k : ℕ, weightedTail r N (zseq k)) ≤ b / 2 :=
        ciSup_le (fun k => (hN k).le)
      linarith

/-- F-007, Pro's signature (STATEMENTS/F.md lines 127-138). -/
theorem f007 (m : ℕ) (hm : 2 ≤ m)
    (zseq : ℕ → SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (z : SobolevHilbert ((m - 1 : ℕ) : ℝ))
    (hz : Tendsto zseq atTop (nhds z)) :
    (∀ N : ℕ, BddAbove (Set.range
      (fun k : ℕ => weightedTail ((m - 1 : ℕ) : ℝ) N (zseq k)))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ,
      weightedTail ((m - 1 : ℕ) : ℝ) N (zseq k) < ε) ∧
    Tendsto (fun N : ℕ => ⨆ k : ℕ,
      weightedTail ((m - 1 : ℕ) : ℝ) N (zseq k)) atTop (nhds 0) :=
  f007_gen ((m - 1 : ℕ) : ℝ) zseq z hz


end NlsGge.ThirdConsultation.F
