import Mathlib

                                                                                                              
                                                                                                               
                                                                                                                      
                                                                                                               
                                                                                                                 
                                                                                                    
set_option autoImplicit false
open Filter Topology
open scoped BigOperators ENNReal

namespace NlsGge.ThirdConsultation.M018D

theorem fin_tail (f : ℤ → ℝ) (L : ℕ) (ε : ℝ)
    (h : (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal |f n| else 0) < ENNReal.ofReal ε)
    (F : Finset ℤ) : ∑ n ∈ F, (if L ≤ n.natAbs then |f n| else 0) ≤ ε := by
  have h1 : ENNReal.ofReal (∑ n ∈ F, (if L ≤ n.natAbs then |f n| else 0)) =
      ∑ n ∈ F, (if L ≤ n.natAbs then ENNReal.ofReal |f n| else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => by split_ifs <;> simp [abs_nonneg])]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    split_ifs <;> simp
  have h2 : ENNReal.ofReal (∑ n ∈ F, (if L ≤ n.natAbs then |f n| else 0)) < ENNReal.ofReal ε := by
    rw [h1]; exact lt_of_le_of_lt (ENNReal.sum_le_tsum F) h
  exact ((ENNReal.ofReal_lt_ofReal_iff').1 h2).1.le

theorem tail_summable (f : ℤ → ℝ) (hf : Summable f) (L : ℕ) :
    Summable (fun n : ℤ => if L ≤ n.natAbs then |f n| else 0) :=
  Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [abs_nonneg])
    (fun n => by split_ifs <;> simp) ((summable_abs_iff).2 hf)

theorem tsum_tail_le (f : ℤ → ℝ) (hf : Summable f) (L : ℕ) (ε : ℝ)
    (hF : ∀ F : Finset ℤ, ∑ n ∈ F, (if L ≤ n.natAbs then |f n| else 0) ≤ ε) :
    |∑' n : ℤ, (if L ≤ n.natAbs then f n else 0)| ≤ ε := by
  have hg := tail_summable f hf L
  have hg' : Summable (fun n : ℤ => ‖(if L ≤ n.natAbs then f n else 0)‖) := by
    convert hg using 1; funext n; split_ifs <;> simp [Real.norm_eq_abs]
  calc |∑' n : ℤ, (if L ≤ n.natAbs then f n else 0)|
      ≤ ∑' n : ℤ, ‖(if L ≤ n.natAbs then f n else 0)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hg'
    _ = ∑' n : ℤ, (if L ≤ n.natAbs then |f n| else 0) := by
        congr 1; funext n; split_ifs <;> simp [Real.norm_eq_abs]
    _ ≤ ε := Real.tsum_le_of_sum_le (fun n => by dsimp only; split_ifs <;> simp [abs_nonneg]) hF

theorem split_tsum (f : ℤ → ℝ) (hf : Summable f) (L : ℕ) :
    ∑' n : ℤ, f n = ∑ n ∈ Finset.Ioo (-(L : ℤ)) L, f n +
      ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0) := by
  have hP : ∀ n : ℤ, n ∈ Finset.Ioo (-(L : ℤ)) L ↔ ¬ (L ≤ n.natAbs) := by
    intro n; simp only [Finset.mem_Ioo]; omega
  have hB : Summable (fun n : ℤ => if L ≤ n.natAbs then f n else 0) := by
    refine (summable_abs_iff).1 ?_
    convert tail_summable f hf L using 1; funext n; split_ifs <;> simp
  have hA : Summable (fun n : ℤ => if L ≤ n.natAbs then 0 else f n) :=
    summable_of_ne_finset_zero (s := Finset.Ioo (-(L : ℤ)) L) (fun n hn => by
      rw [hP, not_not] at hn; simp [hn])
  have hsplit : (fun n : ℤ => f n) = fun n =>
      (if L ≤ n.natAbs then 0 else f n) + (if L ≤ n.natAbs then f n else 0) := by
    funext n; split_ifs <;> simp
  conv_lhs => rw [hsplit]
  rw [hA.tsum_add hB]
  congr 1
  rw [tsum_eq_sum (s := Finset.Ioo (-(L : ℤ)) L) (fun n hn => by
    rw [hP, not_not] at hn; simp [hn])]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [if_neg ((hP n).1 hn)]

theorem tail_tendsto (f : ℤ → ℝ) (t : ℝ) (hf : HasSum f t) :
    Tendsto (fun L : ℕ => ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0)) atTop (𝓝 0) := by
  have hP : Tendsto (fun L : ℕ => Finset.Ioo (-(L : ℤ)) L) atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun L L' h n hn => ?_) (fun n => ?_)
    · simp only [Finset.mem_Ioo] at hn ⊢; constructor <;> omega
    · refine ⟨n.natAbs + 1, ?_⟩; simp only [Finset.mem_Ioo]; constructor <;> omega
  have h1 : Tendsto (fun L : ℕ => ∑ n ∈ Finset.Ioo (-(L : ℤ)) L, f n) atTop (𝓝 t) :=
    hf.comp hP
  have h2 : (fun L : ℕ => ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0)) =
      fun L : ℕ => t - ∑ n ∈ Finset.Ioo (-(L : ℤ)) L, f n := by
    funext L; rw [← hf.tsum_eq, split_tsum f hf.summable L]; ring
  rw [h2, show (0 : ℝ) = t - t by ring]
  exact tendsto_const_nhds.sub h1

theorem tail_anti (f : ℤ → ℝ) (hnn : ∀ n, 0 ≤ f n) (hf : Summable f) {L L' : ℕ} (h : L ≤ L') :
    ∑' n : ℤ, (if L' ≤ n.natAbs then f n else 0) ≤ ∑' n : ℤ, (if L ≤ n.natAbs then f n else 0) := by
  have hs : ∀ K : ℕ, Summable (fun n : ℤ => if K ≤ n.natAbs then f n else 0) := by
    intro K
    convert tail_summable f hf K using 1; funext n; split_ifs <;> simp [abs_of_nonneg (hnn n)]
  refine (hs L').tsum_le_tsum (fun n => ?_) (hs L)
  by_cases h1 : L' ≤ n.natAbs
  · rw [if_pos h1, if_pos (le_trans h h1)]
  · rw [if_neg h1]; split_ifs <;> simp [hnn n]

/-- Scheffé-type uniform tails: nonnegative, pointwise convergent, with convergent sums. -/
theorem scheffe_tails (a : ℕ → ℤ → ℝ) (b : ℤ → ℝ) (s : ℕ → ℝ) (S : ℝ)
    (hnn : ∀ j n, 0 ≤ a j n)
    (hpt : ∀ n : ℤ, Tendsto (fun j => a j n) atTop (𝓝 (b n)))
    (hsum : ∀ j, HasSum (a j) (s j)) (hb : HasSum b S) (hs : Tendsto s atTop (𝓝 S)) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal |a j n| else 0) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨L0, hL0⟩ := ((tail_tendsto b S hb).eventually (gt_mem_nhds hε)).exists
  have hg : Tendsto (fun j => ∑' n : ℤ, (if L0 ≤ n.natAbs then a j n else 0)) atTop
      (𝓝 (∑' n : ℤ, (if L0 ≤ n.natAbs then b n else 0))) := by
    have e : ∀ j, ∑' n : ℤ, (if L0 ≤ n.natAbs then a j n else 0) =
        s j - ∑ n ∈ Finset.Ioo (-(L0 : ℤ)) L0, a j n := by
      intro j; rw [← (hsum j).tsum_eq, split_tsum _ (hsum j).summable L0]; ring
    have eb : ∑' n : ℤ, (if L0 ≤ n.natAbs then b n else 0) =
        S - ∑ n ∈ Finset.Ioo (-(L0 : ℤ)) L0, b n := by
      rw [← hb.tsum_eq, split_tsum _ hb.summable L0]; ring
    simp only [e, eb]
    exact hs.sub (tendsto_finset_sum _ (fun n _ => hpt n))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (hg.eventually (gt_mem_nhds hL0))
  have hfin : ∀ᶠ L : ℕ in atTop, ∀ j ∈ Finset.range J,
      ∑' n : ℤ, (if L ≤ n.natAbs then a j n else 0) < ε :=
    (Filter.eventually_all_finset _).2 (fun j _ =>
      (tail_tendsto (a j) (s j) (hsum j)).eventually (gt_mem_nhds hε))
  obtain ⟨L, hL, hLL0⟩ := (hfin.and (Filter.eventually_ge_atTop L0)).exists
  refine ⟨L, fun j => ?_⟩
  have hreal : ∑' n : ℤ, (if L ≤ n.natAbs then a j n else 0) < ε := by
    by_cases hj : j < J
    · exact hL j (Finset.mem_range.2 hj)
    · exact lt_of_le_of_lt (tail_anti (a j) (hnn j) (hsum j).summable hLL0)
        (hJ j (not_lt.1 hj))
  have hsm : Summable (fun n : ℤ => if L ≤ n.natAbs then a j n else 0) := by
    convert tail_summable (a j) (hsum j).summable L using 1
    funext n; split_ifs <;> simp [abs_of_nonneg (hnn j n)]
  have hconv : (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal |a j n| else 0) =
      ENNReal.ofReal (∑' n : ℤ, (if L ≤ n.natAbs then a j n else 0)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> simp [hnn j n]) hsm]
    congr 1; funext n; split_ifs <;> simp [abs_of_nonneg (hnn j n)]
  rw [hconv]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hreal

/-- Limit step of the density argument. -/
theorem limit_tsum (a : ℕ → ℤ → ℝ) (b : ℤ → ℝ) (s : ℕ → ℝ) (S : ℝ)
    (hpt : ∀ n : ℤ, Tendsto (fun j => a j n) atTop (𝓝 (b n)))
    (hsum : ∀ j, HasSum (a j) (s j)) (hs : Tendsto s atTop (𝓝 S))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal |a j n| else 0) < ENNReal.ofReal ε) :
    Summable b ∧ ∑' n : ℤ, b n = S := by
  -- finite tail sums of b are bounded by the uniform tail bound
  have hbF : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, (∀ j : ℕ, ∀ F : Finset ℤ,
      ∑ n ∈ F, (if L ≤ n.natAbs then |a j n| else 0) ≤ ε) ∧
      ∀ F : Finset ℤ, ∑ n ∈ F, (if L ≤ n.natAbs then |b n| else 0) ≤ ε := by
    intro ε hε
    obtain ⟨L, hL⟩ := htail ε hε
    refine ⟨L, fun j F => fin_tail _ L ε (hL j) F, fun F => ?_⟩
    have hlim : Tendsto (fun j => ∑ n ∈ F, (if L ≤ n.natAbs then |a j n| else 0)) atTop
        (𝓝 (∑ n ∈ F, (if L ≤ n.natAbs then |b n| else 0))) := by
      refine tendsto_finset_sum _ (fun n _ => ?_)
      split_ifs
      · exact (hpt n).abs
      · exact tendsto_const_nhds
    exact le_of_tendsto' hlim (fun j => fin_tail _ L ε (hL j) F)
  have hbs : Summable b := by
    obtain ⟨L, -, hL⟩ := hbF 1 one_pos
    refine (summable_abs_iff).1 ?_
    refine summable_of_sum_le (c := ∑ n ∈ Finset.Ioo (-(L : ℤ)) L, |b n| + 1)
      (fun n => abs_nonneg _) (fun F => ?_)
    have e : ∑ n ∈ F, |b n| = ∑ n ∈ F, (if L ≤ n.natAbs then 0 else |b n|) +
        ∑ n ∈ F, (if L ≤ n.natAbs then |b n| else 0) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun n _ => ?_)
      split_ifs <;> simp
    rw [e]
    refine add_le_add ?_ (hL F)
    calc ∑ n ∈ F, (if L ≤ n.natAbs then 0 else |b n|)
        = ∑ n ∈ F.filter (fun n => ¬ (L ≤ n.natAbs)), |b n| := by
          rw [Finset.sum_filter]; refine Finset.sum_congr rfl (fun n _ => ?_)
          split_ifs <;> simp_all
      _ ≤ ∑ n ∈ Finset.Ioo (-(L : ℤ)) L, |b n| := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
            (fun n _ _ => abs_nonneg _)
          have := (Finset.mem_filter.1 hn).2
          simp only [Finset.mem_Ioo]; omega
  refine ⟨hbs, ?_⟩
  have hlim : Tendsto s atTop (𝓝 (∑' n : ℤ, b n)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L, hLa, hLb⟩ := hbF (ε / 4) (by positivity)
    have hfin : Tendsto (fun j => ∑ n ∈ Finset.Ioo (-(L : ℤ)) L, a j n) atTop
        (𝓝 (∑ n ∈ Finset.Ioo (-(L : ℤ)) L, b n)) :=
      tendsto_finset_sum _ (fun n _ => hpt n)
    obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.1 hfin) (ε / 4) (by positivity)
    refine ⟨J, fun j hj => ?_⟩
    have hsj : s j = ∑' n : ℤ, a j n := (hsum j).tsum_eq.symm
    rw [Real.dist_eq, hsj, split_tsum _ (hsum j).summable L, split_tsum _ hbs L]
    have t1 := tsum_tail_le _ (hsum j).summable L (ε / 4) (hLa j)
    have t2 := tsum_tail_le _ hbs L (ε / 4) hLb
    have t3 := hJ j hj
    rw [Real.dist_eq] at t3
    rw [abs_lt] at t3
    rw [abs_le] at t1 t2
    rw [abs_lt]
    constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]
  exact tendsto_nhds_unique hlim hs

/-- Uniform tails transfer under a pointwise majorant. -/
theorem tails_of_le (a c : ℕ → ℤ → ℝ) (hle : ∀ j n, |a j n| ≤ c j n)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal (c j n) else 0) < ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℕ, ∀ j : ℕ,
      (∑' n : ℤ, if L ≤ n.natAbs then ENNReal.ofReal |a j n| else 0) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨L, hL⟩ := htail ε hε
  refine ⟨L, fun j => lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) (hL j)⟩
  split_ifs
  · exact ENNReal.ofReal_le_ofReal (hle j n)
  · exact le_rfl

end NlsGge.ThirdConsultation.M018D
