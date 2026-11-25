import NlsGge.GK38.Lib.EntireProductsC34b
import Mathlib.Analysis.Normed.Group.Tannery

/-! UNCOMPILED genuine shifted inverse-square masses. Actual summability
precedes Tannery; the final threshold controls BOTH signs by natAbs. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6c3w_cofinite_zero38 (m : ℤ) :
    Tendsto (fun n : ℤ => Lib.c3w m n) cofinite (𝓝 (0 : ℝ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (|(m : ℝ)|+1/ε)
  apply eventually_cofinite.mpr
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro n hn
  by_contra hnIcc
  have hnAbs : (N : ℤ) < |n| := by
    apply lt_of_not_ge
    intro hle
    exact hnIcc (abs_le.mp hle)
  have hnR : (N : ℝ) < |(n : ℝ)| := by exact_mod_cast hnAbs
  have htri : |(n : ℝ)| ≤ |(n : ℝ)-(m : ℝ)|+|(m : ℝ)| := by
    simpa only [sub_zero] using abs_sub_le (n : ℝ) (m : ℝ) 0
  have hdiff : 1/ε < |(n : ℝ)-(m : ℝ)| := by linarith
  have hpos : 0 < |(n : ℝ)-(m : ℝ)| := (one_div_pos.mpr hε).trans hdiff
  have hsmall : Lib.c3w m n < ε := by
    unfold Lib.c3w
    apply (div_lt_iff₀ hpos).mpr
    have hh := (div_lt_iff₀ hε).mp hdiff
    nlinarith
  apply hn
  simpa only [dist_eq_norm,sub_zero,Real.norm_eq_abs,
    abs_of_nonneg (Lib.c3w_nonneg m n)] using hsmall

theorem p6ShiftedSquareMass_summable38 (E : ℤ → ℝ)
    (hE : Summable (fun m : ℤ => E m^2)) (n : ℤ) :
    Summable (fun m : ℤ => E m^2*Lib.c3w m n^2) := by
  apply hE.of_nonneg_of_le (fun m => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  intro m
  have h0 := Lib.c3w_nonneg m n
  have h1 := Lib.c3w_le_one m n
  have hs : Lib.c3w m n^2 ≤ 1 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg (E m))).trans_eq (mul_one _)

theorem p6ShiftedSquareMass_cofinite_zero38 (E : ℤ → ℝ)
    (hE : Summable (fun m : ℤ => E m^2)) :
    Tendsto (fun n : ℤ => ∑' m : ℤ, E m^2*Lib.c3w m n^2) cofinite (𝓝 (0 : ℝ)) := by
  have _hSummable := p6ShiftedSquareMass_summable38 E hE
  have hbound (n m : ℤ) : ‖E m^2*Lib.c3w m n^2‖ ≤ E m^2 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have h0 := Lib.c3w_nonneg m n
    have h1 := Lib.c3w_le_one m n
    have hs : Lib.c3w m n^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs (sq_nonneg (E m))).trans_eq (mul_one _)
  have hlim (m : ℤ) : Tendsto (fun n : ℤ => E m^2*Lib.c3w m n^2)
      cofinite (𝓝 (0 : ℝ)) := by
    have hc : Tendsto (fun _ : ℤ => E m^2) cofinite (𝓝 (E m^2)) := tendsto_const_nhds
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero] using
      hc.mul ((p6c3w_cofinite_zero38 m).pow 2)
  have ht := tendsto_tsum_of_dominated_convergence hE hlim (Eventually.of_forall hbound)
  simpa only [tsum_zero] using ht

theorem p6ShiftedSquareMass_signed_threshold38 (E : ℤ → ℝ)
    (hE : Summable (fun m : ℤ => E m^2)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs →
      (∑' m : ℤ, E m^2*Lib.c3w m n^2) < ε := by
  have ht := (p6ShiftedSquareMass_cofinite_zero38 E hE).eventually (gt_mem_nhds hε)
  have hbad : {n : ℤ | ¬ (∑' m : ℤ, E m^2*Lib.c3w m n^2) < ε}.Finite :=
    eventually_cofinite.mp ht
  obtain ⟨b,hb⟩ := (hbad.image (fun n : ℤ => |n|)).bddAbove
  refine ⟨b.natAbs+1,?_⟩
  intro n hn
  by_contra hnot
  have hnle : |n| ≤ b := hb ⟨n,hnot,rfl⟩
  have hbabs : b ≤ (b.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self b
  have hnat : n.natAbs ≤ b.natAbs := by
    have hh : (n.natAbs : ℤ) ≤ (b.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact hnle.trans hbabs
    exact_mod_cast hh
  omega

end
end NlsGge.GK38
