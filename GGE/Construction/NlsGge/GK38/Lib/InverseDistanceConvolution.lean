import NlsGge.GK38.Lib.EntireProductsC34b

/-! Ordinary inverse-distance convolution decay. This module has no spectral
family, beta-value, or Birkhoff-map premise or conclusion. -/

set_option autoImplicit false
open Set Filter Topology

namespace NlsGge.GK38.Lib
noncomputable section

private def inverseDistanceTail38 (a : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) : ℂ :=
  if m ∈ s then 0 else a m

private theorem inverseDistanceTail_sq_summable38 (a : ℤ → ℂ)
    (ha : Summable (fun m : ℤ => ‖a m‖ ^ 2)) (s : Finset ℤ) :
    Summable (fun m : ℤ => ‖inverseDistanceTail38 a s m‖ ^ 2) := by
  apply ha.of_nonneg_of_le (fun m => sq_nonneg _)
  intro m
  by_cases hm : m ∈ s <;> simp [inverseDistanceTail38, hm]

private theorem inverseDistanceTail_sq_sum38 (a : ℤ → ℂ)
    (ha : Summable (fun m : ℤ => ‖a m‖ ^ 2)) (s : Finset ℤ) :
    (∑' m : ℤ, ‖inverseDistanceTail38 a s m‖ ^ 2) =
      (∑' m : ℤ, ‖a m‖ ^ 2) - ∑ m ∈ s, ‖a m‖ ^ 2 := by
  classical
  let h : ℤ → ℝ := (s : Set ℤ).indicator (fun m => ‖a m‖ ^ 2)
  have hh : Summable h := ha.indicator (s : Set ℤ)
  have ht := inverseDistanceTail_sq_summable38 a ha s
  have hhs : (∑' m : ℤ, h m) = ∑ m ∈ s, ‖a m‖ ^ 2 := by
    rw [tsum_eq_sum (s := s) (fun m hm => by simp [h, hm])]
    exact Finset.sum_congr rfl (fun m hm => by simp [h, hm])
  have he : (∑' m : ℤ, h m) +
      (∑' m : ℤ, ‖inverseDistanceTail38 a s m‖ ^ 2) =
      ∑' m : ℤ, ‖a m‖ ^ 2 := by
    rw [← hh.tsum_add ht]
    apply tsum_congr
    intro m
    by_cases hm : m ∈ s <;> simp [h, inverseDistanceTail38, hm]
  rw [hhs] at he
  linarith

private theorem inverseDistance_kernel_tendsto_zero38 (m : ℤ) :
    Tendsto (fun n : ℤ => c3w n m) cofinite (𝓝 (0 : ℝ)) := by
  have hs := (summable_c3w_sq m).tendsto_cofinite_zero
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  convert h using 1
  · funext n
    change c3w n m = Real.sqrt (c3w m n ^ 2)
    rw [Real.sqrt_sq (c3w_nonneg m n)]
    unfold c3w
    rw [abs_sub_comm]
  · simp

private theorem inverseDistance_head_tendsto_zero38 (a : ℤ → ℂ)
    (s : Finset ℤ) :
    Tendsto (fun n : ℤ => ∑ m ∈ s, ‖a m‖ * c3w n m)
      cofinite (𝓝 (0 : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (tendsto_const_nhds : Tendsto (fun _ : ℤ => (0 : ℝ)) cofinite (𝓝 0))
  | @insert m s hm ih =>
      have h := ((inverseDistance_kernel_tendsto_zero38 m).const_mul ‖a m‖).add ih
      simpa only [Finset.sum_insert hm, mul_zero, zero_add] using h

private theorem inverseDistance_sum_split38 (a : ℤ → ℂ)
    (ha : Summable (fun m : ℤ => ‖a m‖ ^ 2)) (s : Finset ℤ) (n : ℤ) :
    (∑' m : ℤ, ‖a m‖ * c3w n m) =
      (∑ m ∈ s, ‖a m‖ * c3w n m) +
      ∑' m : ℤ, ‖inverseDistanceTail38 a s m‖ * c3w n m := by
  classical
  let h : ℤ → ℝ := (s : Set ℤ).indicator (fun m => ‖a m‖ * c3w n m)
  have hh : Summable h := (c3_cs ha n).1.indicator (s : Set ℤ)
  have ht := (c3_cs (inverseDistanceTail_sq_summable38 a ha s) n).1
  have hhs : (∑' m : ℤ, h m) = ∑ m ∈ s, ‖a m‖ * c3w n m := by
    rw [tsum_eq_sum (s := s) (fun m hm => by simp [h, hm])]
    exact Finset.sum_congr rfl (fun m hm => by simp [h, hm])
  rw [← hhs, ← hh.tsum_add ht]
  apply tsum_congr
  intro m
  by_cases hm : m ∈ s <;> simp [h, inverseDistanceTail38, hm]

theorem inverseDistance_convolution_tendsto_zero38
    (a : ℤ → ℂ)
    (ha : Summable (fun m : ℤ => ‖a m‖ ^ 2)) :
    Tendsto (fun n : ℤ => ∑' m : ℤ, ‖a m‖ * c3w n m)
      cofinite (𝓝 (0 : ℝ)) := by
  classical
  have hmass : Tendsto
      (fun s : Finset ℤ => ∑' m : ℤ, ‖inverseDistanceTail38 a s m‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have hs : Tendsto (fun s : Finset ℤ => ∑ m ∈ s, ‖a m‖ ^ 2)
        atTop (𝓝 (∑' m : ℤ, ‖a m‖ ^ 2)) := ha.hasSum
    have hc : Tendsto
        (fun _ : Finset ℤ => ∑' m : ℤ, ‖a m‖ ^ 2)
        atTop (𝓝 (∑' m : ℤ, ‖a m‖ ^ 2)) := tendsto_const_nhds
    have h := hc.sub hs
    simp only [sub_self] at h
    exact h.congr' (Eventually.of_forall
      (fun s => (inverseDistanceTail_sq_sum38 a ha s).symm))
  have herr : Tendsto
      (fun s : Finset ℤ =>
        Real.sqrt (∑' m : ℤ, ‖inverseDistanceTail38 a s m‖ ^ 2) *
          Real.sqrt invSqSum) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, zero_mul] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hmass).mul_const
        (Real.sqrt invSqSum)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := (herr.eventually (gt_mem_nhds (half_pos hε))).exists
  have hh := (inverseDistance_head_tendsto_zero38 a s).eventually
    (gt_mem_nhds (half_pos hε))
  filter_upwards [hh] with n hn
  have hnonneg : 0 ≤ ∑' m : ℤ, ‖a m‖ * c3w n m :=
    tsum_nonneg (fun m => mul_nonneg (norm_nonneg _) (c3w_nonneg n m))
  have htail := (c3_cs (inverseDistanceTail_sq_summable38 a ha s) n).2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  rw [inverseDistance_sum_split38 a ha s n]
  linarith

end
end NlsGge.GK38.Lib
