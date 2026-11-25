import NlsGge.GK38.Lib.EntireProductsC34b
import NlsGge.GK38.Lib.WeaklyAnalytic
import NlsGge.GK38.Lib.InverseDistanceConvolution
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! Ordinary inverse-distance series calculus. Uniform convergence uses the
square tail of the fixed kernel, with only a common bound on the varying mass. -/

set_option autoImplicit false
open Set Filter Topology

namespace NlsGge.GK38.Lib
noncomputable section

private theorem squareMajorized_series38
    (f : ℤ → ℂ) (u g : ℤ → ℝ) (C M : ℝ)
    (hu0 : ∀ m, 0 ≤ u m) (hg0 : ∀ m, 0 ≤ g m) (hC : 0 ≤ C)
    (hu : Summable (fun m => u m ^ 2))
    (hg : Summable (fun m => g m ^ 2))
    (hM : (∑' m, u m ^ 2) ≤ M)
    (hf : ∀ m, ‖f m‖ ≤ C * u m * g m) :
    Summable (fun m => ‖f m‖) ∧
      ‖∑' m, f m‖ ≤ C * Real.sqrt M * Real.sqrt (∑' m, g m ^ 2) := by
  obtain ⟨hs, hcs⟩ := cs_tsum hu0 hg0 hu hg
  have hsc : Summable (fun m => C * (u m * g m)) := hs.mul_left C
  have habs : Summable (fun m => ‖f m‖) :=
    hsc.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => by
      simpa only [mul_assoc] using hf m)
  refine ⟨habs, (norm_tsum_le_tsum_norm habs).trans ?_⟩
  calc
    (∑' m, ‖f m‖) ≤ ∑' m, C * (u m * g m) :=
      habs.tsum_le_tsum (fun m => by simpa only [mul_assoc] using hf m) hsc
    _ = C * ∑' m, u m * g m := tsum_mul_left
    _ ≤ C * (Real.sqrt (∑' m, u m ^ 2) * Real.sqrt (∑' m, g m ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs hC
    _ ≤ C * Real.sqrt M * Real.sqrt (∑' m, g m ^ 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hM) (Real.sqrt_nonneg _)) hC

private def kernelTail38 (n : ℤ) (s : Finset ℤ) (m : ℤ) : ℝ :=
  if m ∈ s then 0 else c3w n m

private theorem kernelTail_nonneg38 (n : ℤ) (s : Finset ℤ) (m : ℤ) :
    0 ≤ kernelTail38 n s m := by
  classical
  unfold kernelTail38
  split_ifs <;> first | exact le_rfl | exact c3w_nonneg n m

private theorem kernelTail_summable38 (n : ℤ) (s : Finset ℤ) :
    Summable (fun m => kernelTail38 n s m ^ 2) := by
  classical
  apply (summable_c3w_sq n).of_nonneg_of_le (fun m => sq_nonneg _)
  intro m
  by_cases hm : m ∈ s
  · simpa [kernelTail38, hm] using sq_nonneg (c3w n m)
  · simp [kernelTail38, hm]

private theorem kernelTail_mass38 (n : ℤ) (s : Finset ℤ) :
    (∑' m, kernelTail38 n s m ^ 2) =
      (∑' m, c3w n m ^ 2) - ∑ m ∈ s, c3w n m ^ 2 := by
  classical
  let head : ℤ → ℝ := (s : Set ℤ).indicator (fun m => c3w n m ^ 2)
  have hh : Summable head := (summable_c3w_sq n).indicator (s : Set ℤ)
  have htail := kernelTail_summable38 n s
  have hhead : (∑' m, head m) = ∑ m ∈ s, c3w n m ^ 2 := by
    rw [tsum_eq_sum (s := s) (fun m hm => by simp [head, hm])]
    exact Finset.sum_congr rfl (fun m hm => by simp [head, hm])
  have he : (∑' m, head m) + (∑' m, kernelTail38 n s m ^ 2) =
      ∑' m, c3w n m ^ 2 := by
    rw [← hh.tsum_add htail]
    apply tsum_congr
    intro m
    by_cases hm : m ∈ s <;> simp [head, kernelTail38, hm]
  rw [hhead] at he
  linarith

private theorem kernelTail_mass_tendsto38 (n : ℤ) :
    Tendsto (fun s : Finset ℤ => ∑' m, kernelTail38 n s m ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  have hs : Tendsto (fun s : Finset ℤ => ∑ m ∈ s, c3w n m ^ 2)
      atTop (𝓝 (∑' m, c3w n m ^ 2)) := (summable_c3w_sq n).hasSum
  have hc : Tendsto (fun _ : Finset ℤ => ∑' m, c3w n m ^ 2)
      atTop (𝓝 (∑' m, c3w n m ^ 2)) := tendsto_const_nhds
  have h := hc.sub hs
  simp only [sub_self] at h
  exact h.congr' (Eventually.of_forall (fun s => (kernelTail_mass38 n s).symm))

private theorem finiteHead_series_split38 (f : ℤ → ℂ)
    (hf : Summable (fun m => ‖f m‖)) (s : Finset ℤ) :
    (∑' m, f m) = (∑ m ∈ s, f m) +
      ∑' m, (if m ∈ s then 0 else f m) := by
  classical
  let head : ℤ → ℂ := (s : Set ℤ).indicator f
  have hh : Summable head := hf.of_norm.indicator (s : Set ℤ)
  have ht : Summable (fun m => if m ∈ s then (0 : ℂ) else f m) := by
    apply Summable.of_norm
    apply hf.of_nonneg_of_le (fun m => norm_nonneg _)
    intro m
    by_cases hm : m ∈ s <;> simp [hm]
  have hhead : (∑' m, head m) = ∑ m ∈ s, f m := by
    rw [tsum_eq_sum (s := s) (fun m hm => by simp [head, hm])]
    exact Finset.sum_congr rfl (fun m hm => by simp [head, hm])
  rw [← hhead, ← hh.tsum_add ht]
  apply tsum_congr
  intro m
  by_cases hm : m ∈ s <;> simp [head, hm]

private theorem inverseDistance_uniform38
    {E : Type*} (V : Set E) (f : ℤ → E → ℂ) (a : E → ℤ → ℂ)
    (n : ℤ) (C M : ℝ) (hC : 0 ≤ C)
    (hmass : ∀ y ∈ V, Summable (fun m : ℤ => ‖a y m‖ ^ 2) ∧
      (∑' m : ℤ, ‖a y m‖ ^ 2) ≤ M)
    (hbound : ∀ y ∈ V, ∀ m, ‖f m y‖ ≤ C * ‖a y m‖ * c3w n m) :
    HasSumUniformlyOn f (fun y => ∑' m, f m y) V := by
  classical
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  have herr : Tendsto
      (fun s : Finset ℤ => C * Real.sqrt M *
        Real.sqrt (∑' m, kernelTail38 n s m ^ 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (kernelTail_mass_tendsto38 n)).const_mul (C * Real.sqrt M)
  refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
  filter_upwards [herr.eventually (gt_mem_nhds hε)] with s hs y hy
  have hrow := squareMajorized_series38 (fun m => f m y) (fun m => ‖a y m‖)
    (c3w n) C M (fun m => norm_nonneg _) (c3w_nonneg n) hC
    (hmass y hy).1 (summable_c3w_sq n) (hmass y hy).2 (hbound y hy)
  have htail := squareMajorized_series38
    (fun m => if m ∈ s then 0 else f m y) (fun m => ‖a y m‖)
    (kernelTail38 n s) C M (fun m => norm_nonneg _) (kernelTail_nonneg38 n s)
    hC (hmass y hy).1 (kernelTail_summable38 n s) (hmass y hy).2 (by
      intro m
      by_cases hm : m ∈ s
      · simp [kernelTail38, hm]
      · simpa [kernelTail38, hm] using hbound y hy m)
  rw [dist_eq_norm, finiteHead_series_split38 (fun m => f m y) hrow.1 s,
    add_sub_cancel_left]
  exact htail.2.trans_lt hs

theorem inverseDistance_analytic_series38
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W : Set E) (hW : IsOpen W)
    (b : ℤ → ℤ → E → ℂ) (a : E → ℤ → ℂ)
    (hb : ∀ n m : ℤ, AnalyticOnNhd ℂ (b n m) W)
    (hlocal : ∀ x ∈ W, ∃ V : Set E, ∃ C M : ℝ,
      IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ 0 ≤ C ∧ 0 ≤ M ∧
      (∀ y ∈ V,
        Summable (fun m : ℤ => ‖a y m‖ ^ 2) ∧
        (∑' m : ℤ, ‖a y m‖ ^ 2) ≤ M) ∧
      (∀ y ∈ V, ∀ n m : ℤ,
        ‖b n m y‖ ≤ C * ‖a y m‖ * c3w n m)) :
    (∀ n : ℤ, ∀ x ∈ W,
      Summable (fun m : ℤ => ‖b n m x‖)) ∧
    (∀ n : ℤ, HasSumLocallyUniformlyOn (fun m : ℤ => b n m)
      (fun x : E => ∑' m : ℤ, b n m x) W) ∧
    (∀ n : ℤ, AnalyticOnNhd ℂ
      (fun x : E => ∑' m : ℤ, b n m x) W) ∧
    (∀ x ∈ W, Tendsto (fun n : ℤ => ∑' m : ℤ, b n m x)
      cofinite (𝓝 (0 : ℂ))) := by
  classical
  have hsum : ∀ n : ℤ, ∀ x ∈ W,
      Summable (fun m : ℤ => ‖b n m x‖) := by
    intro n x hx
    obtain ⟨V, C, M, hV, hxV, hVW, hC, hM, hmass, hbound⟩ := hlocal x hx
    exact (squareMajorized_series38 (fun m => b n m x) (fun m => ‖a x m‖)
      (c3w n) C M (fun m => norm_nonneg _) (c3w_nonneg n) hC
      (hmass x hxV).1 (summable_c3w_sq n) (hmass x hxV).2
      (hbound x hxV n)).1
  have hunif : ∀ n : ℤ, HasSumLocallyUniformlyOn (fun m : ℤ => b n m)
      (fun x : E => ∑' m : ℤ, b n m x) W := by
    intro n
    apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
    intro x hx
    obtain ⟨V, C, M, hV, hxV, hVW, hC, hM, hmass, hbound⟩ := hlocal x hx
    exact ⟨V, nhdsWithin_le_nhds (hV.mem_nhds hxV),
      inverseDistance_uniform38 V (b n) a n C M hC hmass
        (fun y hy => hbound y hy n)⟩
  refine ⟨hsum, hunif, ?_, ?_⟩
  · intro n
    apply analyticOnNhd_of_weak_of_locBdd hW
    · intro x hx h ℓ
      let line : ℂ → E := fun ζ => x + ζ • h
      have hline : Continuous line := by fun_prop
      have hU : IsOpen (line ⁻¹' W) := hW.preimage hline
      have hzero : (0 : ℂ) ∈ line ⁻¹' W := by simpa [line] using hx
      have hseries : SummableLocallyUniformlyOn
          (fun m ζ => b n m (line ζ)) (line ⁻¹' W) :=
        ((hunif n).comp line (fun ζ hζ => hζ) hline.continuousOn).summableLocallyUniformlyOn
      have hdiff : DifferentiableOn ℂ (fun ζ => ∑' m, b n m (line ζ))
          (line ⁻¹' W) := hseries.differentiableOn hU (by
        intro m ζ hζ
        exact ((hb n m (line ζ) hζ).differentiableAt).comp ζ (by
          dsimp [line]
          fun_prop))
      exact (ℓ.analyticAt _).comp (hdiff.analyticAt (hU.mem_nhds hzero))
    · intro x hx
      obtain ⟨V, C, M, hV, hxV, hVW, hC, hM, hmass, hbound⟩ := hlocal x hx
      obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV x hxV
      refine ⟨r, hr, C * Real.sqrt M * Real.sqrt invSqSum, ?_⟩
      intro y hy
      have h := (squareMajorized_series38 (fun m => b n m y) (fun m => ‖a y m‖)
        (c3w n) C M (fun m => norm_nonneg _) (c3w_nonneg n) hC
        (hmass y (hrV hy)).1 (summable_c3w_sq n) (hmass y (hrV hy)).2
        (hbound y (hrV hy) n)).2
      simpa only [tsum_c3w_sq] using h
  · intro x hx
    obtain ⟨V, C, M, hV, hxV, hVW, hC, hM, hmass, hbound⟩ := hlocal x hx
    have hconv := (inverseDistance_convolution_tendsto_zero38 (a x)
      (hmass x hxV).1).const_mul C
    have hmajor : ∀ n : ℤ, ‖∑' m : ℤ, b n m x‖ ≤
        C * ∑' m : ℤ, ‖a x m‖ * c3w n m := by
      intro n
      have hmaj : Summable (fun m => C * (‖a x m‖ * c3w n m)) :=
        (c3_cs (hmass x hxV).1 n).1.mul_left C
      calc
        ‖∑' m : ℤ, b n m x‖ ≤ ∑' m : ℤ, ‖b n m x‖ :=
          norm_tsum_le_tsum_norm (hsum n x hx)
        _ ≤ ∑' m : ℤ, C * (‖a x m‖ * c3w n m) :=
          (hsum n x hx).tsum_le_tsum
            (fun m => by simpa only [mul_assoc] using hbound x hxV n m) hmaj
        _ = C * ∑' m : ℤ, ‖a x m‖ * c3w n m := tsum_mul_left
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hev := hconv.eventually (gt_mem_nhds (by simpa using hε))
    filter_upwards [hev] with n hn
    rw [dist_zero_right]
    exact (hmajor n).trans_lt hn

end
end NlsGge.GK38.Lib
