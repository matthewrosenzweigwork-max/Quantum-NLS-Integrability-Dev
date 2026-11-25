import Armstrong.Work.RawBetaNormSq
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.GK38

private theorem rawBetaContinuousWithinAtOfSquareZero38
    (g s : ℝ → ℂ) (D : Set ℝ) (a : ℝ)
    (hgc : ContinuousWithinAt g D a)
    (hsquare : ∀ t ∈ D, s t ^ 2 = g t)
    (ha : a ∈ D) (hzero : g a = 0) :
    ContinuousWithinAt s D a := by
  have hs0 : s a = 0 := by
    have h := hsquare a ha
    simpa only [hzero, sq_eq_zero_iff] using h
  have hnorm : ContinuousWithinAt (fun t => ‖s t‖ ^ 2) D a := by
    apply hgc.norm.congr
    · intro t ht
      rw [← norm_pow, hsquare t ht]
    · rw [← norm_pow, hsquare a ha]
  have hlim : Tendsto s (𝓝[D] a) (𝓝 (0 : ℂ)) := by
    apply rawBetaTendstoZeroOfNormSq38
    simpa only [hs0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using hnorm.tendsto
  simpa only [ContinuousWithinAt, hs0] using hlim

private theorem rawBetaContinuousSquareRootExists38
    (g : ℝ → ℂ)
    (hgc : ContinuousOn g (Icc (0 : ℝ) 1))
    (hzero : g 0 = 0)
    (hnonzero : ∀ t ∈ Ioo (0 : ℝ) 1, g t ≠ 0) :
    ∃ s : ℝ → ℂ, ContinuousOn s (Icc (0 : ℝ) 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, s t ^ 2 = g t := by
  by_cases hone : g 1 = 0
  · let : ContractibleSpace (Ioo (0 : ℝ) 1) :=
      (convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace
        ⟨1 / 2, by norm_num⟩
    have hsimple : IsSimplyConnected (Ioo (0 : ℝ) 1) := by
      change SimplyConnectedSpace (Ioo (0 : ℝ) 1)
      infer_instance
    have hnozero : 0 ∉ g '' Ioo (0 : ℝ) 1 := by
      rintro ⟨t, ht, heq⟩
      exact hnonzero t ht heq
    obtain ⟨s, hscont, hsquare⟩ :=
      Complex.exists_continuousOn_pow_eq hsimple isOpen_Ioo
        (hgc.mono Ioo_subset_Icc_self) hnozero (n := 2) (by norm_num)
    refine ⟨s, ?_, fun t _ => hsquare t⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact rawBetaContinuousWithinAtOfSquareZero38 g s (Icc (0 : ℝ) 1) 0
        (hgc 0 ht) (fun t _ => hsquare t) ht hzero
    by_cases ht1 : t = 1
    · subst t
      exact rawBetaContinuousWithinAtOfSquareZero38 g s (Icc (0 : ℝ) 1) 1
        (hgc 1 ht) (fun t _ => hsquare t) ht hone
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact (hscont.continuousAt (isOpen_Ioo.mem_nhds hti)).continuousWithinAt
  · let g' : ℝ → ℂ := fun t => g (min t 1)
    have hmin : MapsTo (fun t : ℝ => min t 1) (Ioi (0 : ℝ)) (Icc (0 : ℝ) 1) := by
      intro t ht
      exact ⟨le_min (le_of_lt ht) (by norm_num), min_le_right _ _⟩
    have hgc' : ContinuousOn g' (Ioi (0 : ℝ)) := by
      exact hgc.comp' (continuous_id.min continuous_const).continuousOn hmin
    have hnozero : 0 ∉ g' '' Ioi (0 : ℝ) := by
      rintro ⟨t, ht, heq⟩
      by_cases ht1 : t < 1
      · apply hnonzero t ⟨ht, ht1⟩
        simpa only [g', min_eq_left ht1.le] using heq
      · apply hone
        simpa only [g', min_eq_right (le_of_not_gt ht1)] using heq
    let : ContractibleSpace (Ioi (0 : ℝ)) :=
      (convex_Ioi (𝕜 := ℝ) (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
    have hsimple : IsSimplyConnected (Ioi (0 : ℝ)) := by
      change SimplyConnectedSpace (Ioi (0 : ℝ))
      infer_instance
    obtain ⟨s, hscont, hsquare⟩ :=
      Complex.exists_continuousOn_pow_eq hsimple isOpen_Ioi hgc' hnozero
        (n := 2) (by norm_num)
    have hsquare' : ∀ t ∈ Icc (0 : ℝ) 1, s t ^ 2 = g t := by
      intro t ht
      simpa only [g', min_eq_left ht.2] using hsquare t
    refine ⟨s, ?_, hsquare'⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact rawBetaContinuousWithinAtOfSquareZero38 g s (Icc (0 : ℝ) 1) 0
        (hgc 0 ht) hsquare' ht hzero
    exact (hscont.continuousAt
      (isOpen_Ioi.mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm ht0)))).continuousWithinAt

/-- A continuous complex function on the closed unit interval, nonzero on the
open interval and zero at the initial endpoint, has a continuous square root
with any prescribed terminal square-root value. -/
theorem rawBetaContinuousSquareRootWithTerminal38
    (g : ℝ → ℂ)
    (hgc : ContinuousOn g (Icc (0 : ℝ) 1))
    (hzero : g 0 = 0)
    (hnonzero : ∀ t ∈ Ioo (0 : ℝ) 1, g t ≠ 0)
    (δ : ℂ) (hδ : δ ^ 2 = g 1) :
    ∃ s : ℝ → ℂ, ContinuousOn s (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, s t ^ 2 = g t) ∧ s 1 = δ := by
  obtain ⟨s, hscont, hsquare⟩ :=
    rawBetaContinuousSquareRootExists38 g hgc hzero hnonzero
  have heq : s 1 ^ 2 = δ ^ 2 := (hsquare 1 (by norm_num)).trans hδ.symm
  have hprod : (s 1 - δ) * (s 1 + δ) = 0 := by
    calc
      (s 1 - δ) * (s 1 + δ) = s 1 ^ 2 - δ ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp hprod with hminus | hplus
  · exact ⟨s, hscont, hsquare, sub_eq_zero.mp hminus⟩
  · refine ⟨fun t => -s t, hscont.neg, ?_, ?_⟩
    · intro t ht
      simpa only [neg_sq] using hsquare t ht
    · calc
        -s 1 = -s 1 + (s 1 + δ) := by rw [hplus, add_zero]
        _ = δ := by ring

end NlsGge.GK38

