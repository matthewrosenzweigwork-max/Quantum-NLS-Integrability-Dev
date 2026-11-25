import Armstrong.Work.RawBetaSpectralInput
import Armstrong.Frozen.RawBeta.GKPathCompactIntegrable38
import NlsGge.GK38.AbelianPsiNumerator
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Compact integrability on the literal rooted path carrier.

The within-derivative of each C1 arc is continuous on the closed unit
interval. We replace it by the ordinary derivative only on the open
integration interval, using null-endpoint invariance of interval integrability.
The original source endpoints remain excluded by the prescribed truncations.
-/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory intervalIntegral

namespace NlsGge.GK38
noncomputable section

private theorem rawBetaArcCompactIntegrable38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (a : GKRootedC1Arc38 φ m)
    (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ 1) (huv : u ≤ v)
    (hslit : ∀ t ∈ Icc u v, GKArcCurve38 a t ∈ GKOriginalSlit38 φ m) :
    IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume u v := by
  have hsub : Icc u v ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hu hv
  have hcurve : ContinuousOn (GKArcCurve38 a) (Icc (0 : ℝ) 1) := a.2.1
  have hC1 : ContDiffOn ℝ 1 (GKArcCurve38 a) (Icc (0 : ℝ) 1) := a.2.2.1
  have hsheet : ContinuousOn (GKArcSheet38 a) (Icc (0 : ℝ) 1) := a.2.2.2.1
  have hsquare : ∀ t ∈ Icc (0 : ℝ) 1,
      GKArcSheet38 a t ^ 2 = perChar φ.1 (GKArcCurve38 a t) := a.2.2.2.2.1
  have hnonzero : ∀ t ∈ Icc u v, GKArcSheet38 a t ≠ 0 := by
    intro t ht hzero
    apply rawBetaPerCharNonzeroOnSlit38 φ m (GKArcCurve38 a t) (hslit t ht)
    rw [← hsquare t (hsub ht), hzero]
    norm_num
  have hnumerator : Continuous (p6PsiNumerator38 n (F n) φ.1) :=
    continuousOn_univ.mp (p6PsiNumerator_entire38 n (F n) φ.1).continuousOn
  have hquotient : ContinuousOn
      (fun t => p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
        GKArcSheet38 a t) (Icc u v) :=
    ((hnumerator.comp_continuousOn hcurve).mono hsub).div₀
      (hsheet.mono hsub) hnonzero
  have hderivative : ContinuousOn
      (derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    hC1.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one (by norm_num)
  have hcontinuous : ContinuousOn
      (fun t => (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
        GKArcSheet38 a t) *
        derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1) t) (Icc u v) :=
    hquotient.mul (hderivative.mono hsub)
  have hintegrable : IntervalIntegrable
      (fun t => (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
        GKArcSheet38 a t) *
        derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1) t) volume u v :=
    hcontinuous.intervalIntegrable_of_Icc huv
  apply hintegrable.congr_uIoo
  intro t ht
  have hti : t ∈ Ioo u v := by simpa only [uIoo_of_le huv] using ht
  have ht0 : 0 < t := lt_of_le_of_lt hu hti.1
  have ht1 : t < 1 := lt_of_lt_of_le hti.2 hv
  change (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
      GKArcSheet38 a t) * derivWithin (GKArcCurve38 a) (Icc (0 : ℝ) 1) t =
    (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) /
      GKArcSheet38 a t) * deriv (GKArcCurve38 a) t
  exact congrArg (fun d : ℂ =>
    (p6PsiNumerator38 n (F n) φ.1 (GKArcCurve38 a t) / GKArcSheet38 a t) * d)
    (derivWithin_of_mem_nhds (f := GKArcCurve38 a) (Icc_mem_nhds ht0 ht1))

private theorem rawBetaChainSlitEndpoints38
    (φ : GKPotential38) (m : ℤ)
    (first last : GKRootedC1Arc38 φ m)
    (middle : List (GKRootedC1Arc38 φ m))
    (hchain : GKRootedArcChain38 φ m (first :: (middle ++ [last]))) :
    GKArcCurve38 first 1 ∈ GKOriginalSlit38 φ m ∧
    (∀ a ∈ middle,
      GKArcCurve38 a 0 ∈ GKOriginalSlit38 φ m ∧
      GKArcCurve38 a 1 ∈ GKOriginalSlit38 φ m) ∧
    GKArcCurve38 last 0 ∈ GKOriginalSlit38 φ m := by
  induction middle generalizing first with
  | nil =>
      change GKRootedArcJoin38 φ m first last ∧
        GKRootedArcChain38 φ m [last] at hchain
      have hjoin := hchain.1
      refine ⟨hjoin.2.2, ?_, ?_⟩
      · intro a ha
        simp at ha
      · simpa only [hjoin.1] using hjoin.2.2
  | cons a tail ih =>
      change GKRootedArcJoin38 φ m first a ∧
        GKRootedArcChain38 φ m (a :: (tail ++ [last])) at hchain
      have hjoin := hchain.1
      obtain ⟨ha1, htail, hlast0⟩ := ih a hchain.2
      refine ⟨hjoin.2.2, ?_, hlast0⟩
      intro b hb
      rcases List.mem_cons.mp hb with hba | hb
      · subst b
        refine ⟨?_, ha1⟩
        simpa only [hjoin.1] using hjoin.2.2
      · exact htail b hb

/-- Every permitted rooted path has the compact integrability required by the
frozen source definition, with its exact first/middle/last truncation ranges. -/
theorem rawBetaPathCompactIntegrable38
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (p : GKRootedPiecewisePath38 φ m) :
    GKPathCompactIntegrable38 n m F φ p := by
  have hchain : GKRootedArcChain38 φ m
      (GKPathFirst38 p :: (GKPathMiddle38 p ++ [GKPathLast38 p])) := p.2.2.1
  obtain ⟨hfirstEnd, hmiddleEnds, hlastStart⟩ :=
    rawBetaChainSlitEndpoints38 φ m (GKPathFirst38 p) (GKPathLast38 p)
      (GKPathMiddle38 p) hchain
  unfold GKPathCompactIntegrable38
  intro ε η hε hη hsum
  have hε1 : ε < 1 := by linarith
  have hη1 : η < 1 := by linarith
  have hlastpos : 0 < 1 - η := by linarith
  have hlastlt : 1 - η < 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · apply rawBetaArcCompactIntegrable38 n m F φ (GKPathFirst38 p)
      ε 1 hε.le le_rfl hε1.le
    intro t ht
    by_cases ht1 : t = 1
    · subst t
      exact hfirstEnd
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le hε ht.1, lt_of_le_of_ne ht.2 ht1⟩
    exact (GKPathFirst38 p).2.2.2.2.2.2 t hti
  · intro a ha
    apply rawBetaArcCompactIntegrable38 n m F φ a
      0 1 le_rfl le_rfl zero_le_one
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact (hmiddleEnds a ha).1
    by_cases ht1 : t = 1
    · subst t
      exact (hmiddleEnds a ha).2
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact a.2.2.2.2.2.2 t hti
  · apply rawBetaArcCompactIntegrable38 n m F φ (GKPathLast38 p)
      0 (1 - η) le_rfl hlastlt.le hlastpos.le
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact hlastStart
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_lt ht.2 hlastlt⟩
    exact (GKPathLast38 p).2.2.2.2.2.2 t hti

end
end NlsGge.GK38
