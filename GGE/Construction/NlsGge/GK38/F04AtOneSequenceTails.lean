import NlsGge.GK38.F04AtOneSequenceActions
import NlsGge.Spectral.ActualGapLocalizationAllUE02_38

/-! Unweighted action tails from L1 convergence, and the common H1 remainder bound. -/
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology
open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.Sobolev38
namespace NlsGge.GK38
noncomputable section

theorem summable_lattice_tails_small38 (f : ℤ → ℝ) (hf : Summable f) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, tailSum38 f N ≤ ε := by
  have ht : Tendsto (tailSum38 f) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (bound := fun n => |f n|) hf.abs
      (f := fun N : ℕ => fun n : ℤ => if (N : ℤ) < |n| then |f n| else 0)
      (g := fun _ => 0) ?_ ?_
    · change Tendsto (fun N : ℕ => ∑' n : ℤ, if (N : ℤ) < |n| then |f n| else 0) atTop (𝓝 0)
      simpa only [tsum_zero] using h
    · intro n
      apply tendsto_const_nhds.congr'
      apply eventually_atTop.mpr
      refine ⟨n.natAbs, fun N hN => ?_⟩
      have hn : |n| ≤ (N : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hN
      simp [not_lt.mpr hn]
    · apply Eventually.of_forall
      intro N n
      split_ifs <;> simp
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨N, hN.le⟩

theorem lattice_tail_le_l1_add38 (f g : ℤ → ℝ) (hf : Summable f) (hg : Summable g) (N : ℕ) :
    tailSum38 f N ≤ (∑' n : ℤ, |f n - g n|) + tailSum38 g N := by
  have hd : Summable (fun n => |f n - g n|) := (hf.sub hg).abs
  have ht := tailSum38_summable g hg N
  calc
    _ ≤ ∑' n : ℤ, (|f n - g n| + (if (N : ℤ) < |n| then |g n| else 0)) := by
      apply Summable.tsum_le_tsum _ (tailSum38_summable f hf N) (hd.add ht)
      intro n
      by_cases hn : (N : ℤ) < |n|
      · simp only [hn, ite_true]
        calc |f n| = |(f n - g n) + g n| := by rw [sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      · simp only [hn, ite_false, add_zero]
        exact abs_nonneg _
    _ = _ := hd.tsum_add ht

theorem actionTails_L2_uniform38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hH : ∀ k, SobolevSquareSummable 1 (physicalFourier (u k)))
    (hH₀ : SobolevSquareSummable 1 (physicalFourier u₀))
    (hL2 : Tendsto u atTop (𝓝 u₀)) :
    ∀ ε > 0, ∃ N : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      tailSum38 (actualGapActionAllE02_38 (u k)) N ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := summable_lattice_tails_small38 (actualGapActionAllE02_38 u₀)
    (actualGapAction_hasSum_E02_38 u₀ hH₀).summable (ε / 2) (by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp
    ((action_l1_tendsto38 u u₀ hH hH₀ hL2).eventually (gt_mem_nhds (by positivity : 0 < ε / 2)))
  refine ⟨N, k₀, fun k hk => ?_⟩
  have hle := lattice_tail_le_l1_add38 (actualGapActionAllE02_38 (u k)) (actualGapActionAllE02_38 u₀)
    (actualGapAction_hasSum_E02_38 (u k) (hH k)).summable
    (actualGapAction_hasSum_E02_38 u₀ hH₀).summable N
  linarith [hk₀ k hk]

theorem remainder_one_sequence_bound38 (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1)
    (u : ℕ → PhysicalL2) (hH : ∀ k, SobolevSquareSummable 1 (physicalFourier (u k)))
    (hb : ∃ B : ℝ, ∀ k, ‖physicalSobolevL2 1 (u k) (hH k)‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ∀ n : ℤ,
      |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (u k) n| ≤
        C * actualGapActionAllE02_38 (u k) n := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨C, hC, hbound⟩ := gapRemainderTerm_le_action_one β hβ (max 1 B) (le_max_left _ _)
  refine ⟨C, hC, fun k n => ?_⟩
  obtain ⟨w, hw, hn⟩ := physicalH1Carrier_surjective_E02_38 (u k) (hH k)
  have hnorm : ‖w‖ ≤ max 1 B := hn ▸ (hB k).trans (le_max_right _ _)
  simpa only [hw] using hbound w hnorm n

theorem remainder_one_sequence_summable38 (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1)
    (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Summable (fun n : ℤ => |gapRemainderTermE02_38 (finiteWeightE02_38 1 β) u n|) :=
  (spectralRemainder_one_nonneg_summable β hβ u hu).1

theorem remainderTails_L2_uniform_one38 (β : ℕ → ℝ) (hβ : 0 < β 0 ∧ 0 < β 1)
    (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hH : ∀ k, SobolevSquareSummable 1 (physicalFourier (u k)))
    (hH₀ : SobolevSquareSummable 1 (physicalFourier u₀))
    (hb : ∃ B : ℝ, ∀ k, ‖physicalSobolevL2 1 (u k) (hH k)‖ ≤ B)
    (hL2 : Tendsto u atTop (𝓝 u₀)) :
    ∀ ε > 0, ∃ N : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      tailSum38 (fun n => gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (u k) n) N ≤ ε := by
  obtain ⟨C, hC, hbC⟩ := remainder_one_sequence_bound38 β hβ u hH hb
  intro ε hε
  obtain ⟨N, k₀, hN⟩ := actionTails_L2_uniform38 u u₀ hH hH₀ hL2
    (ε / (C + 1)) (by positivity)
  refine ⟨N, k₀, fun k hk => ?_⟩
  have hs := tailSum38_summable (actualGapActionAllE02_38 (u k))
    (actualGapAction_hasSum_E02_38 (u k) (hH k)).summable N
  have hr := tailSum38_summable (fun n => gapRemainderTermE02_38 (finiteWeightE02_38 1 β) (u k) n)
    (remainder_one_sequence_summable38 β hβ (u k) (hH k)).of_abs N
  calc
    _ ≤ ∑' n : ℤ, C * (if (N : ℤ) < |n| then |actualGapActionAllE02_38 (u k) n| else 0) := by
      apply Summable.tsum_le_tsum _ hr (hs.mul_left C)
      intro n
      split_ifs
      · rw [abs_of_nonneg (actualGapAction_nonneg_F04_38 (u k) n)]
        exact hbC k n
      · simp
    _ = C * tailSum38 (actualGapActionAllE02_38 (u k)) N := tsum_mul_left
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (hN k hk) hC
    _ ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith

end
end NlsGge.GK38
