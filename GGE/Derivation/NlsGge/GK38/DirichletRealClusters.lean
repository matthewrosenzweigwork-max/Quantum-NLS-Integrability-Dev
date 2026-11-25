import NlsGge.GK38.DirichletRealWindow
import NlsGge.GK38.RealTypeSpectrumProjection

/-! Actual q=1 Dirichlet root clusters, using the accepted local Rouché API.
The q=2 S5 cluster algebra is realized again for the actual Dirichlet characteristic.
Private source anchor: book I.7 Lemma 7.2 deformation route. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_cluster_radius38 (u : PhysicalL2) (N : ℕ)
    (hN : RootCountingAt38 (dirichletChar (realSlice u)) 1 N)
    (a : ℂ) (ha : a ∈ Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ closedBall a r ⊆ ball 0 (countingRadius38 N) ∧
      ∀ z ∈ closedBall a (3 * r), z ≠ a → dirichletChar (realSlice u) z ≠ 0 := by
  have ham := (counting_mem_zeroMultiset38 hN 0 (countingRadius38 N) a).mp ha
  have hain : ‖a‖ < countingRadius38 N := by simpa using ham.1
  have hpunct : ∀ᶠ z in 𝓝[≠] a, dirichletChar (realSlice u) z ≠ 0 := by
    rcases (hN.2.1 a (mem_univ a)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exact False.elim ((counting_order_ne_top38 hN a) (analyticOrderAt_eq_top.mpr hzero))
    · exact hne
  rw [eventually_nhdsWithin_iff] at hpunct
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.mp hpunct
  let δ := min ε (min s (countingRadius38 N - ‖a‖))
  have hδ : 0 < δ := lt_min hε (lt_min hs (sub_pos.mpr hain))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδs : δ ≤ s := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ countingRadius38 N - ‖a‖ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ / 4, by positivity, by linarith, ?_, ?_⟩
  · intro z hz
    have hza : ‖z - a‖ ≤ δ / 4 := mem_closedBall_iff_norm.mp hz
    have ht : ‖z‖ ≤ ‖z - a‖ + ‖a‖ := by
      have hh := norm_add_le (z - a) a
      simpa using hh
    rw [mem_ball_zero_iff]
    linarith
  · intro z hz hne
    apply hball
    · have hza : dist z a ≤ 3 * (δ / 4) := hz
      linarith
    · simpa using hne

theorem dirichlet_cluster_reference_card38 (u : PhysicalL2) (N : ℕ)
    (hN : RootCountingAt38 (dirichletChar (realSlice u)) 1 N)
    (a : ℂ) (ha : a ∈ Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)))
    (r : ℝ) (hr : 0 < r)
    (hiso : ∀ z ∈ closedBall a r, z ≠ a → dirichletChar (realSlice u) z ≠ 0) :
    Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a r)) =
      (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N))).count a := by
  classical
  have ham := (counting_mem_zeroMultiset38 hN 0 (countingRadius38 N) a).mp ha
  rw [Lib.zeroMultiset_ball_eq_replicate hr (hN.2.1.mono (subset_univ _)) hiso,
    Multiset.card_replicate, Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _)),
    ite_eq_left ham.1]

/-- Simultaneous local counts for finitely many reference clusters. -/
theorem dirichlet_cluster_counts38 (u₀ : PhysicalL2) (N : ℕ)
    (hN : RootCountingAt38 (dirichletChar (realSlice u₀)) 1 N) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℂ → ℝ,
      (∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
        0 < ρ a ∧ ρ a < ε ∧ closedBall a (ρ a) ⊆ ball 0 (countingRadius38 N) ∧
        ∀ z ∈ closedBall a (3 * ρ a), z ≠ a → dirichletChar (realSlice u₀) z ≠ 0) ∧
      ∀ᶠ u in 𝓝 u₀, ∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
        Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a (ρ a))) =
          (Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N))).count a := by
  classical
  let M := Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N))
  let ρ : ℂ → ℝ := fun a => if ha : a ∈ M then
    Classical.choose (dirichlet_cluster_radius38 u₀ N hN a ha ε hε) else 1
  have hr (a : ℂ) (ha : a ∈ M) : 0 < ρ a ∧ ρ a < ε ∧
      closedBall a (ρ a) ⊆ ball 0 (countingRadius38 N) ∧
      ∀ z ∈ closedBall a (3 * ρ a), z ≠ a → dirichletChar (realSlice u₀) z ≠ 0 := by
    simpa only [ρ, dite_eq_left ha] using
      Classical.choose_spec (dirichlet_cluster_radius38 u₀ N hN a ha ε hε)
  have hcont : Continuous (fun p : PhysicalL2 × ℂ => dirichletChar (realSlice p.1) p.2) := by
    have hJ : Continuous (fun p : PotPair × ℂ => dirichletChar p.1 p.2) :=
      continuousOn_univ.mp analyticOnNhd_dirichletChar.continuousOn
    have hA : Continuous (fun p : PhysicalL2 × ℂ => (realSlice p.1, p.2)) :=
      (continuous_realSlice.comp continuous_fst).prodMk continuous_snd
    have hcomp := hJ.comp hA
    simpa only [Function.comp_def] using hcomp
  have hlocal (a : ℂ) (ha : a ∈ M) : ∀ᶠ u in 𝓝 u₀,
      Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a (ρ a))) = M.count a := by
    have hne : ∀ z ∈ sphere a (ρ a), dirichletChar (realSlice u₀) z ≠ 0 := by
      intro z hz
      apply (hr a ha).2.2.2 z
      · apply sphere_subset_closedBall.trans (closedBall_subset_closedBall ?_) hz
        linarith [(hr a ha).1]
      · intro he
        have hd : dist z a = ρ a := hz
        rw [he, dist_self] at hd
        linarith [(hr a ha).1]
    have he := Lib.eventually_card_zeroMultiset_eq (hr a ha).1
      (fun u => (analyticOnNhd_dirichletChar_z (realSlice u)).mono (subset_univ _))
      (hcont.continuousOn) u₀ hne
    have hcard := dirichlet_cluster_reference_card38 u₀ N hN a ha (ρ a) (hr a ha).1
      (fun z hz hza => (hr a ha).2.2.2 z
        ((closedBall_subset_closedBall (by linarith [(hr a ha).1])) hz) hza)
    simpa only [hcard] using he
  refine ⟨ρ, hr, ?_⟩
  have hall : ∀ᶠ u in 𝓝 u₀, ∀ a ∈ M.toFinset,
      Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a (ρ a))) = M.count a :=
    (Filter.eventually_all_finset M.toFinset).mpr (fun a ha => hlocal a (Multiset.mem_toFinset.mp ha))
  filter_upwards [hall] with u hu
  exact fun a ha => hu a (Multiset.mem_toFinset.mpr ha)

/-- A triple-radius isolation certificate makes different cluster balls disjoint. -/
theorem dirichlet_cluster_disjoint38 (u₀ : PhysicalL2) (N : ℕ)
    (hN : RootCountingAt38 (dirichletChar (realSlice u₀)) 1 N) (ρ : ℂ → ℝ)
    (hρ : ∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
      0 < ρ a ∧ ∀ z ∈ closedBall a (3 * ρ a), z ≠ a → dirichletChar (realSlice u₀) z ≠ 0)
    (a b : ℂ)
    (ha : a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)))
    (hb : b ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)))
    (hab : a ≠ b) : Disjoint (ball a (ρ a)) (ball b (ρ b)) := by
  have haz := ((counting_mem_zeroMultiset38 hN _ _ a).mp ha).2
  have hbz := ((counting_mem_zeroMultiset38 hN _ _ b).mp hb).2
  have hda : 3 * ρ a < dist a b := by
    by_contra h
    have hz := (hρ a ha).2 b (by simpa [dist_comm] using le_of_not_gt h) hab.symm
    exact hz hbz
  have hdb : 3 * ρ b < dist a b := by
    by_contra h
    have hz := (hρ b hb).2 a (le_of_not_gt h) hab
    exact hz haz
  apply Set.disjoint_left.mpr
  intro z hza hzb
  have ha' : dist a z < ρ a := by simpa [dist_comm] using hza
  have hb' : dist z b < ρ b := hzb
  have ht := dist_triangle a z b
  nlinarith [show 0 ≤ dist a b from dist_nonneg]

/-- Equal full cluster counts exhaust the actual central zeros. -/
theorem dirichlet_cluster_coverage38 (u₀ u : PhysicalL2) (N : ℕ)
    (hN₀ : RootCountingAt38 (dirichletChar (realSlice u₀)) 1 N)
    (hN : RootCountingAt38 (dirichletChar (realSlice u)) 1 N) (ρ : ℂ → ℝ)
    (hρ : ∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
      0 < ρ a ∧ closedBall a (ρ a) ⊆ ball 0 (countingRadius38 N) ∧
      ∀ z ∈ closedBall a (3 * ρ a), z ≠ a → dirichletChar (realSlice u₀) z ≠ 0)
    (hc : ∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
      Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a (ρ a))) =
        (Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N))).count a) :
    ∀ z ∈ Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)),
      ∃ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
        z ∈ ball a (ρ a) := by
  classical
  let M₀ := Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N))
  let D : Set ℂ := ⋃ a ∈ M₀.toFinset, ball a (ρ a)
  have hD : D ⊆ ball 0 (countingRadius38 N) := by
    intro z hz
    obtain ⟨a, ha, hz⟩ := mem_iUnion₂.mp hz
    exact (hρ a (Multiset.mem_toFinset.mp ha)).2.1 (ball_subset_closedBall hz)
  have hdisj : (M₀.toFinset : Set ℂ).PairwiseDisjoint (fun a => ball a (ρ a)) := by
    intro a ha b hb hab
    exact dirichlet_cluster_disjoint38 u₀ N hN₀ ρ
      (fun c hc => ⟨(hρ c hc).1, (hρ c hc).2.2⟩)
      a b (Multiset.mem_toFinset.mp ha) (Multiset.mem_toFinset.mp hb) hab
  have hcard : Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) D) = M₀.card := by
    rw [Lib.card_zeroMultiset_biUnion (hN.2.1.mono (subset_univ _))
      (isCompact_closedBall (0 : ℂ) (countingRadius38 N)) M₀.toFinset
      (fun a => ball a (ρ a))
      (fun a ha => (fun z hz => ball_subset_closedBall ((hρ a (Multiset.mem_toFinset.mp ha)).2.1
        (ball_subset_closedBall hz)))) hdisj]
    exact (Finset.sum_congr rfl (fun a ha => hc a (Multiset.mem_toFinset.mp ha))).trans
      (Multiset.toFinset_sum_count_eq M₀)
  have hle : Lib.zeroMultiset (dirichletChar (realSlice u)) D ≤
      Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)) := by
    apply Multiset.le_iff_count.mpr
    intro z
    rw [Lib.count_zeroMultiset_of_subset (hN.2.1.mono (subset_univ _))
      (isCompact_closedBall (0 : ℂ) (countingRadius38 N)) (hD.trans ball_subset_closedBall),
      Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _))]
    by_cases hz : z ∈ D
    · simp [hz, hD hz]
    · simp [hz]
  have he : Lib.zeroMultiset (dirichletChar (realSlice u)) D =
      Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)) := by
    apply Multiset.eq_of_le_of_card_le hle
    rw [hcard, hN.2.2.2.2.2.1, hN₀.2.2.2.2.2.1]
  intro z hz
  rw [← he] at hz
  have hzD : z ∈ D :=
    ((Lib.mem_zeroMultiset (hN.2.1.mono (subset_univ _))
      (isCompact_closedBall (0 : ℂ) (countingRadius38 N)) (hD.trans ball_subset_closedBall)).mp hz).1
  obtain ⟨a, ha, hz⟩ := mem_iUnion₂.mp hzD
  exact ⟨a, Multiset.mem_toFinset.mp ha, hz⟩

open Classical in
theorem dirichlet_cluster_filter38 (u : PhysicalL2) (N : ℕ)
    (hN : RootCountingAt38 (dirichletChar (realSlice u)) 1 N) (a : ℂ) (r : ℝ)
    (hsub : ball a r ⊆ ball 0 (countingRadius38 N)) :
    (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N))).filter
      (fun z => z ∈ ball a r) = Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a r) := by
  classical
  apply Multiset.ext'
  intro z
  rw [Multiset.count_filter, Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _)),
    Lib.count_zeroMultiset_ball (hN.2.1.mono (subset_univ _))]
  by_cases hz : z ∈ ball a r
  · simp [hz, hsub hz]
  · simp [hz]

end
end NlsGge.GK38
