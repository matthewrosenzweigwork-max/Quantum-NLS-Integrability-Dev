import NlsGge.Ramer.General.PatchingPrereqsG
import NlsGge.Ramer.General.TruncLimitClosedDivG
import NlsGge.Ramer.General.DivergenceIdentificationBoundedG

/-!
# Global divergence identification for unbounded `C²` fields (GB10, general setting)

Generalization of `NlsGge/Ramer/DivergenceIdentificationGlobal.lean` to a `RamerSetting S`.
For `K : S.E → S.H` of class `C²` (no global bounds), there is a single `S.γ`-measurable
`δK : Ω → ℝ` such that

* every point `x₀` has a ball on which `K` agrees with a field `G` having closed divergence `η`;
* `δK` agrees `S.γ`-a.e. on `{S.R ∈ B(x₀, r)}` with the closed divergence of any field `G`
  that equals `K` on `B(x₀, r)`;
* a subsequence of Ramer's approximants `S.ramerA n K` converges `S.γ`-a.e. to `δK`, and the
  approximants converge in measure.

The statement is the old one, translated by the dictionary (`c, s, hs` replaced by `S`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

/-! ### Generic helpers -/

/-- Local radius: around each point a `C¹` map and its derivative are bounded by their value at
the center plus one, on the ball of radius `2r`. -/
theorem exists_local_radius_bounds {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : E → F) (hK : ContDiff ℝ 2 K) (x : E) :
    ∃ r > 0, (∀ y ∈ Metric.ball x (2 * r), ‖K y‖ ≤ ‖K x‖ + 1) ∧
      (∀ y ∈ Metric.ball x (2 * r), ‖fderiv ℝ K y‖ ≤ ‖fderiv ℝ K x‖ + 1) := by
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuousAt_iff.1 hK.continuous.continuousAt 1 one_pos
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousAt_iff.1
    ((hK.continuous_fderiv (by norm_num)).continuousAt (x := x)) 1 one_pos
  refine ⟨min δ1 δ2 / 2, by positivity, fun y hy => ?_, fun y hy => ?_⟩
  · have hy' : dist y x < δ1 := by
      rw [Metric.mem_ball] at hy
      have := min_le_left δ1 δ2; linarith
    have := h1 hy'
    rw [dist_eq_norm] at this
    have := norm_sub_norm_le (K y) (K x)
    linarith
  · have hy' : dist y x < δ2 := by
      rw [Metric.mem_ball] at hy
      have := min_le_right δ1 δ2; linarith
    have := h2 hy'
    rw [dist_eq_norm] at this
    have := norm_sub_norm_le (fderiv ℝ K y) (fderiv ℝ K x)
    linarith

/-- Convergence in measure from `L²` convergence on each piece of a countable measurable cover
(finite measure). No measurability of `f n` or `g` is needed. -/
theorem tendstoInMeasure_of_indicator_cover {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (A : ℕ → Set α) (hA : ∀ k, MeasurableSet (A k))
    (hcov : ∀ z, ∃ k, z ∈ A k) (f : ℕ → α → ℝ) (g : α → ℝ)
    (h : ∀ k, Tendsto (fun n => eLpNorm ((A k).indicator (fun z => f n z - g z)) 2 μ) atTop
      (𝓝 0)) :
    TendstoInMeasure μ f atTop g := by
  have hk : ∀ k, TendstoInMeasure μ (fun n => (A k).indicator (fun z => f n z - g z)) atTop
      (fun _ => (0 : ℝ)) := by
    intro k
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    refine (h k).congr (fun n => ?_)
    congr 1
    funext z
    simp
  set S : ℕ → Set α := fun N => ⋃ k ∈ Finset.range N, A k with hS
  have hSm : ∀ N, MeasurableSet (S N) := fun N =>
    Finset.measurableSet_biUnion _ (fun k _ => hA k)
  have hSc : Tendsto (fun N => μ (S N)ᶜ) atTop (𝓝 0) := by
    have hanti : Antitone (fun N => (S N)ᶜ) := by
      intro N M hNM
      refine Set.compl_subset_compl.2 ?_
      intro z hz
      obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.1 hz
      exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2
        (lt_of_lt_of_le (Finset.mem_range.1 hk) hNM), hzk⟩
    have := tendsto_measure_iInter_atTop (μ := μ) (s := fun N => (S N)ᶜ)
      (fun N => (hSm N).compl.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ N, (S N)ᶜ) = ∅ := by
      ext z
      simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_forall, not_not]
      obtain ⟨k, hzk⟩ := hcov z
      exact ⟨k + 1, Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), hzk⟩⟩
    rw [hempty, measure_empty] at this
    exact this
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hSc (e / 2) he2).exists
  have hsum := tendsto_finsetSum (Finset.range N) (fun k _ => hk k ε hε)
  rw [Finset.sum_const_zero] at hsum
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum (e / 2) he2] with n hn
  calc μ {z | ε ≤ edist (f n z) (g z)}
      ≤ μ ((⋃ k ∈ Finset.range N,
          {z | ε ≤ edist ((A k).indicator (fun z => f n z - g z) z) 0}) ∪ (S N)ᶜ) := by
        refine measure_mono (fun z hz => ?_)
        by_cases hzS : z ∈ S N
        · left
          obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.1 hzS
          refine Set.mem_iUnion₂.2 ⟨k, hk, ?_⟩
          have e1 : edist ((A k).indicator (fun z => f n z - g z) z) 0 =
              edist (f n z) (g z) := by
            rw [Set.indicator_of_mem hzk, edist_dist, edist_dist, dist_zero_right,
              dist_eq_norm]
          show ε ≤ _
          rw [e1]; exact hz
        · right; exact hzS
    _ ≤ μ (⋃ k ∈ Finset.range N,
          {z | ε ≤ edist ((A k).indicator (fun z => f n z - g z) z) 0}) + μ (S N)ᶜ :=
        measure_union_le _ _
    _ ≤ (∑ k ∈ Finset.range N,
          μ {z | ε ≤ edist ((A k).indicator (fun z => f n z - g z) z) 0}) + μ (S N)ᶜ := by
        gcongr
        exact measure_biUnion_finset_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hn hN
    _ = e := ENNReal.add_halves e

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### Closed divergences -/

variable {S} in
/-- The closed divergence may be changed on a `γ`-null set. -/
theorem IsClosedDiv.congr_ae {F : (ℤ → ℂ) → S.H}
    {η η' : (ℤ → ℂ) → ℝ} (h : S.IsClosedDiv F η)
    (he : η =ᵐ[S.γ] η') : S.IsClosedDiv F η' := by
  obtain ⟨hη, N, g, C, p, hg, hgg, hDg, hF, hδ⟩ := h
  refine ⟨hη.ae_eq he, N, g, C, p, hg, hgg, hDg, hF, hδ.congr (fun k => ?_)⟩
  refine eLpNorm_congr_ae ?_
  filter_upwards [he] with z hz
  rw [hz]

variable {S} in
/-- **Locality on open sets.** If `G = G'` on an open `O ⊆ S.E` and `G ∘ R`, `G' ∘ R` have closed
divergences `η`, `η'`, then `η = η'` `γ`-a.e. on `{R ∈ O}`. -/
theorem IsClosedDiv.ae_eq_of_eqOn {O : Set S.E} (hO : IsOpen O)
    {G G' : S.E → S.H} (hGG : Set.EqOn G G' O)
    {η η' : (ℤ → ℂ) → ℝ}
    (h : S.IsClosedDiv (fun z => G (S.R z)) η)
    (h' : S.IsClosedDiv (fun z => G' (S.R z)) η') :
    ∀ᵐ z ∂S.γ, S.R z ∈ O → η z = η' z := by
  set R := S.R with hR
  have hloc : ∀ y ∈ O, ∃ t > 0, ∀ᵐ z ∂S.γ, R z ∈ Metric.ball y t → η z = η' z := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO y hy
    have ht : 0 < ε / 2 := by positivity
    obtain ⟨ρ, gradρ, B, hρ, hρ1, hρ0⟩ := S.exists_bump_productRuleClass_support y ht
    have hGG' : ∀ x, ρ x • G x = ρ x • G' x := by
      intro x
      by_cases hx : x ∈ Metric.ball y (2 * (ε / 2))
      · have : x ∈ O := hball (by rwa [show 2 * (ε / 2) = ε by ring] at hx)
        rw [hGG this]
      · rw [hρ0 x hx, zero_smul, zero_smul]
    exact ⟨ε / 2, ht, IsClosedDiv.local_eq hρ Metric.isOpen_ball hρ1 hGG' h h'⟩
  choose t ht hae using hloc
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : O => Metric.ball (y : S.E) (t y y.2))
    (fun _ => Metric.isOpen_ball)
  have hall : ∀ᵐ z ∂S.γ, ∀ i ∈ T,
      R z ∈ Metric.ball (i : S.E) (t i i.2) → η z = η' z :=
    (ae_ball_iff hT).2 (fun i _ => hae i i.2)
  filter_upwards [hall] with z hz hzO
  have hmem : R z ∈ ⋃ i : O, Metric.ball (i : S.E) (t i i.2) :=
    Set.mem_iUnion.2 ⟨⟨R z, hzO⟩, Metric.mem_ball_self (ht _ hzO)⟩
  rw [← hTeq] at hmem
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 hmem
  exact hz i hi hzi

/-- **Local closed divergence with Ramer convergence.** Around each `x₀ ∈ S.E` a `C²` field `K`
agrees on a ball with a bounded bumped field `G`, which has a strongly measurable closed
divergence `η` to which Ramer's approximants of `G` converge in `L²(γ)`. -/
theorem exists_local_closedDiv (K : S.E → S.H) (hK : ContDiff ℝ 2 K) (x₀ : S.E) :
    ∃ r > 0, ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
      Set.EqOn G K (Metric.ball x₀ r) ∧
      S.IsClosedDiv (fun z => G (S.R z)) η ∧
      StronglyMeasurable η ∧
      Tendsto (fun n => eLpNorm (fun z => S.ramerA n G z - η z) 2 S.γ) atTop (𝓝 0) := by
  obtain ⟨r, hr, hKb, hDb⟩ := exists_local_radius_bounds K hK x₀
  obtain ⟨-, -, -, -, -, -, G, B, -, hGd, hGv, hGD, hEq⟩ :=
    S.exists_bumped_field_radius K hK x₀ hr _ _ hKb hDb
  obtain ⟨η, hη, hv2, hRam⟩ := S.divergence_identification_bounded G hGd B hGv hGD
  have hCD := S.isClosedDiv_of_tendsto_truncField G hGd B hGv hGD η hη hv2
  have he := hη.aestronglyMeasurable.ae_eq_mk
  refine ⟨r, hr, G, hη.aestronglyMeasurable.mk η, hEq, hCD.congr_ae he,
    hη.aestronglyMeasurable.stronglyMeasurable_mk, hRam.congr (fun n => ?_)⟩
  refine eLpNorm_congr_ae ?_
  filter_upwards [he] with z hz
  rw [hz]

/-! ### Main theorem -/

/-- **Global divergence identification.** -/
theorem divergence_identification (K : S.E → S.H) (hK : ContDiff ℝ 2 K) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      AEStronglyMeasurable δK S.γ ∧
      (∀ x₀, ∃ r > 0, ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (Metric.ball x₀ r) ∧
          S.IsClosedDiv (fun z => G (S.R z)) η) ∧
      (∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
          Set.EqOn G K (Metric.ball x₀ r) →
          S.IsClosedDiv (fun z => G (S.R z)) η →
          ∀ᵐ z ∂S.γ, S.R z ∈ Metric.ball x₀ r → δK z = η z) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ᵐ z ∂S.γ, Tendsto (fun j => S.ramerA (φ j) K z) atTop (𝓝 (δK z))) ∧
      TendstoInMeasure S.γ (fun n => S.ramerA n K) atTop δK := by
  classical
  set γ := S.γ with hγ
  set R := S.R with hR
  have hRm : Measurable R := S.measurable_R
  choose r hr G η hEq hCD hηm hRam using S.exists_local_closedDiv K hK
  obtain ⟨T, hTc, hTcov⟩ := S.exists_countable_cover_balls r hr
  have hTne : T.Nonempty := by
    obtain ⟨y, hy, -⟩ := hTcov 0
    exact ⟨y, hy⟩
  obtain ⟨xk, hxk⟩ := hTc.exists_eq_range hTne
  set B : ℕ → Set S.E := fun k => Metric.ball (xk k) (r (xk k)) with hB
  have hcovz : ∀ z, ∃ k, R z ∈ B k := by
    intro z
    obtain ⟨y, hy, hzy⟩ := hTcov (R z)
    rw [hxk] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k, hzy⟩
  set δK : (ℤ → ℂ) → ℝ := fun z => η (xk (Nat.find (hcovz z))) z with hδK
  have hδm : Measurable δK :=
    Measurable.find (f := fun k => η (xk k)) (p := fun k z => R z ∈ B k)
      (fun k => (hηm _).measurable) (fun k => hRm Metric.isOpen_ball.measurableSet) hcovz
  -- clause 3: independence of the localization
  have hind : ∀ (x₀ : S.E) (r' : ℝ) (G' : S.E → S.H) (η' : (ℤ → ℂ) → ℝ),
      Set.EqOn G' K (Metric.ball x₀ r') →
      S.IsClosedDiv (fun z => G' (R z)) η' →
      ∀ᵐ z ∂γ, R z ∈ Metric.ball x₀ r' → δK z = η' z := by
    intro x₀ r' G' η' hE hC
    have hk : ∀ k, ∀ᵐ z ∂γ, R z ∈ Metric.ball x₀ r' ∩ B k → η (xk k) z = η' z := by
      intro k
      refine IsClosedDiv.ae_eq_of_eqOn (Metric.isOpen_ball.inter Metric.isOpen_ball)
        (fun y hy => ?_) (hCD (xk k)) hC
      rw [hEq (xk k) hy.2, hE hy.1]
    filter_upwards [ae_all_iff.2 hk] with z hz hzb
    exact hz _ ⟨hzb, Nat.find_spec (hcovz z)⟩
  refine ⟨δK, hδm.aestronglyMeasurable, fun x₀ => ⟨r x₀, hr x₀, G x₀, η x₀, hEq x₀, hCD x₀⟩,
    hind, ?_⟩
  -- clause 4
  have hloc : ∀ k, Tendsto (fun n => eLpNorm ((R ⁻¹' B k).indicator
      (fun z => S.ramerA n K z - δK z)) 2 γ) atTop (𝓝 0) := by
    intro k
    have h1 := S.tendsto_eLpNorm_indicator_ramerA_of_eqOn (G (xk k)) K Metric.isOpen_ball
      (hEq (xk k)) (η (xk k)) (hRam (xk k))
    have h2 := hind (xk k) (r (xk k)) (G (xk k)) (η (xk k)) (hEq (xk k)) (hCD (xk k))
    refine h1.congr (fun n => eLpNorm_congr_ae ?_)
    filter_upwards [h2] with z hz
    by_cases hzk : z ∈ R ⁻¹' B k
    · rw [Set.indicator_of_mem hzk, Set.indicator_of_mem hzk, hz hzk]
    · rw [Set.indicator_of_notMem hzk, Set.indicator_of_notMem hzk]
  have hmeas := tendstoInMeasure_of_indicator_cover (μ := γ) (fun k => R ⁻¹' B k)
    (fun k => hRm Metric.isOpen_ball.measurableSet) hcovz
    (fun n => S.ramerA n K) δK hloc
  exact ⟨hmeas.exists_seq_tendsto_ae, hmeas⟩

end NlsGge.Ramer.General.RamerSetting

