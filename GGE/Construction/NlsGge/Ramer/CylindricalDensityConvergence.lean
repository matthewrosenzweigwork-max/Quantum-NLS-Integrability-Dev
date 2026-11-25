import NlsGge.Ramer.RamerDensity

/-!
# Convergence in probability of the cylindrical Ramer densities (v2, `prop:gaussiancommon`)

See `CylindricalDensityConvergence.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer

/-! ### Generic convergence-in-measure helpers -/

theorem tendstoInMeasure_add_zero {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : ℕ → α → ℝ} (hf : TendstoInMeasure μ f atTop (fun _ => (0 : ℝ)))
    (hg : TendstoInMeasure μ g atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ (fun n a => f n a + g n a) atTop (fun _ => (0 : ℝ)) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have h := (hf (ε / 2) hε2).add (hg (ε / 2) hε2)
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => zero_le)
    (fun n => ?_)
  refine le_trans (measure_mono (fun a ha => ?_)) (measure_union_le _ _)
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hcon ha
  have h1 : edist (f n a + g n a) 0 ≤ edist (f n a) 0 + edist (g n a) 0 := by
    rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Real.dist_eq, sub_zero]
    exact abs_add_le _ _
  have := lt_of_le_of_lt h1 (ENNReal.add_lt_add hcon.1 hcon.2)
  rw [ENNReal.add_halves] at this
  exact absurd ha (not_le.2 this)

/-- Convergence in measure from convergence in measure on each piece of a countable measurable
cover (finite measure). -/
theorem tendstoInMeasure_of_indicator_cover_inMeasure {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (A : ℕ → Set α) (hA : ∀ k, MeasurableSet (A k))
    (hcov : ∀ z, ∃ k, z ∈ A k) (f : ℕ → α → ℝ) (g : α → ℝ)
    (hk : ∀ k, TendstoInMeasure μ (fun n => (A k).indicator (fun z => f n z - g z)) atTop
      (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ f atTop g := by
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

open NlsGge.Pilot

variable {lower upper : ℝ}

/-! ### The orthogonal projection onto the head is the coordinate truncation -/

theorem starProjection_actualCMHead (c : BoundedCoefficients lower upper) (N : ℕ)
    (x : ActualCM c) :
    (actualCMHead c N).starProjection x = ((cmTrunc c N x : actualCMHead c N) : ActualCM c) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (cmTrunc c N x).2
  intro w hw
  have hwP : w = weightedRealProjectionContinuous (cmModeWeight c) (symmetricModes N) w := by
    apply cmCoord_ext
    intro n
    have h := weightedRealProjection_apply (cmModeWeight c) (symmetricModes N) w n
    change cmCoord w n = _
    change _ = (show WeightedHilbert (cmModeWeight c) from
      weightedRealProjectionContinuous (cmModeWeight c) (symmetricModes N) w) n
    rw [h]
    split_ifs with hn
    · rfl
    · exact hw n hn
  have h := weightedRealProjection_range_residual (cmModeWeight c) (symmetricModes N) x w
  rw [← hwP] at h
  exact (real_inner_comm w _).trans h

theorem tendsto_starProjection_actualCMHead (c : BoundedCoefficients lower upper)
    (x : ActualCM c) :
    Tendsto (fun N : ℕ => (actualCMHead c N).starProjection x) atTop (𝓝 x) := by
  simp_rw [starProjection_actualCMHead]
  exact weightedProjection_tendsto (cmModeWeight c) (show WeightedHilbert (cmModeWeight c) from x)

/-! ### Finite determinant bridge -/

theorem finiteDet2_eq_analysis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (B : V →L[ℝ] V) :
    finiteDet2 B = Analysis.RegularizedDeterminant.finiteDet2 (B : V →ₗ[ℝ] V) := by
  unfold finiteDet2 Analysis.RegularizedDeterminant.finiteDet2
  rfl

/-- The finite density in `det₂`/divergence form for the truncated field. -/
theorem finiteRamerDensity_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K) (N : ℕ)
    (v : actualCMHead c N) :
    finiteRamerDensity (fun w => w + truncField c s K N w) v =
      |finiteDet2 (fderiv ℝ (truncField c s K N) v)| *
        Real.exp (-finiteGaussianDivergence (truncField c s K N) v -
          ‖truncField c s K N v‖ ^ 2 / 2) := by
  have hT : Differentiable ℝ (fun w => w + truncField c s K N w) :=
    differentiable_id.add ((contDiff_truncField c s K hK N).differentiable (by norm_num))
  have h := finiteRamerDensity_eq_det2_form _ hT v
  simpa using h

open Analysis.RegularizedDeterminant (restrictedEnd det2)
open Analysis.RegularizedDeterminant.HilbertSchmidt (compression toCLM toCLM_compression)

theorem restrictedEnd_eq_fderiv_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (N : ℕ) (v : actualCMHead c N) (hmem) :
    restrictedEnd (toCLM
      (compression (actualCMHead c N) (hsDerivH c s hs K (headToE c s N v)))).toLinearMap
      (actualCMHead c N) hmem =
      ((fderiv ℝ (truncField c s K N) v : actualCMHead c N →L[ℝ] actualCMHead c N) :
        actualCMHead c N →ₗ[ℝ] actualCMHead c N) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  have hs0 : 0 ≤ s := le_of_lt (by linarith : (0 : ℝ) < s)
  change (toCLM
      (compression (actualCMHead c N) (hsDerivH c s hs K (headToE c s N v)))) (w : ActualCM c) = _
  rw [toCLM_compression]
  have h1 : (actualCMHead c N).starProjection (w : ActualCM c) = (w : ActualCM c) :=
    Submodule.starProjection_eq_self_iff.2 w.2
  have h2 : ∀ u : ActualCM c, (hsDerivH c s hs K (headToE c s N v)).toCLM u =
      fderiv ℝ K (headToE c s N v) (cmToFullWeightedHilbert c s hs0 u) :=
    fun u => congrArg (fun f => f u) (hsDerivH_toCLM c s hs K (headToE c s N v))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2,
    starProjection_actualCMHead, fderiv_truncField c s K hK N v,
    ← headToE_eq_cmToFull c s hs0 N w]
  rfl
/-- The realization has the sample as its coordinates (the a.e. property used throughout). -/
def RealizesCoords (c : BoundedCoefficients lower upper) (s : ℝ) (z : ℤ → ℂ) : Prop :=
  ∀ n : ℤ, (show WeightedHilbert (fullModeWeight c s) from
      NlsGge.Measure.fullWeightedSequenceRealization c s z) n = z n

theorem tendsto_finiteDet2_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (z : ℤ → ℂ) (hz : RealizesCoords c s z) :
    Tendsto (fun N => finiteDet2 (fderiv ℝ (truncField c s K N) (headPt c N z))) atTop
      (𝓝 (det2 (hsDerivH c s hs K (NlsGge.Measure.fullWeightedSequenceRealization c s z)))) := by
  have hxs := tendsto_headToE_headPt c s z hz
  have hA : Tendsto (fun N => hsDerivH c s hs K (headToE c s N (headPt c N z))) atTop
      (𝓝 (hsDerivH c s hs K (NlsGge.Measure.fullWeightedSequenceRealization c s z))) :=
    ((continuous_hsDerivH c s hs K (hK.of_le (by norm_num))).tendsto _).comp hxs
  have h := Analysis.RegularizedDeterminant.tendsto_finiteSection_finiteDet2 atTop
    (fun N => actualCMHead c N) (tendsto_starProjection_actualCMHead c) _ _ hA
  refine h.congr (fun N => ?_)
  rw [restrictedEnd_eq_fderiv_truncField c s hs K hK N (headPt c N z), finiteDet2_eq_analysis]

theorem tendsto_norm_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : Continuous K)
    (z : ℤ → ℂ) (hz : RealizesCoords c s z) :
    Tendsto (fun N => ‖truncField c s K N (headPt c N z)‖) atTop
      (𝓝 ‖K (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) := by
  have h := tendsto_cmTrunc_comp c s K hK _ _ (tendsto_headToE_headPt c s z hz)
  exact h.norm

/-! ### Local divergence convergence -/

theorem measurable_cylDiv_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K) (N : ℕ) :
    Measurable (fun z => cylDiv c N (truncField c s K N) z) :=
  (continuous_finiteGaussianDivergence
    ((contDiff_truncField c s K hK N).of_le (by norm_num))).measurable.comp
    (measurable_headPt c N)

/-- Local data around a point: a bounded `C²` field `G` equal to `K` on a ball, with the
`L²(γ)` limit `η` of the cylindrical divergences of its truncations, which is a closed divergence
of `G ∘ R`. -/
theorem exists_local_truncDiv (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (x₀ : FullWeightedHilbert c s) :
    ∃ r > 0, ∃ (G : FullWeightedHilbert c s → ActualCM c) (η : (ℤ → ℂ) → ℝ),
      Set.EqOn G K (Metric.ball x₀ r) ∧ ContDiff ℝ 2 G ∧
      IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η ∧
      Tendsto (fun N => eLpNorm (fun z => cylDiv c N (truncField c s G N) z - η z) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0) := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith)
  obtain ⟨r, hr, hKb, hDb⟩ := exists_local_radius_bounds K hK x₀
  obtain ⟨-, -, -, -, -, -, G, B, -, hGd, hGv, hGD, hEq⟩ :=
    exists_bumped_field_radius c s hs0 K hK x₀ hr _ _ hKb hDb
  obtain ⟨η, hη, hv2⟩ := exists_tendsto_cylDiv_truncField c s hs G hGd B hGv hGD
  exact ⟨r, hr, G, η, hEq, hGd, isClosedDiv_of_tendsto_truncField c s hs G hGd B hGv hGD η hη hv2,
    hv2⟩

/-- On a ball where `G = K`, the cylindrical divergences of the truncations eventually agree. -/
theorem eventually_cylDiv_truncField_eq (c : BoundedCoefficients lower upper) (s : ℝ)
    (K G : FullWeightedHilbert c s → ActualCM c) {x₀ : FullWeightedHilbert c s} {r : ℝ}
    (hEq : Set.EqOn G K (Metric.ball x₀ r)) (z : ℤ → ℂ) (hz : RealizesCoords c s z)
    (hzr : NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ Metric.ball x₀ r) :
    ∀ᶠ N in atTop, cylDiv c N (truncField c s K N) z = cylDiv c N (truncField c s G N) z := by
  have hxs := tendsto_headToE_headPt c s z hz
  filter_upwards [hxs.eventually (Metric.isOpen_ball.mem_nhds hzr)] with N hN
  unfold cylDiv
  refine finiteGaussianDivergence_congr_of_eventuallyEq ?_
  have hU : IsOpen ((headToE c s N) ⁻¹' Metric.ball x₀ r) :=
    Metric.isOpen_ball.preimage (headToE c s N).continuous
  filter_upwards [hU.mem_nhds hN] with w hw
  unfold truncField
  rw [hEq hw]

/-- Convergence in measure of the cylindrical divergences on one patch. -/
theorem tendstoInMeasure_indicator_cylDiv (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K G : FullWeightedHilbert c s → ActualCM c)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G) {x₀ : FullWeightedHilbert c s} {r : ℝ}
    (hEq : Set.EqOn G K (Metric.ball x₀ r)) (δK η : (ℤ → ℂ) → ℝ)
    (hδη : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ Metric.ball x₀ r → δK z = η z)
    (hL : Tendsto (fun N => eLpNorm (fun z => cylDiv c N (truncField c s G N) z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
      (fun N => (NlsGge.Measure.fullWeightedSequenceRealization c s ⁻¹' Metric.ball x₀ r).indicator
        (fun z => cylDiv c N (truncField c s K N) z - δK z)) atTop (fun _ => (0 : ℝ)) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  set A : Set (ℤ → ℂ) := R ⁻¹' Metric.ball x₀ r with hA
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hAm : MeasurableSet A := hRm Metric.isOpen_ball.measurableSet
  have hv : TendstoInMeasure γ (fun N => A.indicator
      (fun z => cylDiv c N (truncField c s G N) z - η z)) atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL (fun N => zero_le)
      (fun N => ?_)
    have h : (A.indicator (fun z => cylDiv c N (truncField c s G N) z - η z) -
        fun _ => (0 : ℝ)) = A.indicator (fun z => cylDiv c N (truncField c s G N) z - η z) := by
      funext z; simp
    rw [h]
    exact eLpNorm_indicator_le (p := 2) (μ := γ)
      (fun z => cylDiv c N (truncField c s G N) z - η z) hAm
  have hw : TendstoInMeasure γ (fun N => A.indicator
      (fun z => cylDiv c N (truncField c s K N) z - cylDiv c N (truncField c s G N) z)) atTop
      (fun _ => (0 : ℝ)) := by
    have hmeas : ∀ N, Measurable (A.indicator
        (fun z => cylDiv c N (truncField c s K N) z - cylDiv c N (truncField c s G N) z)) :=
      fun N => ((measurable_cylDiv_truncField c s K hK N).sub
        (measurable_cylDiv_truncField c s G hG N)).indicator hAm
    refine tendstoInMeasure_of_tendsto_ae (fun N => (hmeas N).aestronglyMeasurable) ?_
    filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hz
    by_cases hzA : z ∈ A
    · have := eventually_cylDiv_truncField_eq c s K G hEq z hz hzA
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [this] with N hN
      rw [Set.indicator_of_mem hzA, hN, sub_self]
    · simp [Set.indicator_of_notMem hzA]
  have hsum := tendstoInMeasure_add_zero hv hw
  refine hsum.congr' (Eventually.of_forall fun N => ?_) (Filter.EventuallyEq.refl _ _)
  filter_upwards [hδη] with z hz
  by_cases hzA : z ∈ A
  · simp only [Set.indicator_of_mem hzA]
    rw [hz hzA]; ring
  · simp [Set.indicator_of_notMem hzA]

/-- **Divergence convergence.** If `δK` is a local divergence of `K` in the sense of clause 3 of
`divergence_identification` (it agrees a.e. on `{R ∈ B}` with the closed divergence of every field
equal to `K` on `B`), then `δ_cyl(P_N K(P_N ·)) → δK` in probability. -/
theorem tendstoInMeasure_cylDiv_truncField (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (δK : (ℤ → ℂ) → ℝ)
    (hδK : ∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (Metric.ball x₀ r) →
        IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
        ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
          NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ Metric.ball x₀ r →
            δK z = η z) :
    TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
      (fun N z => cylDiv c N (truncField c s K N) z) atTop δK := by
  classical
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  have hRm : Measurable R := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  choose r hr G η hEq hGd hCD hL using exists_local_truncDiv c s hs K hK
  obtain ⟨T, hTc, hTcov⟩ := exists_countable_cover_balls c s r hr
  have hTne : T.Nonempty := by
    obtain ⟨y, hy, -⟩ := hTcov 0
    exact ⟨y, hy⟩
  obtain ⟨xk, hxk⟩ := hTc.exists_eq_range hTne
  have hcovz : ∀ z, ∃ k, z ∈ R ⁻¹' Metric.ball (xk k) (r (xk k)) := by
    intro z
    obtain ⟨y, hy, hzy⟩ := hTcov (R z)
    rw [hxk] at hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨k, hzy⟩
  refine tendstoInMeasure_of_indicator_cover_inMeasure (μ := γ)
    (fun k => R ⁻¹' Metric.ball (xk k) (r (xk k)))
    (fun k => hRm Metric.isOpen_ball.measurableSet) hcovz _ δK (fun k => ?_)
  exact tendstoInMeasure_indicator_cylDiv c s hs K (G (xk k)) hK (hGd (xk k)) (hEq (xk k)) δK
    (η (xk k)) (hδK (xk k) (r (xk k)) (G (xk k)) (η (xk k)) (hEq (xk k)) (hCD (xk k)))
    (hL (xk k))

theorem measurable_finiteRamerDensity_of_continuous {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (T : V → V) (hT : Continuous T) : Measurable (finiteRamerDensity T) := by
  unfold finiteRamerDensity
  have hdet : Measurable (fun x : V => (fderiv ℝ T x).det) :=
    ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ T)
  have hexp : Measurable (fun x : V => Real.exp (-(‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2)) := by
    have : Continuous (fun x : V => Real.exp (-(‖T x‖ ^ 2 - ‖x‖ ^ 2) / 2)) := by fun_prop
    exact this.measurable
  exact (continuous_abs.measurable.comp hdet).mul hexp

/-- **Cylindrical Ramer densities converge in probability to `J_T`** (v2, `prop:gaussiancommon`,
`eq:cylindricalcommon`, via `lem:determinants`).  With `x_N = P_N x`, `T_N = id + P_N K(P_N ·)` on
`V_N`, the density `J_N = |det DT_N(x_N)| exp(-(‖T_N x_N‖² - ‖x_N‖²)/2)` converges in
`γ`-probability to `J_K = |det₂(I + D_H K)| exp(-δK - ‖K‖²_H/2)`, for any `δK` satisfying the
locality clause (clause 3) of `divergence_identification`. -/
theorem tendstoInMeasure_cylindricalDensity (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K)
    (δK : (ℤ → ℂ) → ℝ)
    (hδK : ∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (Metric.ball x₀ r) →
        IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
        ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
          NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ Metric.ball x₀ r →
            δK z = η z) :
    TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
      (fun N z => finiteRamerDensity (fun v => v + truncField c s K N v) (headPt c N z))
      atTop (ramerJ c s hs K δK) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hmeas : ∀ N, AEStronglyMeasurable (fun z =>
      finiteRamerDensity (fun v => v + truncField c s K N v) (headPt c N z)) γ := by
    intro N
    refine (Measurable.aestronglyMeasurable ?_)
    refine (measurable_finiteRamerDensity_of_continuous _ ?_).comp (measurable_headPt c N)
    exact continuous_id.add (contDiff_truncField c s K hK N).continuous
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  have hdiv := (tendstoInMeasure_cylDiv_truncField c s hs K hK δK hδK).comp hns.tendsto_atTop
  obtain ⟨ns', hns', hae⟩ := hdiv.exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  have hsub : Tendsto (fun i => ns (ns' i)) atTop atTop := hns.tendsto_atTop.comp hns'.tendsto_atTop
  filter_upwards [hae, NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hd hz
  have hD := (tendsto_finiteDet2_truncField c s hs K hK z hz).comp hsub
  have hn := (tendsto_norm_truncField c s K hK.continuous z hz).comp hsub
  have hlim := hD.abs.mul (Real.continuous_exp.tendsto _ |>.comp (hd.neg.sub ((hn.pow 2).div_const 2)))
  unfold ramerJ
  refine hlim.congr (fun i => ?_)
  simp only [Function.comp]
  rw [finiteRamerDensity_truncField c s K hK]
  rfl

/-- **Composed form.** The divergence `δK` of `divergence_identification` (measurable, locally
equal to closed divergences, independent of localization) satisfies the convergence
`J_N → J_K` in probability. -/
theorem exists_cylindricalDensity_limit (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 2 K) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      AEStronglyMeasurable δK (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
      (∀ (x₀ : FullWeightedHilbert c s) (r : ℝ) (G : FullWeightedHilbert c s → ActualCM c)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (Metric.ball x₀ r) →
          IsClosedDiv c (fun z => G (NlsGge.Measure.fullWeightedSequenceRealization c s z)) η →
          ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
            NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ Metric.ball x₀ r →
              δK z = η z) ∧
      TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
        (fun N z => finiteRamerDensity (fun v => v + truncField c s K N v) (headPt c N z))
        atTop (ramerJ c s hs K δK) := by
  obtain ⟨δK, hm, -, h3, -, -⟩ := divergence_identification c s hs K hK
  exact ⟨δK, hm, h3, tendstoInMeasure_cylindricalDensity c s hs K hK δK h3⟩

end NlsGge.Ramer
