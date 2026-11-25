import NlsGge.Ramer.General.RamerDensityG

/-!
# Convergence in probability of the cylindrical Ramer densities over a `RamerSetting`

Adapted from `NlsGge/Ramer/CylindricalDensityConvergence.lean` (v2, `prop:gaussiancommon`).
Generic helpers (convergence in measure, the finite determinant bridge, measurability of the finite
Ramer density) are in `NlsGge.Ramer.Gen`; everything else is `S.name`.  The anisotropy enters only
through the already-landed `S.headToE`, `S.incl`, `S.hsDerivH`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer.Gen

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

/-! ### Finite determinant bridge -/

theorem finiteDet2_eq_analysis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (B : V →L[ℝ] V) :
    finiteDet2 B = Analysis.RegularizedDeterminant.finiteDet2 (B : V →ₗ[ℝ] V) := by
  unfold finiteDet2 Analysis.RegularizedDeterminant.finiteDet2
  rfl


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

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Ramer.Gen
open NlsGge.Analysis.RegularizedDeterminant (restrictedEnd det2)
open NlsGge.Analysis.RegularizedDeterminant.HilbertSchmidt (compression toCLM toCLM_compression)

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### The orthogonal projection onto the head is the coordinate truncation -/

theorem starProjection_head (N : ℕ) (x : S.H) :
    (S.head N).starProjection x = ((S.cmTrunc N x : S.head N) : S.H) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (S.cmTrunc N x).2
  intro w hw
  have hwP : w = weightedRealProjectionContinuous S.cmWeight (symmetricModes N) w := by
    apply S.hcoord_ext
    intro n
    have h := weightedRealProjection_apply S.cmWeight (symmetricModes N) w n
    change S.hcoord w n = _
    change _ = (show WeightedHilbert S.cmWeight from
      weightedRealProjectionContinuous S.cmWeight (symmetricModes N) w) n
    rw [h]
    split_ifs with hn
    · rfl
    · exact hw n hn
  have h := weightedRealProjection_range_residual S.cmWeight (symmetricModes N) x w
  rw [← hwP] at h
  exact (real_inner_comm w _).trans h

theorem tendsto_starProjection_head (x : S.H) :
    Tendsto (fun N : ℕ => (S.head N).starProjection x) atTop (𝓝 x) := by
  simp_rw [S.starProjection_head]
  exact weightedProjection_tendsto S.cmWeight (show WeightedHilbert S.cmWeight from x)

/-! ### Finite determinant bridge -/

/-- The finite density in `det₂`/divergence form for the truncated field. -/
theorem finiteRamerDensity_truncField
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K) (N : ℕ)
    (v : S.head N) :
    finiteRamerDensity (fun w => w + S.truncField K N w) v =
      |finiteDet2 (fderiv ℝ (S.truncField K N) v)| *
        Real.exp (-finiteGaussianDivergence (S.truncField K N) v -
          ‖S.truncField K N v‖ ^ 2 / 2) := by
  have hT : Differentiable ℝ (fun w => w + S.truncField K N w) :=
    differentiable_id.add ((S.contDiff_truncField K hK N).differentiable (by norm_num))
  have h := finiteRamerDensity_eq_det2_form _ hT v
  simpa using h

theorem restrictedEnd_eq_fderiv_truncField
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K)
    (N : ℕ) (v : S.head N) (hmem) :
    restrictedEnd (toCLM
      (compression (S.head N) (S.hsDerivH K (S.headToE N v)))).toLinearMap
      (S.head N) hmem =
      ((fderiv ℝ (S.truncField K N) v : S.head N →L[ℝ] S.head N) :
        S.head N →ₗ[ℝ] S.head N) := by
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  change (toCLM
      (compression (S.head N) (S.hsDerivH K (S.headToE N v)))) (w : S.H) = _
  rw [toCLM_compression]
  have h1 : (S.head N).starProjection (w : S.H) = (w : S.H) :=
    Submodule.starProjection_eq_self_iff.2 w.2
  have h2 : ∀ u : S.H, (S.hsDerivH K (S.headToE N v)).toCLM u =
      fderiv ℝ K (S.headToE N v) (S.incl u) :=
    fun u => congrArg (fun f => f u) (S.hsDerivH_toCLM K (S.headToE N v))
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2,
    S.starProjection_head, S.fderiv_truncField K hK N v,
    ← S.headToE_apply N w]
  rfl

/-- The realization has the sample as its coordinates (the a.e. property used throughout). -/
def RealizesCoords (z : ℤ → ℂ) : Prop :=
  ∀ n : ℤ, S.coord n (S.R z) = z n

theorem tendsto_finiteDet2_truncField
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K)
    (z : ℤ → ℂ) (hz : S.RealizesCoords z) :
    Tendsto (fun N => finiteDet2 (fderiv ℝ (S.truncField K N) (S.headPt N z))) atTop
      (𝓝 (det2 (S.hsDerivH K (S.R z)))) := by
  have hxs := S.tendsto_headToE_headPt z hz
  have hA : Tendsto (fun N => S.hsDerivH K (S.headToE N (S.headPt N z))) atTop
      (𝓝 (S.hsDerivH K (S.R z))) :=
    ((S.continuous_hsDerivH K (hK.of_le (by norm_num))).tendsto _).comp hxs
  have h := Analysis.RegularizedDeterminant.tendsto_finiteSection_finiteDet2 atTop
    (fun N => S.head N) S.tendsto_starProjection_head _ _ hA
  refine h.congr (fun N => ?_)
  rw [S.restrictedEnd_eq_fderiv_truncField K hK N (S.headPt N z), finiteDet2_eq_analysis]

theorem tendsto_norm_truncField
    (K : S.E → S.H) (hK : Continuous K)
    (z : ℤ → ℂ) (hz : S.RealizesCoords z) :
    Tendsto (fun N => ‖S.truncField K N (S.headPt N z)‖) atTop
      (𝓝 ‖K (S.R z)‖) := by
  have h := S.tendsto_cmTrunc_comp K hK _ _ (S.tendsto_headToE_headPt z hz)
  exact h.norm

/-! ### Local divergence convergence -/

theorem measurable_cylDiv_truncField
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K) (N : ℕ) :
    Measurable (fun z => S.cylDiv N (S.truncField K N) z) :=
  (continuous_finiteGaussianDivergence
    ((S.contDiff_truncField K hK N).of_le (by norm_num))).measurable.comp
    (S.measurable_headPt N)

/-- Local data around a point: a bounded `C²` field `G` equal to `K` on a ball, with the
`L²(γ)` limit `η` of the cylindrical divergences of its truncations, which is a closed divergence
of `G ∘ R`. -/
theorem exists_local_truncDiv
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K)
    (x₀ : S.E) :
    ∃ r > 0, ∃ (G : S.E → S.H) (η : (ℤ → ℂ) → ℝ),
      Set.EqOn G K (Metric.ball x₀ r) ∧ ContDiff ℝ 2 G ∧
      S.IsClosedDiv (fun z => G (S.R z)) η ∧
      Tendsto (fun N => eLpNorm (fun z => S.cylDiv N (S.truncField G N) z - η z) 2 S.γ)
        atTop (𝓝 0) := by
  obtain ⟨r, hr, hKb, hDb⟩ := exists_local_radius_bounds K hK x₀
  obtain ⟨-, -, -, -, -, -, G, B, -, hGd, hGv, hGD, hEq⟩ :=
    S.exists_bumped_field_radius K hK x₀ hr _ _ hKb hDb
  obtain ⟨η, hη, hv2⟩ := S.exists_tendsto_cylDiv_truncField G hGd B hGv hGD
  exact ⟨r, hr, G, η, hEq, hGd, S.isClosedDiv_of_tendsto_truncField G hGd B hGv hGD η hη hv2,
    hv2⟩

/-- On a ball where `G = K`, the cylindrical divergences of the truncations eventually agree. -/
theorem eventually_cylDiv_truncField_eq
    (K G : S.E → S.H) {x₀ : S.E} {r : ℝ}
    (hEq : Set.EqOn G K (Metric.ball x₀ r)) (z : ℤ → ℂ) (hz : S.RealizesCoords z)
    (hzr : S.R z ∈ Metric.ball x₀ r) :
    ∀ᶠ N in atTop, S.cylDiv N (S.truncField K N) z = S.cylDiv N (S.truncField G N) z := by
  have hxs := S.tendsto_headToE_headPt z hz
  filter_upwards [hxs.eventually (Metric.isOpen_ball.mem_nhds hzr)] with N hN
  unfold cylDiv
  refine finiteGaussianDivergence_congr_of_eventuallyEq ?_
  have hU : IsOpen ((S.headToE N) ⁻¹' Metric.ball x₀ r) :=
    Metric.isOpen_ball.preimage (S.headToE N).continuous
  filter_upwards [hU.mem_nhds hN] with w hw
  unfold truncField
  rw [hEq hw]

/-- Convergence in measure of the cylindrical divergences on one patch. -/
theorem tendstoInMeasure_indicator_cylDiv
    (K G : S.E → S.H)
    (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G) {x₀ : S.E} {r : ℝ}
    (hEq : Set.EqOn G K (Metric.ball x₀ r)) (δK η : (ℤ → ℂ) → ℝ)
    (hδη : ∀ᵐ z ∂S.γ, S.R z ∈ Metric.ball x₀ r → δK z = η z)
    (hL : Tendsto (fun N => eLpNorm (fun z => S.cylDiv N (S.truncField G N) z - η z) 2
      S.γ) atTop (𝓝 0)) :
    TendstoInMeasure S.γ
      (fun N => (S.R ⁻¹' Metric.ball x₀ r).indicator
        (fun z => S.cylDiv N (S.truncField K N) z - δK z)) atTop (fun _ => (0 : ℝ)) := by
  set γ := S.γ with hγ
  set R := S.R with hR
  set A : Set (ℤ → ℂ) := R ⁻¹' Metric.ball x₀ r with hA
  have hRm : Measurable R := S.measurable_R
  have hAm : MeasurableSet A := hRm Metric.isOpen_ball.measurableSet
  have hv : TendstoInMeasure γ (fun N => A.indicator
      (fun z => S.cylDiv N (S.truncField G N) z - η z)) atTop (fun _ => (0 : ℝ)) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL (fun N => zero_le)
      (fun N => ?_)
    have h : (A.indicator (fun z => S.cylDiv N (S.truncField G N) z - η z) -
        fun _ => (0 : ℝ)) = A.indicator (fun z => S.cylDiv N (S.truncField G N) z - η z) := by
      funext z; simp
    rw [h]
    exact eLpNorm_indicator_le (p := 2) (μ := γ)
      (fun z => S.cylDiv N (S.truncField G N) z - η z) hAm
  have hw : TendstoInMeasure γ (fun N => A.indicator
      (fun z => S.cylDiv N (S.truncField K N) z - S.cylDiv N (S.truncField G N) z)) atTop
      (fun _ => (0 : ℝ)) := by
    have hmeas : ∀ N, Measurable (A.indicator
        (fun z => S.cylDiv N (S.truncField K N) z - S.cylDiv N (S.truncField G N) z)) :=
      fun N => ((S.measurable_cylDiv_truncField K hK N).sub
        (S.measurable_cylDiv_truncField G hG N)).indicator hAm
    refine tendstoInMeasure_of_tendsto_ae (fun N => (hmeas N).aestronglyMeasurable) ?_
    filter_upwards [S.coord_R_ae] with z hz
    by_cases hzA : z ∈ A
    · have := S.eventually_cylDiv_truncField_eq K G hEq z hz hzA
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
theorem tendstoInMeasure_cylDiv_truncField
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K)
    (δK : (ℤ → ℂ) → ℝ)
    (hδK : ∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (Metric.ball x₀ r) →
        S.IsClosedDiv (fun z => G (S.R z)) η →
        ∀ᵐ z ∂S.γ, S.R z ∈ Metric.ball x₀ r → δK z = η z) :
    TendstoInMeasure S.γ
      (fun N z => S.cylDiv N (S.truncField K N) z) atTop δK := by
  classical
  set γ := S.γ with hγ
  set R := S.R with hR
  have hRm : Measurable R := S.measurable_R
  choose r hr G η hEq hGd hCD hL using S.exists_local_truncDiv K hK
  obtain ⟨T, hTc, hTcov⟩ := S.exists_countable_cover_balls r hr
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
  exact S.tendstoInMeasure_indicator_cylDiv K (G (xk k)) hK (hGd (xk k)) (hEq (xk k)) δK
    (η (xk k)) (hδK (xk k) (r (xk k)) (G (xk k)) (η (xk k)) (hEq (xk k)) (hCD (xk k)))
    (hL (xk k))

/-- **Cylindrical Ramer densities converge in probability to `J_T`** (v2, `prop:gaussiancommon`,
`eq:cylindricalcommon`, via `lem:determinants`).  With `x_N = P_N x`, `T_N = id + P_N K(P_N ·)` on
`V_N`, the density `J_N = |det DT_N(x_N)| exp(-(‖T_N x_N‖² - ‖x_N‖²)/2)` converges in
`γ`-probability to `J_K = |det₂(I + D_H K)| exp(-δK - ‖K‖²_H/2)`, for any `δK` satisfying the
locality clause (clause 3) of `divergence_identification`. -/
theorem tendstoInMeasure_cylindricalDensity
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K)
    (δK : (ℤ → ℂ) → ℝ)
    (hδK : ∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H)
        (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (Metric.ball x₀ r) →
        S.IsClosedDiv (fun z => G (S.R z)) η →
        ∀ᵐ z ∂S.γ, S.R z ∈ Metric.ball x₀ r → δK z = η z) :
    TendstoInMeasure S.γ
      (fun N z => finiteRamerDensity (fun v => v + S.truncField K N v) (S.headPt N z))
      atTop (S.ramerJ K δK) := by
  set γ := S.γ with hγ
  have hmeas : ∀ N, AEStronglyMeasurable (fun z =>
      finiteRamerDensity (fun v => v + S.truncField K N v) (S.headPt N z)) γ := by
    intro N
    refine (Measurable.aestronglyMeasurable ?_)
    refine (measurable_finiteRamerDensity_of_continuous _ ?_).comp (S.measurable_headPt N)
    exact continuous_id.add (S.contDiff_truncField K hK N).continuous
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  have hdiv := (S.tendstoInMeasure_cylDiv_truncField K hK δK hδK).comp hns.tendsto_atTop
  obtain ⟨ns', hns', hae⟩ := hdiv.exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  have hsub : Tendsto (fun i => ns (ns' i)) atTop atTop := hns.tendsto_atTop.comp hns'.tendsto_atTop
  filter_upwards [hae, S.coord_R_ae] with z hd hz
  have hD := (S.tendsto_finiteDet2_truncField K hK z hz).comp hsub
  have hn := (S.tendsto_norm_truncField K hK.continuous z hz).comp hsub
  have hlim := hD.abs.mul (Real.continuous_exp.tendsto _ |>.comp (hd.neg.sub ((hn.pow 2).div_const 2)))
  unfold ramerJ
  refine hlim.congr (fun i => ?_)
  simp only [Function.comp]
  rw [S.finiteRamerDensity_truncField K hK]
  rfl

/-- **Composed form.** The divergence `δK` of `divergence_identification` (measurable, locally
equal to closed divergences, independent of localization) satisfies the convergence
`J_N → J_K` in probability. -/
theorem exists_cylindricalDensity_limit
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      AEStronglyMeasurable δK S.γ ∧
      (∀ (x₀ : S.E) (r : ℝ) (G : S.E → S.H)
          (η : (ℤ → ℂ) → ℝ), Set.EqOn G K (Metric.ball x₀ r) →
          S.IsClosedDiv (fun z => G (S.R z)) η →
          ∀ᵐ z ∂S.γ, S.R z ∈ Metric.ball x₀ r → δK z = η z) ∧
      TendstoInMeasure S.γ
        (fun N z => finiteRamerDensity (fun v => v + S.truncField K N v) (S.headPt N z))
        atTop (S.ramerJ K δK) := by
  obtain ⟨δK, hm, -, h3, -, -⟩ := S.divergence_identification K hK
  exact ⟨δK, hm, h3, S.tendstoInMeasure_cylindricalDensity K hK δK h3⟩

end NlsGge.Ramer.General.RamerSetting
