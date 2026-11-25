                                                                                        
                                                                                           
import Mathlib

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace NlsGge.ThirdConsultation.I

/-- The standard bounded-Lipschitz metric on probability measures. This formula
    is used only after the two measures are shown to be probabilities. -/
def boundedLipschitzDistance {α : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  sSup {a : ℝ | ∃ f : α →ᵇ ℝ, ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧
    a = |(∫ x, f x ∂μ) - ∫ x, f x ∂ν|}


namespace I043BLAux

/-- Probability makes the literal defining set nonempty and bounded above. -/
theorem testValues_bounds {alpha : Type*} [PseudoMetricSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    (mu nu : Measure alpha) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (0 : ℝ) ∈ {a : ℝ | ∃ f : alpha →ᵇ ℝ, ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧
      a = |(∫ x, f x ∂mu) - ∫ x, f x ∂nu|} ∧
    BddAbove {a : ℝ | ∃ f : alpha →ᵇ ℝ, ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧
      a = |(∫ x, f x ∂mu) - ∫ x, f x ∂nu|} := by
  constructor
  · refine ⟨0, by simp, ?_, by simp⟩
    exact LipschitzWith.const' (0 : ℝ)
  · refine ⟨2, ?_⟩
    rintro a ⟨f, hf, _, rfl⟩
    have hfi : Integrable f mu := f.integrable mu
    have hfj : Integrable f nu := f.integrable nu
    calc
      |(∫ x, f x ∂mu) - ∫ x, f x ∂nu| ≤
          |∫ x, f x ∂mu| + |∫ x, f x ∂nu| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_integral_le_norm mu)
        (f.norm_integral_le_norm nu)
      _ ≤ 2 := by linarith only [hf]

/-- One compact set controls the sequence and its limit; this statement is topological. -/
theorem common_compact {alpha : Type*} [TopologicalSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha] [PolishSpace alpha]
    (mu : ℕ → Measure alpha) (nu : Measure alpha)
    (hmu : ∀ N : ℕ, IsProbabilityMeasure (mu N)) (hnu : IsProbabilityMeasure nu)
    (hweak : ∀ F : alpha →ᵇ ℝ,
      Tendsto (fun N : ℕ => ∫ x, F x ∂mu N) atTop (𝓝 (∫ x, F x ∂nu)))
    (delta : ℝ) (hd : 0 < delta) :
    ∃ K : Set alpha, IsCompact K ∧
      (∀ N : ℕ, (mu N).real Kᶜ ≤ delta) ∧ nu.real Kᶜ ≤ delta := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable alpha
  let p : ℕ → ProbabilityMeasure alpha := fun N => ⟨mu N, hmu N⟩
  let q : ProbabilityMeasure alpha := ⟨nu, hnu⟩
  have hp : Tendsto p atTop (𝓝 q) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  have hc : IsCompact (closure (insert q (range p))) := by
    rw [hp.isCompact_insert_range.isClosed.closure_eq]
    exact hp.isCompact_insert_range
  have ht := isTightMeasureSet_of_isCompact_closure hc
  obtain ⟨K, hK, hmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
      (ENNReal.ofReal delta) (ENNReal.ofReal_pos.mpr hd)
  refine ⟨K, hK, fun N => ?_, ?_⟩
  · apply ENNReal.toReal_le_of_le_ofReal hd.le
    exact hmass (mu N) ⟨p N, mem_insert_of_mem q (mem_range_self N), rfl⟩
  · apply ENNReal.toReal_le_of_le_ofReal hd.le
    exact hmass nu ⟨q, mem_insert q (range p), rfl⟩

/-- A finite compact-domain net whose centers are original global admissible tests. -/
theorem finite_test_net {alpha : Type*} [MetricSpace alpha]
    (K : Set alpha) (hK : IsCompact K) (delta : ℝ) (hd : 0 < delta) :
    ∃ t : Set (alpha →ᵇ ℝ), t.Finite ∧
      (∀ g ∈ t, ‖g‖ ≤ 1 ∧ LipschitzWith 1 g) ∧
      ∀ f : alpha →ᵇ ℝ, ‖f‖ ≤ 1 → LipschitzWith 1 f →
        ∃ g ∈ t, ∀ x ∈ K, |f x - g x| ≤ delta := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A : Set (K →ᵇ ℝ) :=
    (fun f : alpha →ᵇ ℝ => f.domRestrict K) ''
      {f : alpha →ᵇ ℝ | ‖f‖ ≤ 1 ∧ LipschitzWith 1 f}
  have hrange : ∀ (f : K →ᵇ ℝ) (x : K), f ∈ A → f x ∈ Icc (-1) 1 := by
    rintro f x ⟨g, hg, rfl⟩
    exact abs_le.mp ((g.norm_coe_le_norm x).trans hg.1)
  have hequi : Equicontinuous ((↑) : A → K → ℝ) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    rintro x y ⟨f, hf⟩
    obtain ⟨g, hg, rfl⟩ := hf
    simpa only [id_eq, BoundedContinuousFunction.domRestrict_apply,
      Subtype.dist_eq, NNReal.coe_one, one_mul] using
      hg.2.dist_le_mul (x : alpha) (y : alpha)
  have hcomp : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-1) 1) isCompact_Icc A hrange hequi
  obtain ⟨s, hsA, hsfin, hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hcomp hd
  choose G hG using (fun g : s => hsA g.property)
  letI : Finite s := hsfin.to_subtype
  refine ⟨G '' (univ : Set s), (Set.finite_univ.image G), ?_, ?_⟩
  · rintro g ⟨a, _, rfl⟩
    exact (hG a).1
  · intro f hf hlip
    have hfA : f.domRestrict K ∈ A := ⟨f, ⟨hf, hlip⟩, rfl⟩
    obtain ⟨g, hgs, hfg⟩ := mem_iUnion₂.mp (hcover hfA)
    let a : s := ⟨g, hgs⟩
    refine ⟨G a, ⟨a, mem_univ a, rfl⟩, fun x hx => ?_⟩
    have hdist : dist (f.domRestrict K) ((G a).domRestrict K) < delta := by
      have hGa : (G a).domRestrict K = g := (hG a).2
      rw [hGa]
      exact hfg
    exact (BoundedContinuousFunction.dist_coe_le_dist
      (f := f.domRestrict K) (g := (G a).domRestrict K) ⟨x, hx⟩).trans hdist.le

/-- Compact error plus complement mass controls a difference of test integrals. -/
theorem integral_error_of_compact {alpha : Type*} [MetricSpace alpha]
    [MeasurableSpace alpha] [BorelSpace alpha]
    (mu : Measure alpha) [IsProbabilityMeasure mu]
    (K : Set alpha) (hK : IsCompact K) (f g : alpha →ᵇ ℝ)
    (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) (delta : ℝ) (hd : 0 ≤ delta)
    (hclose : ∀ x ∈ K, |f x - g x| ≤ delta) (htail : mu.real Kᶜ ≤ delta) :
    |(∫ x, f x ∂mu) - ∫ x, g x ∂mu| ≤ 3 * delta := by
  have hfi : Integrable f mu := f.integrable mu
  have hgi : Integrable g mu := g.integrable mu
  have hi : Integrable (fun x => f x - g x) mu := hfi.sub hgi
  have hglobal (x : alpha) : ‖f x - g x‖ ≤ 2 := by
    calc
      ‖f x - g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add ((f.norm_coe_le_norm x).trans hf)
        ((g.norm_coe_le_norm x).trans hg)
      _ = 2 := by norm_num
  have hinside : ‖∫ x in K, f x - g x ∂mu‖ ≤ delta * mu.real K :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top mu K) hclose
  have houtside : ‖∫ x in Kᶜ, f x - g x ∂mu‖ ≤ 2 * mu.real Kᶜ :=
    norm_setIntegral_le_of_norm_le_const (measure_lt_top mu Kᶜ) (fun x _ => hglobal x)
  calc
    |(∫ x, f x ∂mu) - ∫ x, g x ∂mu| = ‖∫ x, f x - g x ∂mu‖ := by
      rw [integral_sub hfi hgi]
      rfl
    _ = ‖(∫ x in K, f x - g x ∂mu) + ∫ x in Kᶜ, f x - g x ∂mu‖ := by
      rw [integral_add_compl hK.isClosed.measurableSet hi]
    _ ≤ ‖∫ x in K, f x - g x ∂mu‖ + ‖∫ x in Kᶜ, f x - g x ∂mu‖ :=
      norm_add_le _ _
    _ ≤ delta * mu.real K + 2 * mu.real Kᶜ := add_le_add hinside houtside
    _ ≤ delta * 1 + 2 * delta := add_le_add
      (mul_le_mul_of_nonneg_left measureReal_le_one hd)
      (mul_le_mul_of_nonneg_left htail (by norm_num))
    _ = 3 * delta := by ring

end I043BLAux

theorem boundedLipschitzDistance_tendsto_zero_of_weak
    {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha]
    [BorelSpace alpha] [PolishSpace alpha]
    (mu : ℕ → Measure alpha) (nu : Measure alpha)
    (hmu : ∀ N : ℕ, IsProbabilityMeasure (mu N))
    (hnu : IsProbabilityMeasure nu)
    (hweak : ∀ F : alpha →ᵇ ℝ,
      Tendsto (fun N : ℕ => ∫ x, F x ∂mu N) atTop
        (𝓝 (∫ x, F x ∂nu))) :
    Tendsto (fun N : ℕ => I.boundedLipschitzDistance (mu N) nu) atTop (𝓝 0) := by
  letI : ∀ N, IsProbabilityMeasure (mu N) := hmu
  letI : IsProbabilityMeasure nu := hnu
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun N => by
      obtain ⟨hz, hb⟩ := I043BLAux.testValues_bounds (mu N) nu
      have hne : Set.Nonempty {b : ℝ | ∃ f : alpha →ᵇ ℝ,
          ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧
          b = |(∫ x, f x ∂mu N) - ∫ x, f x ∂nu|} := ⟨0, hz⟩
      exact ha.trans_le (le_csSup hb hz)
  · intro eps heps
    let delta : ℝ := eps / 8
    have hd : 0 < delta := div_pos heps (by norm_num)
    obtain ⟨K, hK, hmuK, hnuK⟩ :=
      I043BLAux.common_compact mu nu hmu hnu hweak delta hd
    obtain ⟨t, htfin, htgood, hnet⟩ := I043BLAux.finite_test_net K hK delta hd
    have hfinite : ∀ᶠ N : ℕ in atTop, ∀ g ∈ t,
        |(∫ x, g x ∂mu N) - ∫ x, g x ∂nu| < delta := by
      apply htfin.eventually_all.mpr
      intro g _
      have hg : Tendsto (fun N : ℕ => |(∫ x, g x ∂mu N) - ∫ x, g x ∂nu|)
          atTop (𝓝 0) := by
        have hconst : Tendsto (fun _ : ℕ => ∫ x, g x ∂nu) atTop
            (𝓝 (∫ x, g x ∂nu)) := tendsto_const_nhds
        simpa only [sub_self, abs_zero] using ((hweak g).sub hconst).abs
      exact (tendsto_order.mp hg).2 delta hd
    filter_upwards [hfinite] with N hN
    obtain ⟨hz, hb⟩ := I043BLAux.testValues_bounds (mu N) nu
    have hne : Set.Nonempty {b : ℝ | ∃ f : alpha →ᵇ ℝ,
        ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧
        b = |(∫ x, f x ∂mu N) - ∫ x, f x ∂nu|} := ⟨0, hz⟩
    have hsup : I.boundedLipschitzDistance (mu N) nu ≤ 7 * delta := by
      apply csSup_le hne
      rintro a ⟨f, hf, hlip, rfl⟩
      obtain ⟨g, hgt, hfg⟩ := hnet f hf hlip
      have hmuErr := I043BLAux.integral_error_of_compact
        (mu N) K hK f g hf (htgood g hgt).1 delta hd.le hfg (hmuK N)
      have hnuErr := I043BLAux.integral_error_of_compact
        nu K hK g f (htgood g hgt).1 hf delta hd.le
        (fun x hx => by simpa only [abs_sub_comm] using hfg x hx) hnuK
      calc
        |(∫ x, f x ∂mu N) - ∫ x, f x ∂nu| ≤
            |(∫ x, f x ∂mu N) - ∫ x, g x ∂mu N| +
            |(∫ x, g x ∂mu N) - ∫ x, f x ∂nu| := abs_sub_le _ _ _
        _ ≤ |(∫ x, f x ∂mu N) - ∫ x, g x ∂mu N| +
            (|(∫ x, g x ∂mu N) - ∫ x, g x ∂nu| +
            |(∫ x, g x ∂nu) - ∫ x, f x ∂nu|) :=
          add_le_add le_rfl (abs_sub_le
            (∫ x, g x ∂mu N) (∫ x, g x ∂nu) (∫ x, f x ∂nu))
        _ ≤ 3 * delta + (delta + 3 * delta) :=
          add_le_add hmuErr (add_le_add (hN g hgt).le hnuErr)
        _ = 7 * delta := by ring
    exact hsup.trans_lt (by dsimp [delta]; linarith only [heps])

end NlsGge.ThirdConsultation.I

end
