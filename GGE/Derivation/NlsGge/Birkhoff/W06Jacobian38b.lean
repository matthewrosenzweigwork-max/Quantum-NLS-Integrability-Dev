import NlsGge.Birkhoff.W06Jacobian38
import NlsGge.Ramer.CameronMartinE
import NlsGge.Ramer.HypothesisBridge

/-! # W06.01-W06.02: the full-weight Gaussian `γ_W` on `E_s` (Birkhoff-free)

Source: `paper/v2.tex` l.1537-1539 (proof of `D:thm:Ramer`: Radon Gaussian on `E_s` with
Cameron-Martin space `H`, Hilbert-Schmidt inclusion `H ↪ E_s`, `s > 1/2`).

* W06.01: `γ_W` is a regular (Radon) probability measure on the Polish space `E_s` and has full
  support (`IsOpenPosMeasure`): every nonempty open set has positive measure. Proof: `H` is dense in
  `E_s` (`cmToFullWeightedHilbert_denseRange`), `γ_W` is quasi-invariant under translations by `i h`
  (`quasiMeasurePreserving_add_inclE`), and `E_s` is covered by countably many balls.
* W06.02: `‖h‖²_H = 2 ∑ a_n |h_n|²` and the inclusion `H ↪ E_s` is Hilbert-Schmidt.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory Metric NlsGge.Pilot NlsGge.Ramer Filter Topology
open scoped ENNReal

section FullSupport

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem polishSpace_fullWeighted_W06_38 : PolishSpace (FullWeightedHilbert c s) :=
  polishSpace_ECarrier38 c s

theorem regular_gammaW_W06_38 :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).Regular := by
  have := polishSpace_fullWeighted_W06_38 c s
  infer_instance

theorem ball_null_transfer_W06_38 (hs : (1 : ℝ) / 2 < s) (e : ActualCM c) (ρ : ℝ) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s (ball (inclE c s hs e) ρ) = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (ball 0 ρ) = 0) ∧
    (NlsGge.Measure.fullWeightedSequenceGaussian c s (ball 0 ρ) = 0 →
      NlsGge.Measure.fullWeightedSequenceGaussian c s (ball (inclE c s hs e) ρ) = 0) := by
  constructor
  · intro h
    have := (quasiMeasurePreserving_add_inclE c s hs e).preimage_null h
    convert this using 2
    ext x
    simp [mem_ball, dist_eq_norm]
  · intro h
    have := (quasiMeasurePreserving_sub_inclE c s hs e).preimage_null h
    convert this using 2
    ext x
    simp [mem_ball, dist_eq_norm]

theorem ball_zero_pos_W06_38 (hs : (1 : ℝ) / 2 < s) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < NlsGge.Measure.fullWeightedSequenceGaussian c s (ball 0 ρ) := by
  by_contra hcon
  have h0 : NlsGge.Measure.fullWeightedSequenceGaussian c s (ball 0 ρ) = 0 :=
    le_antisymm (not_lt.1 hcon) zero_le
  have hsep : TopologicalSpace.SeparableSpace (ActualCM c) := inferInstance
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (ActualCM c)
  have hdense : DenseRange (inclE c s hs) :=
    cmToFullWeightedHilbert_denseRange c s (zero_le_of_half_lt hs)
  have hDi : Dense ((inclE c s hs) '' D) :=
    hdense.dense_image (inclE c s hs).continuous hDd
  have hcover : (Set.univ : Set (FullWeightedHilbert c s)) ⊆ ⋃ e ∈ D, ball (inclE c s hs e) ρ := by
    intro z _
    obtain ⟨b, ⟨e, he, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 (hDi z) ρ hρ
    simp only [Set.mem_iUnion]
    exact ⟨e, he, by rw [mem_ball]; exact hb⟩
  have hnull : NlsGge.Measure.fullWeightedSequenceGaussian c s Set.univ = 0 := by
    refine measure_mono_null hcover ?_
    exact (measure_biUnion_null_iff hDc).2 fun e _ =>
      (ball_null_transfer_W06_38 c s hs e ρ).2 h0
  have h1 : NlsGge.Measure.fullWeightedSequenceGaussian c s Set.univ = 1 := measure_univ
  rw [h1] at hnull
  exact one_ne_zero hnull

theorem isOpenPosMeasure_gammaW_W06_38 (hs : (1 : ℝ) / 2 < s) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hxr⟩ := Metric.isOpen_iff.1 hU x hx
  have hdense : DenseRange (inclE c s hs) :=
    cmToFullWeightedHilbert_denseRange c s (zero_le_of_half_lt hs)
  obtain ⟨b, ⟨e, rfl⟩, he⟩ := Metric.mem_closure_iff.1 (hdense x) (r / 2) (by linarith)
  have hsub : ball (inclE c s hs e) (r / 2) ⊆ U := by
    refine subset_trans ?_ hxr
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z (inclE c s hs e) x
    rw [dist_comm (inclE c s hs e) x] at this
    linarith [he, this, hz]
  have hpos := ball_zero_pos_W06_38 c s hs (by linarith : 0 < r / 2)
  have hpos' : 0 < NlsGge.Measure.fullWeightedSequenceGaussian c s (ball (inclE c s hs e) (r / 2)) := by
    by_contra hcon
    have h0 : NlsGge.Measure.fullWeightedSequenceGaussian c s (ball (inclE c s hs e) (r / 2)) = 0 :=
      le_antisymm (not_lt.1 hcon) zero_le
    exact hpos.ne' ((ball_null_transfer_W06_38 c s hs e (r / 2)).1 h0)
  exact (lt_of_lt_of_le hpos' (measure_mono hsub)).ne'

/-- **W06.01.** `γ_W` is a regular (Radon) probability measure on the Polish space `E_s` with full
support. -/
theorem W06_01_38 (hs : (1 : ℝ) / 2 < s) :
    IsProbabilityMeasure (NlsGge.Measure.fullWeightedSequenceGaussian c s) ∧
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).Regular ∧
    (∀ U : Set (FullWeightedHilbert c s), IsOpen U → U.Nonempty →
      0 < NlsGge.Measure.fullWeightedSequenceGaussian c s U) := by
  refine ⟨inferInstance, regular_gammaW_W06_38 c s, fun U hU hne => ?_⟩
  have := isOpenPosMeasure_gammaW_W06_38 c s hs
  exact pos_iff_ne_zero.2 (hU.measure_ne_zero _ hne)

/-- **W06.02.** The Cameron-Martin norm is `‖h‖²_H = 2 ∑ a_n |h_n|²`, and the inclusion
`H ↪ E_s` is Hilbert-Schmidt (`s > 1/2`), with squared HS norm `∑ ⟨n⟩^{-2s}`. -/
theorem W06_02_38 (hs : (1 : ℝ) / 2 < s) :
    (∀ h : ActualCM c, ‖h‖ ^ 2 = 2 * ∑' n : ℤ, sourceRate c n * ‖cmCoord h n‖ ^ 2) ∧
    ((NlsGge.Analysis.RegularizedDeterminant.cmInclusionHS c s hs).toCLM = inclE c s hs) ∧
    ‖NlsGge.Analysis.RegularizedDeterminant.cmInclusionHS c s hs‖ ^ 2 =
      ∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s) := by
  refine ⟨fun h => ?_, rfl, NlsGge.Analysis.RegularizedDeterminant.cmInclusionHS_norm_sq c s hs⟩
  rw [actualCM_norm_sq, ← tsum_mul_left]
  exact tsum_congr fun n => by unfold cmModeWeight; ring

end FullSupport

end NlsGge.Birkhoff
