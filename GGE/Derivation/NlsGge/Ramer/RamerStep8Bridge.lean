import NlsGge.Ramer.RamerStep8c
import NlsGge.Ramer.RamerJacobianHead

/-!
# Bridge: Step 8's divergence and `ramerJac`

Ramer's Step 8 (`step8b`, `step8c`) is proved with a divergence `δL` produced inside
`step8b_divergence`: an a.e. limit of `ramerA (φ j) L` along a subsequence `φ`. Lemma 5.4
(R9a/R9c) works with `ramerJac L = ramerJE L (ramerDiv L)`, where `ramerDiv L` is the choice
made in `divergence_identification`, which is the limit in measure of the whole sequence `ramerA n L`.

* `ae_eq_of_subseq_ae_of_tendstoInMeasure`: an a.e. limit along a subsequence agrees a.e. with
  the limit in measure of the whole sequence.
* `step8_delta_ae_eq_ramerDiv`: any such `δL` equals `ramerDiv L` `γ`-a.e.
* `ramerJE_ae_eq_of_ae_eq`: a.e.-equal divergences give `γ_E`-a.e.-equal Jacobians (via `coordE`).
* `step8c_ramerJac`: `step8c` restated for `ramerJac L`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-- A subsequence a.e. limit coincides a.e. with the in-measure limit of the full sequence. -/
theorem ae_eq_of_subseq_ae_of_tendstoInMeasure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g h : α → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun j => f (φ j) x) atTop (𝓝 (g x)))
    (hmeas : TendstoInMeasure μ f atTop h) :
    g =ᵐ[μ] h := by
  have hsub : TendstoInMeasure μ (fun j => f (φ j)) atTop h :=
    hmeas.comp hφ.tendsto_atTop
  obtain ⟨ns, hns, hns_ae⟩ := hsub.exists_seq_tendsto_ae
  filter_upwards [hae, hns_ae] with x hx1 hx2
  exact tendsto_nhds_unique (hx1.comp hns.tendsto_atTop) hx2

variable (c : BoundedCoefficients lower upper) (s : ℝ)

/-- **Bridge 1.** The Step-8 divergence (any a.e. subsequence limit of `ramerA · L`) is
`ramerDiv L` almost surely. -/
theorem step8_delta_ae_eq_ramerDiv (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s → ActualCM c) (hL : ContDiff ℝ 2 L)
    (δL : (ℤ → ℂ) → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) L z) atTop (𝓝 (δL z))) :
    δL =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] ramerDiv c s hs L := by
  have hmeas : TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val)
      (fun n => ramerA c s (zero_le_of_half_lt hs) n L) atTop (ramerDiv c s hs L) :=
    (ramerDiv_spec c s hs L hL).2.2
  exact ae_eq_of_subseq_ae_of_tendstoInMeasure
    (f := fun n => ramerA c s (zero_le_of_half_lt hs) n L) (g := δL) (h := ramerDiv c s hs L)
    hφ hlim hmeas

/-- A.e.-equal divergences give `γ_E`-a.e.-equal Jacobians. -/
theorem ramerJE_ae_eq_of_ae_eq (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s → ActualCM c) {δ δ' : (ℤ → ℂ) → ℝ}
    (h : δ =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] δ') :
    ramerJE c s hs L δ =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s] ramerJE c s hs L δ' := by
  filter_upwards [ae_of_ae_coordE c s hs h] with x hx
  rw [ramerJE_eq, ramerJE_eq, hx]

/-- **Bridge 2.** Ramer's Step 8 conclusions (positivity, (**) for sets, and null-set preservation),
stated for `ramerJac L`. -/
theorem step8c_ramerJac (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    {ε : ℝ} (hyp : Step8Hyp c s hs L ε) :
    (∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
        x ∈ closedBall (0 : FullWeightedHilbert c s) ε → 0 < ramerJac c s hs L x) ∧
      (∀ M : Set (FullWeightedHilbert c s), M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) →
        ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M,
          ENNReal.ofReal (ramerJac c s hs L x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
        NlsGge.Measure.fullWeightedSequenceGaussian c s M) ∧
      (∀ M : Set (FullWeightedHilbert c s), MeasurableSet M →
        M ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) →
        NlsGge.Measure.fullWeightedSequenceGaussian c s M = 0 →
        NlsGge.Measure.fullWeightedSequenceGaussian c s
          (closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M) = 0) := by
  obtain ⟨δL, hm, ⟨φ, hφ, hlim⟩, -⟩ := step8b_divergence c s hs L hyp
  have hEq : ramerJE c s hs L δL =ᵐ[NlsGge.Measure.fullWeightedSequenceGaussian c s]
      ramerJac c s hs L :=
    ramerJE_ae_eq_of_ae_eq c s hs L
      (step8_delta_ae_eq_ramerDiv c s hs L hyp.smooth δL φ hφ hlim)
  refine ⟨?_, ?_, fun M hMm hM h0 => step8c_null hs L hyp δL hm φ hφ hlim hMm hM h0⟩
  · filter_upwards [hEq] with x hx hxB
    rw [← hx]
    exact ramerJE_pos_closedBall c s hs L hyp δL hxB
  · intro M hM
    calc ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M,
          ENNReal.ofReal (ramerJac c s hs L x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s)
        = ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' M,
          ENNReal.ofReal (ramerJE c s hs L δL x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
          lintegral_congr_ae (ae_restrict_of_ae (hEq.mono fun x hx => by dsimp only; rw [hx]))
      _ ≤ _ := step8c_set hs L hyp δL hm φ hφ hlim hM

end NlsGge.Ramer
