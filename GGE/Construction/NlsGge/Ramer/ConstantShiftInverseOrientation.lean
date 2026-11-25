import NlsGge.Measure.ActualSourceCMFiniteScoreExplicitRNDensityV2

/-!
# Ramer formula for a constant Cameron–Martin shift on the actual source law

Let `γ = fullWeightSequenceGaussian c` be the actual countable product law and
`h = actualSourceCMSequence c x` the sequence of an actual CM vector `x`. For
`T z = z + h`, v2 `eq:Ramercommon` with `K ≡ h` reads

  `(T⁻¹)_# γ = exp(-δh - ‖h‖_H²/2) γ`,

with `det₂(I) = 1` and `δh` the Gaussian divergence of the constant field `h`,
which is the L² limit `S` of the finite CM scores. Note the NEGATIVE score. The
accepted checkpoint-20 theorem `exists_actualSourceCM_expScoreRNdensity_v2`
concerns the pushforward by `+h`, which has the positive score. This file
derives the inverse orientation by applying that theorem to `-x`. It proves the
needed linearity: the CM sequence and the finite scores are odd in `x`, and the
L² limits satisfy `S_{-x} = -S_x`.

`‖h‖_H² = Σ_n cmModeWeight c n · |h_n|²` with `cmModeWeight = 2 · sourceRate`,
which is the factor-two CM norm of v2.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer

variable {lower upper : ℝ}

theorem actualSourceCMSequence_neg (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    NlsGge.Measure.actualSourceCMSequence c (-x) =
      fun n => -NlsGge.Measure.actualSourceCMSequence c x n := by
  funext n
  rfl

theorem actualSourceCMFiniteScorePartial_neg
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (N : ℕ) (z : ℤ → ℂ) :
    NlsGge.Measure.actualSourceCMFiniteScorePartial c (-x) N z =
      -NlsGge.Measure.actualSourceCMFiniteScorePartial c x N z := by
  unfold NlsGge.Measure.actualSourceCMFiniteScorePartial
    NlsGge.Measure.actualSourceCMFiniteScoreFunctional
  rw [map_neg]
  change (2 : ℝ) • (innerSL ℝ (-(NlsGge.Pilot.cmToFullWeightedHilbert c 0 (by norm_num) x))
      (NlsGge.Measure.fullWeightedSequencePartial c 0 N z)) =
    -((2 : ℝ) • (innerSL ℝ (NlsGge.Pilot.cmToFullWeightedHilbert c 0 (by norm_num) x)
      (NlsGge.Measure.fullWeightedSequencePartial c 0 N z)))
  rw [innerSL_apply_apply, innerSL_apply_apply, inner_neg_left, smul_neg]

theorem actualSourceCMFiniteScorePartialLp_neg
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) (N : ℕ) :
    NlsGge.Measure.actualSourceCMFiniteScorePartialLp c (-x) N =
      -NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N := by
  have e : ∀ y : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c),
      (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c y N : (ℤ → ℂ) → ℝ) =ᵐ[
        NlsGge.Measure.fullWeightSequenceGaussian c.val]
        NlsGge.Measure.actualSourceCMFiniteScorePartial c y N := by
    intro y
    unfold NlsGge.Measure.actualSourceCMFiniteScorePartialLp
    exact MemLp.coeFn_toLp _
  apply Lp.ext
  filter_upwards [e (-x), e x,
    Lp.coeFn_neg (NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N)] with z h1 h2 h3
  rw [h1, h3, Pi.neg_apply, h2]
  exact actualSourceCMFiniteScorePartial_neg c x N z

/-- **Ramer formula for a constant CM shift, inverse-pushforward orientation.**
For an actual CM vector `x` with sequence `h`, the finite CM scores of `x`
converge in `L²(γ)` to a limit `S`, the Gaussian divergence of the constant
field `h`. The law of `z ↦ z - h`, which is `(T⁻¹)_# γ` for `T z = z + h`, has
density `exp(-S - ‖h‖_H²/2)`. That density is a.e.-measurable and has
ENNReal mass one. -/
theorem exists_actualSourceCM_inverseShift_negativeScoreDensity
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c)) :
    ∃ S : Lp ℝ 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun N : ℕ => NlsGge.Measure.actualSourceCMFiniteScorePartialLp c x N)
        atTop (𝓝 S) ∧
      AEMeasurable
        (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-S z -
          (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
            ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2)))
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
      (∫⁻ z : ℤ → ℂ, ENNReal.ofReal (Real.exp (-S z -
          (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
            ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2))
        ∂NlsGge.Measure.fullWeightSequenceGaussian c.val) = 1 ∧
      (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
          (fun z : ℤ → ℂ => fun n => z n - NlsGge.Measure.actualSourceCMSequence c x n) =
        (NlsGge.Measure.fullWeightSequenceGaussian c.val).withDensity
          (fun z => ENNReal.ofReal (Real.exp (-S z -
            (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
              ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2) / 2))) := by
  obtain ⟨S', hS', hmeas', hmass', hmap'⟩ :=
    NlsGge.Measure.exists_actualSourceCM_expScoreRNdensity_v2 c (-x)
  have hQ : (∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
        ‖NlsGge.Measure.actualSourceCMSequence c (-x) n‖ ^ 2) =
      ∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
        ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2 := by
    rw [actualSourceCMSequence_neg]; simp only [norm_neg]
  rw [hQ] at hmeas' hmass' hmap'
  set Q := ∑' n : ℤ, NlsGge.Pilot.cmModeWeight c n *
    ‖NlsGge.Measure.actualSourceCMSequence c x n‖ ^ 2 with hQdef
  have hae : (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (S' z - Q / 2))) =ᵐ[
      NlsGge.Measure.fullWeightSequenceGaussian c.val]
      (fun z => ENNReal.ofReal (Real.exp (-(-S' : Lp ℝ 2 _) z - Q / 2))) := by
    filter_upwards [Lp.coeFn_neg S'] with z hz
    rw [hz, Pi.neg_apply, neg_neg]
  refine ⟨-S', ?_, ?_, ?_, ?_⟩
  · have h := hS'.neg
    simp only [actualSourceCMFiniteScorePartialLp_neg, neg_neg] at h
    exact h
  · exact hmeas'.congr hae
  · rw [← lintegral_congr_ae hae]; exact hmass'
  · have hfun : (fun z : ℤ → ℂ => fun n => z n - NlsGge.Measure.actualSourceCMSequence c x n) =
        (fun z : ℤ → ℂ => fun n => z n + NlsGge.Measure.actualSourceCMSequence c (-x) n) := by
      funext z n; rw [actualSourceCMSequence_neg]; ring
    rw [hfun, hmap']
    exact withDensity_congr_ae hae

end NlsGge.Ramer
