/- I-043 TRANSPORT PRODUCTION04 (codex_luna16, AUTHOR; not worker-compiled).
   Intended target: NlsGge/ThirdConsultation/I/I043Transport.lean.
   Proof repairs from the root MAINPROBE02 diagnostics only; all exported
   statement heads from PRODUCTION02 are unchanged. -/
import Mathlib
import NlsGge.Atomic.F.F032
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.ThirdConsultation.I.FiniteOrderLaw

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.SpectralFoundations
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.I

/-- The source-compatible Fourier field law, expressed in `H^r` coordinates. -/
abbrev finiteOrderFourierLaw (c : ℕ → ℝ) (r m N : ℕ) :
    Measure (SobolevHilbert (r : ℝ)) :=
  nuBareS38 m (coefficient c) N (r : ℝ)

private theorem i043_coefficient_pos {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (j : ℕ) :
    0 < coefficient c.val j :=
  NlsGge.Weights.coefficient_pos lower c.val c.property.1
    (fun i => (c.property.2.2 i).1) j

private theorem i043_weight_le (k r : ℕ) (hr : r < k) :
    ∀ n : ℤ, sobolevModeWeight (r : ℝ) n ≤
      1 * sobolevModeWeight ((k - 1 : ℕ) : ℝ) n := by
  have hrk : r ≤ k - 1 := by omega
  have hrk' : (r : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrk
  intro n
  unfold sobolevModeWeight
  rw [one_mul]
  exact Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le n) (by nlinarith)

private def i043_sobolevInclusion (k r : ℕ) (hr : r < k) :
    Hm1 k →L[ℝ] SobolevHilbert (r : ℝ) :=
  weightedRealComparisonContinuous
    (sobolevModeWeight ((k - 1 : ℕ) : ℝ)) (sobolevModeWeight (r : ℝ))
    1 (by norm_num) (i043_weight_le k r hr)

private theorem i043_reSob_eq_inclusion (k r : ℕ) (hr : r < k)
    (u : Hm1 k) :
    reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) u = i043_sobolevInclusion k r hr u := by
  apply coeffSeq38_injective (r : ℝ)
  funext n
  have hrk : r ≤ k - 1 := by omega
  have hrk' : (r : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrk
  have hsource :
      coeffSeq38 ((k - 1 : ℕ) : ℝ) u ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ) :=
    (mem_seqSobolev38_iff _ _).2 (summable_coeffSeq38 _ _)
  have hsum := (mem_seqSobolev38_iff _ _).1 (seqSobolev38_mono hrk' hsource)
  rw [coeffSeq_reSob38 _ _ _ hsum n]
  change (show WeightedHilbert (sobolevModeWeight ((k - 1 : ℕ) : ℝ)) from u) n =
    (show WeightedHilbert (sobolevModeWeight (r : ℝ)) from
      i043_sobolevInclusion k r hr u) n
  exact (weightedRealComparison_apply
    (sobolevModeWeight ((k - 1 : ℕ) : ℝ)) (sobolevModeWeight (r : ℝ))
    1 (by norm_num) (i043_weight_le k r hr) u n).symm

theorem i043_reSob_eq_physFS_sobolevToL2 (k r : ℕ) (hr : r < k)
    (u : Hm1 k) :
    reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) u =
      physFS38 r (sobolevToL2_38 (k - 1) u) := by
  apply coeffSeq38_injective (r : ℝ)
  funext n
  have hrk : r ≤ k - 1 := by omega
  have hrk' : (r : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrk
  have hsource :
      coeffSeq38 ((k - 1 : ℕ) : ℝ) u ∈ seqSobolev38 ((k - 1 : ℕ) : ℝ) :=
    (mem_seqSobolev38_iff _ _).2 (summable_coeffSeq38 _ _)
  have hsum := (mem_seqSobolev38_iff _ _).1 (seqSobolev38_mono hrk' hsource)
  have hphysHigh : SobolevSquareSummable ((k - 1 : ℕ) : ℝ)
      (physicalFourier (sobolevToL2_38 (k - 1) u)) :=
    sobolevToL2_38_sobolev (k - 1) u
  have hphysLow : SobolevSquareSummable (r : ℝ)
      (physicalFourier (sobolevToL2_38 (k - 1) u)) := by
    exact (mem_seqSobolev38_iff _ _).1
      (seqSobolev38_mono hrk' ((mem_seqSobolev38_iff _ _).2 hphysHigh))
  rw [coeffSeq_reSob38 _ _ _ hsum n,
    coeffSeq_physFS38 r _ hphysLow n,
    sobolevToL2_38_fourier]
  rfl

theorem i043_reSob_planeElement (k r N : ℕ) (hr : r < k)
    (z : FourierPlane N) :
    reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ)
        (planeElement38 ((k - 1 : ℕ) : ℝ) N z) = planeElement38 (r : ℝ) N z := by
  apply coeffSeq38_injective (r : ℝ)
  funext n
  have hrk : r ≤ k - 1 := by omega
  have hrk' : (r : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrk
  have hsource :
      coeffSeq38 ((k - 1 : ℕ) : ℝ)
        (planeElement38 ((k - 1 : ℕ) : ℝ) N z) ∈
        seqSobolev38 ((k - 1 : ℕ) : ℝ) :=
    (mem_seqSobolev38_iff _ _).2
      (summable_coeffSeq38 _ (planeElement38 ((k - 1 : ℕ) : ℝ) N z))
  have hsum := (mem_seqSobolev38_iff _ _).1 (seqSobolev38_mono hrk' hsource)
  rw [coeffSeq_reSob38 _ _ _ hsum n]
  change
    (show WeightedHilbert (sobolevModeWeight ((k - 1 : ℕ) : ℝ)) from
      planeElement38 ((k - 1 : ℕ) : ℝ) N z) n =
    (show WeightedHilbert (sobolevModeWeight (r : ℝ)) from
      planeElement38 (r : ℝ) N z) n
  exact (planeElement_hsource38 ((k - 1 : ℕ) : ℝ) N z n).trans
    (planeElement_hsource38 (r : ℝ) N z n).symm

private theorem i043_measurable_planeElement (r N : ℕ) :
    Measurable (planeElement38 (r : ℝ) N) := by
  change Measurable (finiteElement38 (r : ℝ) (modeIndex N))
  exact measurable_finiteElement38 (r : ℝ) (modeIndex N)

theorem i043_map_nuBare38_reSob (k r N : ℕ) (hr : r < k)
    (β : ℕ → ℝ) :
    (nuBare38 k β N).map (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ)) =
      nuBareS38 k β N (r : ℝ) := by
  rw [nuBare38_eq_nuBareS38]
  unfold nuBareS38
  rw [Measure.map_map (measurable_reSob38 _ _)
    (i043_measurable_planeElement (k - 1) N)]
  congr 1
  funext z
  exact i043_reSob_planeElement k r N hr z

theorem i043_map_finiteGapLaw_reSob (lower upper : ℝ)
    (c : BoundedCoefficients lower upper) (k r : ℕ) (hr : r < k) :
    (NlsGge.ThirdConsultation.F.finiteGapLaw k (coefficient c.val)).map
        (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ)) =
      finiteOrderLaw c.val r k := by
  rw [finiteOrderLaw]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall
    (fun u => i043_reSob_eq_physFS_sobolevToL2 k r hr u)

theorem i043_isProbabilityMeasure_finiteOrderFourierLaw
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (k r N : ℕ) (hk : 2 ≤ k) :
    IsProbabilityMeasure (finiteOrderFourierLaw c.val r k N) := by
  change IsProbabilityMeasure (nuBareS38 k (coefficient c.val) N (r : ℝ))
  exact NlsGge.Birkhoff.isProbabilityMeasure_nuBareS38 hk
    (fun j hj => i043_coefficient_pos c j) N (r : ℝ)

theorem i043_isProbabilityMeasure_finiteOrderLaw
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (k r : ℕ) (hk : 2 ≤ k) :
    IsProbabilityMeasure (finiteOrderLaw c.val r k) := by
  have hβ : ∀ j ≤ k, 0 < coefficient c.val j :=
    fun j hj => i043_coefficient_pos c j
  have h032 := NlsGge.ThirdConsultation.F.f032 k hk (coefficient c.val) hβ
  have hmeas : Measurable (fun u : Hm1 k =>
      physFS38 r (sobolevToL2_38 (k - 1) u)) :=
    (measurable_physFS38 r).comp (sobolevToL2_38 (k - 1)).continuous.measurable
  change IsProbabilityMeasure
    ((NlsGge.ThirdConsultation.F.finiteGapLaw k (coefficient c.val)).map
      (fun u => physFS38 r (sobolevToL2_38 (k - 1) u)))
  exact (Measure.isProbabilityMeasure_map_iff hmeas.aemeasurable).2 h032.2.2.1

theorem i043_finiteOrderFourierLaw_tendsto_integral
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (k r : ℕ) (hk : 2 ≤ k) (hr : r < k)
    (F : SobolevHilbert (r : ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ =>
      ∫ u, F u ∂finiteOrderFourierLaw c.val r k N) atTop
      (𝓝 (∫ u, F u ∂finiteOrderLaw c.val r k)) := by
  have hβ : ∀ j ≤ k, 0 < coefficient c.val j :=
    fun j hj => i043_coefficient_pos c j
  have h032 := NlsGge.ThirdConsultation.F.f032 k hk (coefficient c.val) hβ
  rcases h032 with ⟨_, _, _, _, hF032⟩
  let inclusion : ContinuousMap (Hm1 k) (SobolevHilbert (r : ℝ)) :=
    ⟨⇑(i043_sobolevInclusion k r hr),
      (i043_sobolevInclusion k r hr).continuous⟩
  let G : Hm1 k →ᵇ ℝ := F.compContinuous inclusion
  have hG : (fun u : Hm1 k => F (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) u)) =
      fun u => G u := by
    funext u
    change F (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ) u) =
      F (i043_sobolevInclusion k r hr u)
    exact congrArg F (i043_reSob_eq_inclusion k r hr u)
  have hsource : Tendsto
      (fun N : ℕ => ∫ u, G u ∂nuBare38 k (coefficient c.val) N) atTop
      (𝓝 (∫ u, G u ∂NlsGge.ThirdConsultation.F.finiteGapLaw k
        (coefficient c.val))) := (hF032 G).2.2
  have hmeas : Measurable (reSob38 ((k - 1 : ℕ) : ℝ) (r : ℝ)) :=
    measurable_reSob38 _ _
  have hFmeas : Measurable (fun x : SobolevHilbert (r : ℝ) => F x) :=
    F.continuous.measurable
  have hleft : ∀ N : ℕ,
      (∫ u, F u ∂finiteOrderFourierLaw c.val r k N) =
        ∫ u, G u ∂nuBare38 k (coefficient c.val) N := by
    intro N
    unfold finiteOrderFourierLaw
    rw [← i043_map_nuBare38_reSob k r N hr (coefficient c.val),
      integral_map hmeas.aemeasurable hFmeas.aestronglyMeasurable, hG]
  have hright :
      (∫ u, F u ∂finiteOrderLaw c.val r k) =
        ∫ u, G u ∂NlsGge.ThirdConsultation.F.finiteGapLaw k
          (coefficient c.val) := by
    rw [← i043_map_finiteGapLaw_reSob lower upper c k r hr,
      integral_map hmeas.aemeasurable hFmeas.aestronglyMeasurable, hG]
  have hseq :
      (fun N : ℕ => ∫ u, F u ∂finiteOrderFourierLaw c.val r k N) =
        fun N => ∫ u, G u ∂nuBare38 k (coefficient c.val) N := by
    funext N
    exact hleft N
  rw [hseq, hright]
  exact hsource

end NlsGge.ThirdConsultation.I

end
