import Mathlib
import NlsGge.ThirdConsultation.F.Round5
import NlsGge.ThirdConsultation.F.Wick018A
import NlsGge.ThirdConsultation.F.Wick018B
import NlsGge.Hierarchy.RiccatiLocalRemainderSobolev38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38

                                                                                                                   
                                                                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.Measure

namespace NlsGge.ThirdConsultation.F
attribute [local instance] Classical.propDecidable
namespace Wick018D1

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

/-- W7 core: the realized monomial on a smooth field's Sobolev element. -/
theorem mon_smooth (M j : ℕ) (hM : 2 ≤ M) (hjM : j ≤ M)
    (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1)
    (x : SobolevHilbert ((M - 1 : ℕ) : ℝ))
    (hsource : ∀ n : ℤ,
      (show WeightedHilbert (sobolevModeWeight ((M - 1 : ℕ) : ℝ)) from x) n =
        physicalFourier (ContinuousMap.toLp 2 spatialMeasure ℂ
          (riccatiSmoothPeriodicLiftContinuousMapRecovery30First u hu.continuous hper)) n)
    (q : Jet →₀ ℕ) (hq : q ∈ (normalizedRemainder38 j).support) :
    localRemainderMonomialValue38 M j q (toCarrier38 _ x) =
      (∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t
        (MvPolynomial.monomial q ((normalizedRemainder38 j).coeff q))).re := by
  have h : 2 ≤ M ∧ j ≤ M ∧ q ∈ (normalizedRemainder38 j).support := ⟨hM, hjM, hq⟩
  simp only [localRemainderMonomialValue38, h, and_self, dite_true]
  exact riccatiMonomialSobolevCMM38_diag_smooth (M - 1) q _ _
    (normalizedRemainder38_order M j hjM q hq) u hu hper x hsource

/-- The monomial integral as `coeff * ∫ ∏ jets`. -/
theorem eval_integral (u : ℝ → ℂ) (q : Jet →₀ ℕ) (c : ℤ) :
    ∫ t in (0 : ℝ)..1, riccatiJetEvaluation u t (MvPolynomial.monomial q c) =
      (c : ℂ) * ∫ t in (0 : ℝ)..1,
        ∏ i : OccType38 q, jet38 (occBar38 q) (occOrd38 q) u i t := by
  simp only [eval_monomial38]
  exact intervalIntegral.integral_const_mul _ _

theorem mon_plane_add (m : ℕ) (hm : 2 ≤ m) (N : ℕ) (z : FourierPlane N)
    {K : ℕ} (ι : Fin K → ℤ) (hinj : Function.Injective ι) (hι : ∀ k, (N : ℤ) < |ι k|)
    (g : Fin K → ℂ) (j : ℕ) (hj : j ≤ m) (q : Jet →₀ ℕ)
    (hq : q ∈ (normalizedRemainder38 j).support) :
    localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + finiteElement38 _ ι g)) =
      (((normalizedRemainder38 j).coeff q : ℂ) * ∫ t in (0 : ℝ)..1,
        ∏ i : OccType38 q, jet38 (occBar38 q) (occOrd38 q)
          (fun y => planeReal N z y + tailField38 ι g y) i t).re := by
  have hab := plane_append_injective38 N ι hinj hι
  have hu : ContDiff ℝ ∞ (fun y => planeReal N z y + tailField38 ι g y) := planeTail_contDiff38 N z ι g
  have hper : Function.Periodic (fun y => planeReal N z y + tailField38 ι g y) 1 :=
    fun y => by
      simp only
      rw [planeReal_periodic N z y, tailField_periodic38 ι g y]
  have hfe : planeElement38 ((m - 1 : ℕ) : ℝ) N z + finiteElement38 _ ι g =
      finiteElement38 _ (Fin.append (modeIndex N) ι) (Fin.append z g) := by
    rw [planeElement38, finiteElement_append38 _ _ _ _ _ hab]
  have hu' : ContDiff ℝ ∞ (tailField38 (Fin.append (modeIndex N) ι) (Fin.append z g)) := by
    have : tailField38 (Fin.append (modeIndex N) ι) (Fin.append z g) =
        fun y => planeReal N z y + tailField38 ι g y := by
      funext y
      rw [tailField_append38, planeReal_eq_tailField38]
    rw [this]; exact hu
  have hper' := tailField_periodic38 (Fin.append (modeIndex N) ι) (Fin.append z g)
  have hfun : tailField38 (Fin.append (modeIndex N) ι) (Fin.append z g) =
      fun y => planeReal N z y + tailField38 ι g y := by
    funext y
    rw [tailField_append38, planeReal_eq_tailField38]
  rw [hfe, mon_smooth m j hm hj _ hu' hper' _
    (finiteElement_hsource38 _ _ _ hab hu' hper') q hq, eval_integral, hfun]

theorem mon_plane (m : ℕ) (hm : 2 ≤ m) (N : ℕ) (z : FourierPlane N) (j : ℕ) (hj : j ≤ m)
    (q : Jet →₀ ℕ) (hq : q ∈ (normalizedRemainder38 j).support) :
    localRemainderMonomialValue38 m j q (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z)) =
      (((normalizedRemainder38 j).coeff q : ℂ) * ∫ t in (0 : ℝ)..1,
        ∏ i : OccType38 q, jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i t).re := by
  rw [mon_smooth m j hm hj (planeReal N z) (planeReal_smooth38 N z) (planeReal_periodic N z) _
    (planeElement_hsource38 _ N z) q hq, eval_integral]

/-- Finite-cutoff expectation of one monomial: the sum over all low-occurrence sets `R`. -/
theorem finite_cutoff_expectation (m : ℕ) (β : ℕ → ℝ) (hm : 2 ≤ m)
    (hq : ∀ n : ℤ, 0 < finiteHierarchyRate38 m β n) (j : ℕ) (hj : j ≤ m) (q : Jet →₀ ℕ)
    (hqs : q ∈ (normalizedRemainder38 j).support) (N : ℕ) (z : FourierPlane N) (N' : ℕ) :
    ∫ s, localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + truncRealization38 m N N' s))
        ∂gammaM38 m β =
      ∑ R ∈ (Finset.univ : Finset (OccType38 q)).powerset,
        (((normalizedRemainder38 j).coeff q : ℂ) *
          ∫ x in (0 : ℝ)..1,
            (∏ i ∈ R, jet38 (occBar38 q) (occOrd38 q) (planeReal N z) i x) *
              Wick018B.wickMatchingSumFin m β N N' q R).re := by
  set γ := gammaM38 m β
  set ι := truncIota38 N N' with hι_def
  set c : ℂ := ((normalizedRemainder38 j).coeff q : ℂ) with hc_def
  set F : (Fin (truncFinset38 N N').card → ℂ) → ℝ := fun g =>
    localRemainderMonomialValue38 m j q
      (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + finiteElement38 _ ι g)) with hF_def
  have hFc : Continuous (fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) =>
      localRemainderMonomialValue38 m j q (toCarrier38 _ y)) :=
    (continuous_localRemainderMonomialValue38 m j q).comp (continuous_toCarrier38 _)
  have hFm : Measurable F :=
    (hFc.measurable).comp ((measurable_const.add (measurable_finiteElement38 _ _)))
  have hφ : Measurable (fun s : ℤ → ℂ => fun k => s (ι k)) :=
    measurable_pi_iff.2 (fun k => measurable_pi_apply _)
  have hstep : ∫ s, localRemainderMonomialValue38 m j q
        (toCarrier38 _ (planeElement38 ((m - 1 : ℕ) : ℝ) N z + truncRealization38 m N N' s)) ∂γ =
      ∫ g, F g ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k)) := by
    rw [← law_truncBlock38 (m := m) (β := β) N N', integral_map hφ.aemeasurable hFm.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [hF_def, truncRealization_eq_finiteElement38]
    rfl
  rw [hstep]
  have hinj := truncIota_injective38 N N'
  have hgt := truncIota_gt38 N N'
  have hFg : ∀ g, F g = (c * ∑ R ∈ (Finset.univ : Finset (OccType38 q)).powerset,
      ∫ x in (0 : ℝ)..1, termR38 (occBar38 q) (occOrd38 q) N z ι R x g).re := by
    intro g
    simp only [hF_def]
    rw [mon_plane_add m hm N z ι hinj hgt g j hj q hqs]
    congr 2
    rw [← intervalIntegral.integral_finset_sum]
    · refine intervalIntegral.integral_congr (fun x _ => ?_)
      exact prod_jet_expand38 (occBar38 q) (occOrd38 q) N z ι g x
    · intro R _
      exact (continuous_termR38 (occBar38 q) (occOrd38 q) N z ι R g).intervalIntegrable _ _
  have hI : ∀ R : Finset (OccType38 q), Integrable (fun g : Fin (truncFinset38 N N').card → ℂ =>
      ∫ x in (0 : ℝ)..1, termR38 (occBar38 q) (occOrd38 q) N z ι R x g)
      (cgPi (fun k => finiteHierarchyRate38 m β (ι k))) :=
    fun R => (Wick018B.finite_wick_term m β hq N N' z q R).1
  have hterm : ∀ R : Finset (OccType38 q), Integrable (fun g : Fin (truncFinset38 N N').card → ℂ =>
      (c * ∫ x in (0 : ℝ)..1, termR38 (occBar38 q) (occOrd38 q) N z ι R x g).re)
      (cgPi (fun k => finiteHierarchyRate38 m β (ι k))) :=
    fun R => Complex.reCLM.integrable_comp ((hI R).const_mul c)
  simp only [hFg, Finset.mul_sum, Complex.re_sum]
  rw [integral_finset_sum _ (fun R _ => hterm R)]
  refine Finset.sum_congr rfl fun R _ => ?_
  have h1 := Complex.reCLM.integral_comp_comm ((hI R).const_mul c)
  have h2 : ∫ g : Fin (truncFinset38 N N').card → ℂ, (c * ∫ x in (0 : ℝ)..1,
      termR38 (occBar38 q) (occOrd38 q) N z ι R x g).re
        ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k)) =
      (∫ g : Fin (truncFinset38 N N').card → ℂ, c * (∫ x in (0 : ℝ)..1,
      termR38 (occBar38 q) (occOrd38 q) N z ι R x g)
        ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))).re := h1
  rw [h2, integral_const_mul, (Wick018B.finite_wick_term m β hq N N' z q R).2]

end Wick018D1
end NlsGge.ThirdConsultation.F
end
