import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G3.G3SourcePathHost
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.ThirdConsultation.G3.G3006Host
import Armstrong.Work.RawBetaSum
import Armstrong.Work.ActualBetaRealTrace
import Armstrong.Work.ActualScalarCartesianModels
import Armstrong.Work.ActualScalarZRealTrace

/- G3_006 PRODUCTION01 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G3/G3006.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from followup8 design STATEMENTS/G3.md:117-132 (no round 9/10 change; same text in followup7 and followup5).
   Route (all Armstrong imports are in the X-006 closure; none is REVIEW_ONLY/DRAFT):
   (1) offDiagonalBeta = gk151BetaAmbient38 = gkSourceBeta38 on the subtype (gk151BetaAmbient_eq_source38), and
       gkSourceBeta_real_trace38 (Armstrong.Work.ActualBetaRealTrace) at the sourceFamily fields gives im = 0.
   (2) Z+ := gk16ActualScalarZPlus38 sourceF n (realSlice u).  star Z+ = Z- (gk16_same_family_scalar_models_conj38) and Z+ * Z- = gamma2 =
       gap^2 (gk16_actual_scalar_models_product38, gamma2_value38) give ||Z+|| = ||gap||, so ||etaExponential|| = 1 for gap /= 0; hence it is
       nonzero and Complex.log of it is purely imaginary, so etaRepresentative = (arg etaExponential : R).
   (3) For a source path integral a, gk16_actual_scalar_models_of_path_integral38 gives Z+ = gap * exp(I a), i.e. etaExponential = exp(I a);
       exp(I a) = exp(I etaRepresentative) (exp_log) gives a = etaRepresentative + k 2 pi, hence the quotient identity and the real+2 pi Z form. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G3_006 (u : PhysicalL2) :
  (∀ n m : ℤ, m ≠ n → (offDiagonalBeta n m (realSlice u)).im = 0) ∧
  ∀ n : ℤ, gap (realSlice u) n ≠ 0 →
    etaExponential n (realSlice u) ≠ 0 ∧
    (∃ r : ℝ, etaAngle n (realSlice u) = QuotientAddGroup.mk (r : ℂ)) ∧
    ∀ (p : SourcePath n ⟨realSlice u, sourceFamily.W_real (mem_range_self u)⟩)
      (a : ℂ),
      HasGKImproperPathIntegral38 n n sourceF
        (sourceGK ⟨realSlice u, sourceFamily.W_real (mem_range_self u)⟩) p a →
      etaAngle n (realSlice u) = QuotientAddGroup.mk a ∧
      ∃ r : ℝ, ∃ k : ℤ, a = (r : ℂ)+(k : ℂ)*(2*(Real.pi : ℂ)) := by
  have hW : realSlice u ∈ sourceW := sourceFamily.W_real (mem_range_self u)
  have hgk : realSlice u ∈ gkW := sourceFamily.W_gk hW
  refine ⟨?_, ?_⟩
  · intro n m hmn
    have e : offDiagonalBeta n m (realSlice u) =
        gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
          sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
          sourceFamily.F_period n m hmn ⟨realSlice u, hW⟩ :=
      gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m hmn ⟨realSlice u, hW⟩
    rw [e]
    exact gkSourceBeta_real_trace38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period sourceFamily.F_real n m hmn u
  · intro n hgap
    have hconj := gk16_same_family_scalar_models_conj38 sourceW sourceFamily.W_real sourceF
      sourceFamily.F_period sourceFamily.F_real n u
    have hprod := gk16_actual_scalar_models_product38 sourceF n (realSlice u) hgk
    have hg2 := gamma2_value38 (realSlice u) hgk n
    have hnormsq : ‖gk16ActualScalarZPlus38 sourceF n (realSlice u)‖ *
        ‖gk16ActualScalarZPlus38 sourceF n (realSlice u)‖ =
        ‖gap (realSlice u) n‖ * ‖gap (realSlice u) n‖ := by
      have h1 := congrArg norm hprod
      rw [norm_mul, ← hconj, norm_star, hg2, norm_pow] at h1
      rw [h1, pow_two]
      rfl
    have hZnorm : ‖gk16ActualScalarZPlus38 sourceF n (realSlice u)‖ =
        ‖gap (realSlice u) n‖ :=
      (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 hnormsq
    have hgapn : ‖gap (realSlice u) n‖ ≠ 0 := norm_ne_zero_iff.2 hgap
    have hnormE : ‖etaExponential n (realSlice u)‖ = 1 := by
      unfold etaExponential
      rw [norm_div, hZnorm]
      exact div_self hgapn
    have hne : etaExponential n (realSlice u) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hnormE
      exact zero_ne_one hnormE
    have hrep : etaRepresentative n (realSlice u) =
        ((Complex.arg (etaExponential n (realSlice u)) : ℝ) : ℂ) := by
      have key : ∀ z : ℂ, ‖z‖ = 1 → -Complex.I * Complex.log z = (Complex.arg z : ℂ) := by
        intro z hz
        apply Complex.ext
        · simp [Complex.log_im, hz]
        · simp [Complex.log_re, hz]
      exact key _ hnormE
    refine ⟨hne, ⟨Complex.arg (etaExponential n (realSlice u)), ?_⟩, ?_⟩
    · unfold etaAngle
      rw [hrep]
    · intro p a ha
      have hlm : lamMinus (realSlice u) n ≠ lamPlus (realSlice u) n := by
        intro h
        apply hgap
        change lamPlus (realSlice u) n - lamMinus (realSlice u) n = 0
        rw [h, sub_self]
      have hm := (gk16_actual_scalar_models_of_path_integral38 sourceW sourceFamily.W_gk sourceF
        sourceFamily.F_period n ⟨realSlice u, hW⟩ hlm p a ha).1
      have hE : etaExponential n (realSlice u) = Complex.exp (Complex.I * a) := by
        unfold etaExponential
        rw [hm]
        exact mul_div_cancel_left₀ _ hgap
      have hexp : Complex.exp (Complex.I * a) =
          Complex.exp (Complex.I * etaRepresentative n (realSlice u)) := by
        rw [← hE]
        have : Complex.I * etaRepresentative n (realSlice u) =
            Complex.log (etaExponential n (realSlice u)) := by
          unfold etaRepresentative
          rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
        rw [this, Complex.exp_log hne]
      obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 hexp
      have hak : a = etaRepresentative n (realSlice u) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
        apply mul_left_cancel₀ Complex.I_ne_zero
        linear_combination hk
      refine ⟨?_, Complex.arg (etaExponential n (realSlice u)), k, ?_⟩
      · unfold etaAngle
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_zmultiples_iff]
        refine ⟨k, ?_⟩
        rw [hak]
        simp only [zsmul_eq_mul]
        ring
      · rw [hak, hrep]

end
end NlsGge.GKDefinitionDesign
