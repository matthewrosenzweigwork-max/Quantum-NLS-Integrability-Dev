import NlsGge.Hierarchy.ExponentialH2Moment38
import NlsGge.Birkhoff.F09Limit38d
import NlsGge.ThirdConsultation.T.ECarrier98

/- T-005 PRODUCTION (author proof development; packaged by proof development; not reviewed, not accepted).
   Module: NlsGge.Atomic.T.T005 (TASK_INDEX T-005: NlsGge/Atomic/T/T005.lean). Head: Pro round 8 section 19, verbatim
   (fullFourier_unnormalized_expH2). Also hosts the ONE common producer fullFourier_common_producer98
   (T-005, T-006, T-007 are projections of it) and the definition unnormalizedTest (Pro section 19 body,
   T.lean.md). Route: exponentialH2Moment38 chooses (eta, C) once, before c, s, N; transfer to E_s via
   integrable_comp_planeCoord98 / integral_transfer38 (host module NlsGge.ThirdConsultation.T.ECarrier98);
   tails use the pointwise bound indicator <= fN * exp(eta*||P x||^2) * exp(-eta R^2) and integral_mono;
   tests use the pointwise bound |F(Px)(1-chi(Px))fN| <= ||F|| indicator(tail) fN and norm_integral_le_of_norm_le.
   B/O-free: isOpen_tailSet38 (F09Limit38d) and the other anchors carry no BirkhoffInput38 or OneSmoothingInput38
   premise. tail_Es38 and unloc_sub_loc38 (F09Limit38d) are also free of B/O at premise level: they call
   BirkhoffInput38.integrable_fN38, whose statement has no B or O binder (W10Localized38i.lean). They are not
   used here, because the substitute route through exponentialH2Moment38 is used instead. -/

set_option autoImplicit false
open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core

noncomputable section

namespace NlsGge.ThirdConsultation.T

/-- Unnormalized test functional on the E_s Gaussian (Pro section 19; T.lean.md body). -/
def unnormalizedTest {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (F : ECarrier38 c s → ℝ) (N : ℕ) : ℝ :=
  ∫ x, F (projE38 c s N x) * fN38 c s N x
    ∂(fullWeightedSequenceGaussian c s)

/-- ONE common producer: the same (eta, C) give the moment, every strict tail, and every
bounded-continuous-test cutoff estimate. Exported by T-005, T-006 and T-007 as projections. -/
theorem fullFourier_common_producer98
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : lower ≤ upper) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (c : BoundedCoefficients lower upper) (s : ℝ),
        (1 : ℝ) / 2 < s → ∀ N : ℕ,
          (Integrable
              (fun x : ECarrier38 c s =>
                fN38 c s N x * Real.exp
                  (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
              (fullWeightedSequenceGaussian c s) ∧
            (∫ x : ECarrier38 c s,
              fN38 c s N x * Real.exp
                (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
                ∂(fullWeightedSequenceGaussian c s)) ≤ C) ∧
          (∀ R : ℝ, 0 ≤ R →
            Integrable
              ((tailSet38 c s N R).indicator (fN38 c s N))
              (fullWeightedSequenceGaussian c s) ∧
            (∫ x : ECarrier38 c s,
              (tailSet38 c s N R).indicator (fN38 c s N) x
                ∂(fullWeightedSequenceGaussian c s)) ≤
                  C * Real.exp (-(η * R ^ 2))) ∧
          (∀ R : ℝ, 0 ≤ R →
            ∀ (F : BoundedContinuousFunction (ECarrier38 c s) ℝ)
              (χ : ECarrier38 c s → ℝ),
              Measurable χ →
              (∀ y : ECarrier38 c s, 0 ≤ χ y ∧ χ y ≤ 1) →
              (∀ y : ECarrier38 c s,
                ‖eToSob38 c s 2 y‖ ≤ R → χ y = 1) →
              Integrable
                (fun x : ECarrier38 c s =>
                  F (projE38 c s N x) * fN38 c s N x)
                (fullWeightedSequenceGaussian c s) ∧
              Integrable
                (fun x : ECarrier38 c s =>
                  F (projE38 c s N x) * χ (projE38 c s N x) *
                    fN38 c s N x)
                (fullWeightedSequenceGaussian c s) ∧
              |unnormalizedTest c s (fun y => F y) N -
                unnormalizedTest c s (fun y => F y * χ y) N| ≤
                  C * ‖F‖ * Real.exp (-(η * R ^ 2))) := by
  obtain ⟨η, C, hη, hC, hmom⟩ := exponentialH2Moment38 lower upper hlower hupper
  refine ⟨η, C, hη, hC, fun c s hs N => ?_⟩
  have hI := (hmom c N).1
  have hMom : Integrable (fun x : ECarrier38 c s =>
      fN38 c s N x * Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
      (fullWeightedSequenceGaussian c s) := by
    rw [fun_eq_planeCoord98 c s N η]
    exact integrable_comp_planeCoord98 c s hs N _ hI
  have hMomInt : (∫ x : ECarrier38 c s,
      fN38 c s N x * Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
        ∂(fullWeightedSequenceGaussian c s)) ≤ C := by
    rw [fun_eq_planeCoord98 c s N η]
    exact (NlsGge.Birkhoff.integral_transfer38 c s hs N _ hI.aestronglyMeasurable).trans_le
      (hmom c N).2
  have hfN : Integrable (fN38 c s N) (fullWeightedSequenceGaussian c s) := by
    refine hMom.mono' (measurable_fN38_98 c s N).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (fN38_pos c s N x)]
    exact le_mul_of_one_le_right (fN38_pos c s N x).le
      (Real.one_le_exp (mul_nonneg hη.le (sq_nonneg _)))
  -- tails: one pointwise bound with the same eta, C
  have htail : ∀ R : ℝ, 0 ≤ R →
      Integrable ((tailSet38 c s N R).indicator (fN38 c s N))
        (fullWeightedSequenceGaussian c s) ∧
      (∫ x : ECarrier38 c s,
        (tailSet38 c s N R).indicator (fN38 c s N) x
          ∂(fullWeightedSequenceGaussian c s)) ≤ C * Real.exp (-(η * R ^ 2)) := by
    intro R hR
    have hind : Integrable ((tailSet38 c s N R).indicator (fN38 c s N))
        (fullWeightedSequenceGaussian c s) :=
      hfN.indicator (isOpen_tailSet38 c s N R).measurableSet
    refine ⟨hind, ?_⟩
    have hpt : ∀ x : ECarrier38 c s,
        (tailSet38 c s N R).indicator (fN38 c s N) x ≤
          (fN38 c s N x * Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)) *
            Real.exp (-(η * R ^ 2)) := by
      intro x
      by_cases hx : x ∈ tailSet38 c s N R
      · refine le_trans (le_of_eq (Set.indicator_of_mem hx _)) ?_
        have hx' : R < ‖eToSob38 c s 2 (projE38 c s N x)‖ := hx
        have hsq : R ^ 2 ≤ ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2 := by nlinarith
        have h1 : 1 ≤ Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2) *
            Real.exp (-(η * R ^ 2)) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have := mul_nonneg hη.le (sub_nonneg.2 hsq)
          linarith
        calc fN38 c s N x = fN38 c s N x * 1 := (mul_one _).symm
          _ ≤ fN38 c s N x * (Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2) *
              Real.exp (-(η * R ^ 2))) :=
            mul_le_mul_of_nonneg_left h1 (fN38_pos c s N x).le
          _ = _ := by ring
      · refine le_trans (le_of_eq (Set.indicator_of_notMem hx _)) ?_
        exact mul_nonneg (mul_nonneg (fN38_pos c s N x).le (Real.exp_pos _).le) (Real.exp_pos _).le
    calc (∫ x : ECarrier38 c s, (tailSet38 c s N R).indicator (fN38 c s N) x
            ∂(fullWeightedSequenceGaussian c s))
        ≤ ∫ x : ECarrier38 c s,
            (fN38 c s N x * Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)) *
              Real.exp (-(η * R ^ 2)) ∂(fullWeightedSequenceGaussian c s) :=
          integral_mono hind (hMom.mul_const _) hpt
      _ = (∫ x : ECarrier38 c s,
            fN38 c s N x * Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
              ∂(fullWeightedSequenceGaussian c s)) * Real.exp (-(η * R ^ 2)) :=
          integral_mul_const _ _
      _ ≤ C * Real.exp (-(η * R ^ 2)) :=
          mul_le_mul_of_nonneg_right hMomInt (Real.exp_pos _).le
  -- tests: arbitrary bounded continuous F and measurable cutoff chi in [0,1], chi = 1 on the ball
  have htest : ∀ R : ℝ, 0 ≤ R →
      ∀ (F : BoundedContinuousFunction (ECarrier38 c s) ℝ)
        (χ : ECarrier38 c s → ℝ),
        Measurable χ →
        (∀ y : ECarrier38 c s, 0 ≤ χ y ∧ χ y ≤ 1) →
        (∀ y : ECarrier38 c s, ‖eToSob38 c s 2 y‖ ≤ R → χ y = 1) →
        Integrable
          (fun x : ECarrier38 c s => F (projE38 c s N x) * fN38 c s N x)
          (fullWeightedSequenceGaussian c s) ∧
        Integrable
          (fun x : ECarrier38 c s =>
            F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x)
          (fullWeightedSequenceGaussian c s) ∧
        |unnormalizedTest c s (fun y => F y) N -
          unnormalizedTest c s (fun y => F y * χ y) N| ≤
            C * ‖F‖ * Real.exp (-(η * R ^ 2)) := by
    intro R hR F χ hχm hχb hχ1
    have hFm : Measurable (fun x : ECarrier38 c s => F (projE38 c s N x)) :=
      (F.continuous.comp (projE38 c s N).continuous).measurable
    have hχPm : Measurable (fun x : ECarrier38 c s => χ (projE38 c s N x)) :=
      hχm.comp (projE38 c s N).continuous.measurable
    have hA : Integrable
        (fun x : ECarrier38 c s => F (projE38 c s N x) * fN38 c s N x)
        (fullWeightedSequenceGaussian c s) := by
      refine (hfN.const_mul ‖F‖).mono'
        (hFm.mul (measurable_fN38_98 c s N)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (fN38_pos c s N x).le]
      exact mul_le_mul_of_nonneg_right (F.norm_coe_le_norm _) (fN38_pos c s N x).le
    have hB : Integrable
        (fun x : ECarrier38 c s =>
          F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x)
        (fullWeightedSequenceGaussian c s) := by
      refine (hfN.const_mul ‖F‖).mono'
        ((hFm.mul hχPm).mul (measurable_fN38_98 c s N)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (fN38_pos c s N x).le]
      have h1 := F.norm_coe_le_norm (projE38 c s N x)
      have h2 : ‖χ (projE38 c s N x)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχb (projE38 c s N x)).1]
        exact (hχb (projE38 c s N x)).2
      have h4 : ‖F (projE38 c s N x)‖ * ‖χ (projE38 c s N x)‖ ≤ ‖F‖ := by
        have := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
        linarith
      exact mul_le_mul_of_nonneg_right h4 (fN38_pos c s N x).le
    refine ⟨hA, hB, ?_⟩
    have hdiff : ∀ x : ECarrier38 c s,
        |F (projE38 c s N x) * fN38 c s N x -
            F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x| ≤
          ‖F‖ * (tailSet38 c s N R).indicator (fN38 c s N) x := by
      intro x
      by_cases hx : x ∈ tailSet38 c s N R
      · refine le_trans ?_ (le_of_eq (congrArg (HMul.hMul ‖F‖)
            (Set.indicator_of_mem hx (fN38 c s N))).symm)
        have hχ0 := hχb (projE38 c s N x)
        have h1 := F.norm_coe_le_norm (projE38 c s N x)
        have e : F (projE38 c s N x) * fN38 c s N x -
            F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x =
              F (projE38 c s N x) * (1 - χ (projE38 c s N x)) * fN38 c s N x := by ring
        have h2 : |F (projE38 c s N x)| ≤ ‖F‖ := by
          simpa [Real.norm_eq_abs] using h1
        have h3 : (0 : ℝ) ≤ 1 - χ (projE38 c s N x) := by linarith [hχ0.2]
        have h5 : 1 - χ (projE38 c s N x) ≤ 1 := by linarith [hχ0.1]
        rw [e, abs_mul, abs_mul, abs_of_nonneg (fN38_pos c s N x).le, abs_of_nonneg h3]
        have h4 : |F (projE38 c s N x)| * (1 - χ (projE38 c s N x)) ≤ ‖F‖ := by
          have := mul_le_mul h2 h5 h3 (norm_nonneg _)
          linarith
        exact mul_le_mul_of_nonneg_right h4 (fN38_pos c s N x).le
      · refine le_trans ?_ (le_of_eq (congrArg (HMul.hMul ‖F‖)
            (Set.indicator_of_notMem hx (fN38 c s N))).symm)
        have hx' : ¬ (R < ‖eToSob38 c s 2 (projE38 c s N x)‖) := hx
        have hle : ‖eToSob38 c s 2 (projE38 c s N x)‖ ≤ R := not_lt.1 hx'
        rw [hχ1 (projE38 c s N x) hle]
        simp
    have hD : Integrable (fun x : ECarrier38 c s =>
        ‖F‖ * (tailSet38 c s N R).indicator (fN38 c s N) x)
        (fullWeightedSequenceGaussian c s) := (htail R hR).1.const_mul ‖F‖
    have hsub : (∫ x : ECarrier38 c s,
        (F (projE38 c s N x) * fN38 c s N x -
          F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x)
          ∂(fullWeightedSequenceGaussian c s)) =
        (∫ x : ECarrier38 c s, F (projE38 c s N x) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) -
        (∫ x : ECarrier38 c s, F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) :=
      integral_sub hA hB
    have hle := norm_integral_le_of_norm_le
      (f := fun x : ECarrier38 c s => F (projE38 c s N x) * fN38 c s N x -
        F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x) hD
      (Filter.Eventually.of_forall fun x => le_trans (le_of_eq (Real.norm_eq_abs _)) (hdiff x))
    have hconst : (∫ x : ECarrier38 c s, ‖F‖ * (tailSet38 c s N R).indicator (fN38 c s N) x
          ∂(fullWeightedSequenceGaussian c s)) =
        ‖F‖ * ∫ x : ECarrier38 c s, (tailSet38 c s N R).indicator (fN38 c s N) x
          ∂(fullWeightedSequenceGaussian c s) :=
      integral_const_mul _ _
    have hle2 := (congrArg (fun t => ‖t‖) hsub.symm).trans_le hle
    show |(∫ x : ECarrier38 c s, F (projE38 c s N x) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) -
        (∫ x : ECarrier38 c s, F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))| ≤ C * ‖F‖ * Real.exp (-(η * R ^ 2))
    calc _ = ‖(∫ x : ECarrier38 c s, F (projE38 c s N x) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s)) -
        (∫ x : ECarrier38 c s, F (projE38 c s N x) * χ (projE38 c s N x) * fN38 c s N x
          ∂(fullWeightedSequenceGaussian c s))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x : ECarrier38 c s, ‖F‖ * (tailSet38 c s N R).indicator (fN38 c s N) x
          ∂(fullWeightedSequenceGaussian c s) := hle2
      _ = ‖F‖ * ∫ x : ECarrier38 c s, (tailSet38 c s N R).indicator (fN38 c s N) x
          ∂(fullWeightedSequenceGaussian c s) := hconst
      _ ≤ ‖F‖ * (C * Real.exp (-(η * R ^ 2))) :=
          mul_le_mul_of_nonneg_left (htail R hR).2 (norm_nonneg _)
      _ = C * ‖F‖ * Real.exp (-(η * R ^ 2)) := by ring
  exact ⟨⟨hMom, hMomInt⟩, htail, htest⟩

theorem fullFourier_unnormalized_expH2
    (lower upper : ℝ) (hlower : 0 < lower) (hupper : lower ≤ upper) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (c : BoundedCoefficients lower upper) (s : ℝ),
        (1 : ℝ) / 2 < s → ∀ N : ℕ,
          Integrable
            (fun x : ECarrier38 c s =>
              fN38 c s N x * Real.exp
                (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
            (fullWeightedSequenceGaussian c s) ∧
          (∫ x : ECarrier38 c s,
            fN38 c s N x * Real.exp
              (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
              ∂fullWeightedSequenceGaussian c s) ≤ C := by
  obtain ⟨η, C, hη, hC, H⟩ := fullFourier_common_producer98 lower upper hlower hupper
  exact ⟨η, C, hη, hC, fun c s hs N => (H c s hs N).1⟩

end NlsGge.ThirdConsultation.T

end
