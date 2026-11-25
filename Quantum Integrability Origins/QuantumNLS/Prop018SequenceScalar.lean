import QuantumNLS.Prop018Scalar
import QuantumNLS.Prop018SequencePhase

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Complex Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop018SequenceScalar

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN sNsrc sLimsrc)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodTwoTerm
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.LabelExactPeriod (rectIntegral)
open QuantumNLS.Prop018Period (poly continuous_poly)
open QuantumNLS.Prop018SequenceBundle (moving_contour_bundle sequence_regime)
open QuantumNLS.Prop018Scalar
open QuantumNLS.HaarSummableReconstruction (contAt_gen)
open QuantumNLS.BetheSpectralCharges (eigenvalue)
open QuantumNLS.Prop018Phase (dch ach lam qch corrf_eq_qch sNsrc_eq sLimsrc_eq gam_sub_nbhd norm_le_of_gam
  norm_poly_le)
open QuantumNLS.Prop018SequencePhase (C0ev C1ev phase_of_bundle)

def cscal (L κ : ℝ) (μ : Measure ℝ) (a : ℕ → ℝ) (h : ℝ) (p : ℕ → ℝ) (d N : ℕ) : ℝ :=
  ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
    (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) (-a N) (a N) h).re

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem scalar_of_bundle (μ : Measure ℝ) {h ρ C M η r K Kd : ℝ} {b : ℕ} (hh : 0 < h)
    (hρ0 : 0 < ρ) (hM1 : 1 ≤ M) (hη : 0 < η) (_hb : 1 ≤ b)
    (R ε a : ℕ → ℝ) (hR : ∀ N, 0 < R N) (hε : ∀ N, 0 < ε N)
    (hseq : Tendsto (fun N : ℕ => ε N + 1 / R N ^ b + 1 / (N : ℝ)) atTop (𝓝 0))
    (hgeom : ∀ᶠ N : ℕ in atTop, 1 ≤ R N ∧ 2 * R N ≤ a N)
    (E : (N : ℕ) → Set (MArr N))
    (hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ E N, ∀ z ∈ NbhdN (a N) h (ρ / 8),
          ((∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
          ‖Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ 1 / 2 ∧
          1 / (2 * M) ≤ ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          3 * η / 4 ≤ ‖DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z - Af κ (Gfull μ) z‖ ≤ 1 / (2 * M) ∧
          ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
              I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ C / (N : ℝ) ^ 2) ∧
          (∀ j, |qAct L κ N m j| ≤ R N) ∧
          ‖Gfull μ z - GN (qAct L κ N m) z‖ ≤ K * (ε N + 1 / (R N) ^ b) ∧
          (∀ j, r ≤ ‖z - (qAct L κ N m j : ℂ)‖) ∧
          DifferentiableAt ℂ (Gfull μ) z ∧
          η ≤ ‖Df L κ (Gfull μ) z‖ ∧
          ‖Af κ (Gfull μ) z‖ ≤ M ∧ ‖(Af κ (Gfull μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
          ∀ n : ℕ, ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L μ w) z‖ ≤
            n.factorial * (Kd * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)
    (d : ℕ) (r0 : ℝ) (hr0' : 0 < r0) (qt : ℂ → ℂ → ℂ → ℂ)
    (hqt : ∀ z w v, ‖w - sf L κ (Gfull μ) z‖ < r0 →
      ‖v - deriv (sf L κ (Gfull μ)) z‖ < r0 → qt z w v = qch L κ (Gfull μ) z w v) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, ∀ m ∈ E N,
      |C1ev L κ qt a h p d N m - cscal L κ μ a h p d N| ≤
        4 * Lbd M η L ((M + M * M) / (ρ / 16)) (max Kd 0) (max Kd 0 / (ρ / 2)) * (1 + h) ^ (d + 1) /
            (2 * Real.pi) * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) *
          (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) := by
  have hL : 0 < L := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 < M := by linarith
  set Kd' : ℝ := max Kd 0 with hKd'
  have hKd'0 : 0 ≤ Kd' := le_max_right _ _
  set Vs : ℝ := (M + M * M) / (ρ / 16) with hVs
  have hVs0 : 0 ≤ Vs := by rw [hVs]; positivity
  set Lq : ℝ := Lbd M η L Vs Kd' (Kd' / (ρ / 2)) with hLq
  have hLq0 : 0 ≤ Lq := Lbd_nonneg hM1 hη hVs0 hKd'0 hρ0
  -- `δ_N → 0`
  have hδN : Tendsto (fun N : ℕ => Kd' * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using hseq.const_mul Kd'
  have hδN2 : Tendsto (fun N : ℕ => Kd' * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) / (ρ / 2))
      atTop (𝓝 0) := by simpa using hδN.div_const (ρ / 2)
  have hsm : ∀ᶠ N : ℕ in atTop,
      (Kd' * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) < r0 ∧
        Kd' * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) / (ρ / 2) < r0) ∧
      (Kd' * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) < 1 ∧
        Kd' * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) / (ρ / 2) < 1) :=
    ((hδN.eventually (gt_mem_nhds hr0')).and (hδN2.eventually (gt_mem_nhds hr0'))).and
      ((hδN.eventually (gt_mem_nhds one_pos)).and (hδN2.eventually (gt_mem_nhds one_pos)))
  filter_upwards [hev, hsm, hgeom, eventually_ge_atTop 1]
    with N hevN hsmN hreg hN1
  intro p m hm
  have hN : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha2 : 2 ≤ a N := by linarith [hreg.1, hreg.2]
  have hρ8 : 0 < ρ / 8 := by positivity
  set δN : ℝ := ε N + 1 / (R N) ^ b + 1 / (N : ℝ) with hδNdef
  have hδN0 : 0 ≤ δN := by
    have := hR N
    have := hε N
    rw [hδNdef]; positivity
  have hzN : ∀ z ∈ Gam (-(a N)) (a N) h, z ∈ NbhdN (a N) h (ρ / 8) := fun z hz =>
    gam_sub_nbhd hz (by rw [sub_self, norm_zero]; exact hρ8.le)
  have hball : ∀ z ∈ Gam (-(a N)) (a N) h, Metric.ball z (ρ / 8) ⊆ NbhdN (a N) h (ρ / 8) :=
    fun z hz w hw => gam_sub_nbhd hz (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le)
  have hsfd : ∀ z ∈ NbhdN (a N) h (ρ / 8), DifferentiableAt ℂ (sf L κ (Gfull μ)) z := fun z hz => by
    have hG := (hevN m hm z hz).2.2.2.2.1
    have hA : DifferentiableAt ℂ (Af κ (Gfull μ)) z := (hG.const_mul (I * κ)).cexp
    have he : DifferentiableAt ℂ (ef L) z := (hasDerivAt_ef L z).differentiableAt
    exact hA.add (he.div hA (exp_ne_zero _))
  -- the transfer deviations on `Γ_N`
  have hdev : ∀ z ∈ Gam (-(a N)) (a N) h,
      ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ (Gfull μ) z‖ ≤ Kd' * δN ∧
      ‖deriv (sNf L (κ / N) (qAct L κ N m)) z - deriv (sf L κ (Gfull μ)) z‖ ≤ Kd' * δN / (ρ / 2) := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hder := hP.2.2.2.2.2.2.2.2.2
    rw [sNsrc_eq, sLimsrc_eq] at hder
    have hroot : ∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖ := hP.1.1
    have hd1 : DifferentiableAt ℂ (sNf L (κ / N) (qAct L κ N m)) z := (hasDerivAt_sN L hroot).differentiableAt
    have hKK : Kd * δN ≤ Kd' * δN := mul_le_mul_of_nonneg_right (le_max_left _ _) hδN0
    constructor
    · have h0 := hder 0
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul] at h0
      exact h0.trans hKK
    · have h1 := hder 1
      rw [iteratedDeriv_one, deriv_fun_sub hd1 (hsfd z (hzN z hz))] at h1
      simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul] at h1
      exact h1.trans (div_le_div_of_nonneg_right hKK (by positivity))
  -- the background derivative is bounded (Cauchy estimate on a ball of radius `ρ/16`)
  have hsbd : ∀ w ∈ NbhdN (a N) h (ρ / 8), ‖sf L κ (Gfull μ) w‖ ≤ M + M * M := fun w hw => by
    have hP := hevN m hm w hw
    exact norm_sf_le hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1
  have hvbd : ∀ z ∈ Gam (-(a N)) (a N) h, ‖deriv (sf L κ (Gfull μ)) z‖ ≤ Vs := by
    intro z hz
    have hρ16 : 0 < ρ / 16 := by positivity
    have hcl : ∀ w ∈ Metric.closedBall z (ρ / 16), w ∈ NbhdN (a N) h (ρ / 8) := fun w hw =>
      gam_sub_nbhd hz (by rw [Metric.mem_closedBall, dist_eq_norm] at hw; linarith)
    have hdc : DiffContOnCl ℂ (sf L κ (Gfull μ)) (Metric.ball z (ρ / 16)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z hρ16.ne']
      exact fun w hw => (hsfd w (hcl w hw)).differentiableWithinAt
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ16 hdc
      (fun w hw => hsbd w (hcl w (Metric.sphere_subset_closedBall hw)))
  -- the pointwise identifications on `Γ_N`
  have hqz : ∀ z ∈ Gam (-(a N)) (a N) h,
      qt z (sNf L (κ / N) (qAct L κ N m) z) (deriv (sNf L (κ / N) (qAct L κ N m)) z) =
        corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ∧
      corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z =
        qch L κ (Gfull μ) z (sNf L (κ / N) (qAct L κ N m) z) (deriv (sNf L (κ / N) (qAct L κ N m)) z) := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hGc : ∀ᶠ w in 𝓝 z, Df L κ (Gfull μ) w ≠ 0 := by
      filter_upwards [Metric.ball_mem_nhds z hρ8] with w hw
      have := (hevN m hm w (hball z hz hw)).2.2.2.2.2.1
      intro h0; rw [h0, norm_zero] at this; linarith
    have hW : 1 + Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ∈ slitPlane := by
      refine Or.inl ?_
      have h1 := Complex.abs_re_le_norm (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
      have h2 := hP.1.2.1
      simp only [add_re, one_re]
      linarith [neg_abs_le (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z).re]
    have hM0' : 0 < 1 / (2 * M) := by positivity
    have ha0 : aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.1; rw [h0, norm_zero] at this; linarith
    have hDN0 : DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hcq := corrf_eq_qch hP.2.2.2.2.1 hGc hP.1.1 hW ha0 hDN0
    refine ⟨?_, hcq⟩
    rw [hqt z _ _ (lt_of_le_of_lt (hdev z hz).1 hsmN.1.1) (lt_of_le_of_lt (hdev z hz).2 hsmN.1.2)]
    exact hcq.symm
  have hcs : ∀ z ∈ Gam (-(a N)) (a N) h,
      ef L z * deriv (Af κ (Gfull μ)) z / (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)) =
        qch L κ (Gfull μ) z (sf L κ (Gfull μ) z) (deriv (sf L κ (Gfull μ)) z) := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hD0 : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    exact (qch_bg hP.2.2.2.2.1 hD0).symm
  -- continuity of the two integrands on `Γ_N`
  have hPc : Continuous (poly p d) := continuous_poly p d
  have hc1 : ∀ z ∈ Gam (-(a N)) (a N) h,
      ContinuousAt (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z) z := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (Gfull μ) w := by
      filter_upwards [Metric.ball_mem_nhds z hρ8] with w hw
      exact (hevN m hm w (hball z hz hw)).2.2.2.2.1
    have hDz : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hc := contAt_gen hM0 hη hGnear hP.1.1 hDz hP.1.2.1 hP.1.2.2.1 hP.1.2.2.2.1
      hP.1.2.2.2.2.1 hP.2.2.2.2.2.2.2.1
    exact hPc.continuousAt.mul hc.2.1
  have hc0 : ∀ z ∈ Gam (-(a N)) (a N) h,
      ContinuousAt (fun z => poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
        (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) z := by
    intro z hz
    have hP := hevN m hm z (hzN z hz)
    have hAd : DifferentiableOn ℂ (Af κ (Gfull μ)) (Metric.ball z (ρ / 8)) := fun w hw =>
      (((hevN m hm w (hball z hz hw)).2.2.2.2.1).const_mul (I * κ)).cexp.differentiableWithinAt
    have hA'c : ContinuousAt (deriv (Af κ (Gfull μ))) z :=
      ((hAd.deriv Metric.isOpen_ball).continuousOn).continuousAt (Metric.ball_mem_nhds z hρ8)
    have hAc : ContinuousAt (Af κ (Gfull μ)) z :=
      (hAd.differentiableAt (Metric.ball_mem_nhds z hρ8)).continuousAt
    have hec : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    have hA0 : Af κ (Gfull μ) z ≠ 0 := exp_ne_zero _
    have hD0 : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hA2 : Af κ (Gfull μ) z ^ 2 - ef L z ≠ 0 := by
      intro h0; apply hD0; unfold Df; field_simp; linear_combination h0
    exact hPc.continuousAt.mul ((hec.mul hA'c).div (hAc.mul ((hAc.pow 2).sub hec)) (mul_ne_zero hA0 hA2))
  -- assemble
  have hab : -(a N) ≤ a N := by linarith
  have hC1 : C1ev L κ qt a h p d N m = ((I / (2 * Real.pi)) *
      rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
        (-(a N)) (a N) h).re := by
    unfold C1ev
    rw [QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam hab hh.le fun z hz => by rw [(hqz z hz).1]]
  have hdiff : rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
        (-(a N)) (a N) h -
      rectIntegral (fun z => poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
        (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) (-(a N)) (a N) h =
      rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(a N)) (a N) h := by
    rw [rectIntegral_add (f := fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
      (g := fun z => (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) hab hh.le hc1
      (fun z hz => continuousAt_const.mul (hc0 z hz)), rectIntegral_const_mul]
    ring
  set S : ℝ := ∑ r ∈ Finset.range (d + 1), |p r| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => abs_nonneg _
  set B : ℝ := (1 + a N) * (1 + h) with hBdef
  have hB1 : 1 ≤ B := by rw [hBdef]; nlinarith
  have hbound : ‖rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(a N)) (a N) h‖ ≤
      (2 * (a N - -(a N)) + 4 * h) * (S * B ^ d * (Lq * δN)) := by
    refine norm_rectIntegral_le hab hh.le fun z hz => ?_
    have hP := hevN m hm z (hzN z hz)
    have e : poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z)))) =
        poly p d z * (qch L κ (Gfull μ) z (sNf L (κ / N) (qAct L κ N m) z)
            (deriv (sNf L (κ / N) (qAct L κ N m)) z) -
          qch L κ (Gfull μ) z (sf L κ (Gfull μ) z) (deriv (sf L κ (Gfull μ)) z)) := by
      rw [(hqz z hz).2, hcs z hz]; ring
    rw [e, norm_mul]
    have hz1 : ‖z‖ ≤ B := (norm_le_of_gam (by linarith) hh.le hz).trans (by rw [hBdef]; nlinarith)
    have hq := qch_diff_le hM1 hη hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2.1
      hP.2.2.2.2.2.1 hP.1.2.2.1 hP.1.2.2.2.1 (hvbd z hz) (hdev z hz).1 (hdev z hz).2 hsmN.2.1.le hsmN.2.2.le
    rw [Lbd_scale] at hq
    exact mul_le_mul (norm_poly_le p d hB1 hz1) hq (norm_nonneg _) (mul_nonneg hS0 (pow_nonneg (by linarith) d))
  have hlen : 2 * (a N - -(a N)) + 4 * h ≤ 4 * B := by rw [hBdef]; nlinarith
  rw [hC1]
  unfold cscal
  rw [← sub_re, ← mul_sub, hdiff]
  calc |((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(a N)) (a N) h).re|
      ≤ ‖(I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
        (-1 : ℂ) * (poly p d z * (ef L z * deriv (Af κ (Gfull μ)) z /
          (Af κ (Gfull μ) z * (Af κ (Gfull μ) z ^ 2 - ef L z))))) (-(a N)) (a N) h‖ :=
        Complex.abs_re_le_norm _
    _ ≤ 1 / (2 * Real.pi) * ((4 * B) * (S * B ^ d * (Lq * δN))) := by
        rw [norm_mul, norm_div, Complex.norm_I, norm_mul, Complex.norm_two, Complex.norm_real,
          Real.norm_of_nonneg hpi.le]
        refine mul_le_mul_of_nonneg_left (hbound.trans (mul_le_mul_of_nonneg_right hlen ?_)) (by positivity)
        exact mul_nonneg (mul_nonneg hS0 (pow_nonneg (by linarith) d)) (mul_nonneg hLq0 hδN0)
    _ = 4 * Lq * (1 + h) ^ (d + 1) / (2 * Real.pi) * S * (1 + a N) ^ (d + 1) * δN := by
        rw [hBdef, mul_pow, pow_succ (1 + a N) d, pow_succ (1 + h) d]
        field_simp

theorem prop018_reconstruct (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (R ε a : ℕ → ℝ) (idx : ℕ → ℕ)
    (hR : ∀ N, 0 < R N) (hε : ∀ N, 0 < ε N)
    (hseq : Tendsto (fun N : ℕ => ε N + 1 / R N ^ b + 1 / (N : ℝ)) atTop (𝓝 0))
    (hcut : ∀ᶠ N : ℕ in atTop, l0 ≤ idx N ∧ a N = PROP017UniformN.cutSeq L (idx N) ∧ 2 * R N ≤ a N)
    (d : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ Cp Cs : ℝ, 0 ≤ Cp ∧ 0 ≤ Cs ∧ ∀ r0 : ℝ, 0 < r0 → ∀ (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ),
        (∀ z w, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 → f z w = lam L κ (Gfull (μ : Measure ℝ)) z w) →
        (∀ z w v, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 →
          ‖v - deriv (sf L κ (Gfull (μ : Measure ℝ))) z‖ < r0 → qt z w v = qch L κ (Gfull (μ : Measure ℝ)) z w v) →
        ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) (R N) (a N) ρ h
          (eta0 L κ) (ε N) b,
          |∑ r ∈ Finset.range (d + 1), p r * eigenvalue L N (κ / N) r m
            - (N : ℝ) * C0ev L κ f a h p d N m - C1ev L κ qt a h p d N m| ≤
            Cp * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) / N ∧
          |C1ev L κ qt a h p d N m - cscal L κ (μ : Measure ℝ) a h p d N| ≤
            Cs * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) *
              (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) := by
  obtain ⟨ρ, hρ0, h2ρ, C, M, η, r, K, Kd, hM1, hη, hr0, hK0, hev⟩ :=
    moving_contour_bundle hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc R ε a idx hR hε hseq hcut
  have hh : 0 < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 < M := by linarith
  have hVs0 : 0 ≤ (M + M * M) / (ρ / 16) := by positivity
  have hLq0 := Lbd_nonneg (L := L) hM1 hη hVs0 (le_max_right Kd 0) hρ0
  refine ⟨ρ, hρ0, κ ^ 2 + 4 * max C 0 * (1 + h) ^ (d + 1) / (2 * Real.pi * κ),
    4 * Lbd M η L ((M + M * M) / (ρ / 16)) (max Kd 0) (max Kd 0 / (ρ / 2)) * (1 + h) ^ (d + 1) / (2 * Real.pi),
    by positivity, by positivity, fun r0 hr0' f qt hf hqt => ?_⟩
  set E : (N : ℕ) → Set (MArr N) := fun N =>
    EN (μ : Measure ℝ) (qAct L κ N) (R N) (a N) ρ h (eta0 L κ) (ε N) b with hE
  have hgeom : ∀ᶠ N : ℕ in atTop, 1 ≤ R N ∧ 2 * R N ≤ a N :=
    (sequence_regime hb R ε a idx hR hε hseq hcut 1).mono fun _ hn => ⟨hn.1, hn.2.2.1⟩
  have h1 := phase_of_bundle hκ (μ : Measure ℝ) hh hρ0 hM1 hη hb R ε a hR hε hseq hgeom E hev d r0 hr0' f qt hf hqt
  have h2 := scalar_of_bundle (μ : Measure ℝ) hh hρ0 hM1 hη hb R ε a hR hε hseq hgeom E hev d r0 hr0' qt hqt
  filter_upwards [h1, h2] with N hN1 hN2
  exact fun p m hm => ⟨hN1 p m hm, hN2 p m hm⟩

end QuantumNLS.Prop018SequenceScalar

#print axioms QuantumNLS.Prop018SequenceScalar.scalar_of_bundle
#print axioms QuantumNLS.Prop018SequenceScalar.prop018_reconstruct

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop018SequenceScalar." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
