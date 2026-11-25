import QuantumNLS.Prop018Phase
import QuantumNLS.Prop018SequenceBundle

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Complex Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop018SequencePhase

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
open QuantumNLS.LabelExactPeriod (rectIntegral rectIntegral_sum)
open QuantumNLS.Prop018Period (poly prim root_period_poly period_err continuous_poly)
open QuantumNLS.Prop018SequenceBundle (moving_contour_bundle sequence_regime)
open QuantumNLS.Prop018Phase
open QuantumNLS.HaarSummableReconstruction (contAt_gen)
open QuantumNLS.BetheSpectralCharges (eigenvalue)

def C0ev (L κ : ℝ) (f : ℂ → ℂ → ℂ) (a : ℕ → ℝ) (h : ℝ) (p : ℕ → ℝ) (d N : ℕ) (m : MArr N) : ℝ :=
  -(1 / (2 * Real.pi * κ)) *
    (rectIntegral (fun z => poly p d z * f z (sNf L (κ / N) (qAct L κ N m) z)) (-a N) (a N) h).re

/-- Eigenvalue of `C_{1,N,p} = Re (i/2π) ∮_{Γ_N} p(z) q̃_z(S_N(z), S_N'(z)) dz` on `Ψ_{N,m}` (`Q7A:eq:C1`). -/
def C1ev (L κ : ℝ) (qt : ℂ → ℂ → ℂ → ℂ) (a : ℕ → ℝ) (h : ℝ) (p : ℕ → ℝ) (d N : ℕ) (m : MArr N) : ℝ :=
  ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * qt z (sNf L (κ / N) (qAct L κ N m) z)
    (deriv (sNf L (κ / N) (qAct L κ N m)) z)) (-a N) (a N) h).re

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem phase_of_bundle (hκ : 0 < κ) (μ : Measure ℝ) {h ρ C M η r K Kd : ℝ} {b : ℕ} (hh : 0 < h)
    (hρ0 : 0 < ρ) (hM1 : 1 ≤ M) (hη : 0 < η) (_hb : 1 ≤ b)
    (R ε a : ℕ → ℝ) (_hR : ∀ N, 0 < R N) (_hε : ∀ N, 0 < ε N)
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
    (d : ℕ) (r0 : ℝ) (hr0' : 0 < r0) (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ)
    (hf : ∀ z w, ‖w - sf L κ (Gfull μ) z‖ < r0 → f z w = lam L κ (Gfull μ) z w)
    (hqt : ∀ z w v, ‖w - sf L κ (Gfull μ) z‖ < r0 →
      ‖v - deriv (sf L κ (Gfull μ)) z‖ < r0 → qt z w v = qch L κ (Gfull μ) z w v) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ → ℝ, ∀ m ∈ E N,
      |∑ r ∈ Finset.range (d + 1), p r * eigenvalue L N (κ / N) r m
        - (N : ℝ) * C0ev L κ f a h p d N m - C1ev L κ qt a h p d N m| ≤
        (κ ^ 2 + 4 * max C 0 * (1 + h) ^ (d + 1) / (2 * Real.pi * κ)) *
          (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) / N := by
  have hL : 0 < L := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  -- `δ_N → 0`
  have hδN : Tendsto (fun N : ℕ => Kd * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using hseq.const_mul Kd
  have hsm : ∀ᶠ N : ℕ in atTop,
      Kd * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) < r0 ∧
      Kd * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) / (ρ / 2) < r0 := by
    have h2 : Tendsto (fun N : ℕ => Kd * (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)) / (ρ / 2))
        atTop (𝓝 0) := by simpa using hδN.div_const (ρ / 2)
    exact (hδN.eventually (gt_mem_nhds hr0')).and (h2.eventually (gt_mem_nhds hr0'))
  have hcN : ∀ᶠ N : ℕ in atTop, 2 * (κ / (N : ℝ)) < h ∧ 2 * (κ / (N : ℝ)) < 1 := by
    have : Tendsto (fun N : ℕ => 2 * (κ / (N : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).const_mul (2 : ℝ)
    exact (this.eventually (gt_mem_nhds hh)).and (this.eventually (gt_mem_nhds one_pos))
  filter_upwards [hev, hsm, hcN, hgeom, eventually_ge_atTop 1]
    with N hevN hsmN hcN' hreg hN1
  intro p m hm
  have hN : 0 < N := hN1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha2 : 2 ≤ (a N) := by linarith [hreg.1, hreg.2]
  have hρ8 : 0 < ρ / 8 := by positivity
  have hzN : ∀ z ∈ Gam (-(a N)) (a N) h, z ∈ NbhdN (a N) h (ρ / 8) := fun z hz =>
    gam_sub_nbhd hz (by rw [sub_self, norm_zero]; exact hρ8.le)
  have hball : ∀ z ∈ Gam (-(a N)) (a N) h, ∀ᶠ w in 𝓝 z, w ∈ NbhdN (a N) h (ρ / 8) := fun z hz => by
    filter_upwards [Metric.ball_mem_nhds z hρ8] with w hw
    exact gam_sub_nbhd hz (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le)
  -- the roots lie in the window
  have hroots : ∀ j, |(qAct L κ N m) j| ≤ (a N) / 2 := by
    have hz0 : (((a N) : ℝ) : ℂ) ∈ Gam (-(a N)) (a N) h := Or.inr ⟨by simp only [ofReal_im, Set.mem_Icc]; constructor <;> linarith,
      Or.inr (by simp only [ofReal_re])⟩
    intro j
    have := ((hevN m hm _ (hzN _ hz0)).2.1) j
    linarith [hreg.2]
  -- the background is differentiable near `Γ_N`
  have hsfd : ∀ z ∈ NbhdN (a N) h (ρ / 8), DifferentiableAt ℂ (sf L κ (Gfull μ)) z := fun z hz => by
    have hG := (hevN m hm z hz).2.2.2.2.1
    have hA : DifferentiableAt ℂ (Af κ (Gfull μ)) z := (hG.const_mul (I * κ)).cexp
    have he : DifferentiableAt ℂ (ef L) z := (hasDerivAt_ef L z).differentiableAt
    exact hA.add (he.div hA (exp_ne_zero _))
  -- `s_N` and `s_N'` are within `r₀` of the background on `Γ_N`
  have hsN : ∀ z ∈ Gam (-(a N)) (a N) h, ‖sNf L (κ / N) (qAct L κ N m) z - sf L κ (Gfull μ) z‖ < r0 ∧
      ‖deriv (sNf L (κ / N) (qAct L κ N m)) z - deriv (sf L κ (Gfull μ)) z‖ < r0 := fun z hz => by
    have hP := hevN m hm z (hzN z hz)
    have hder := hP.2.2.2.2.2.2.2.2.2
    rw [sNsrc_eq, sLimsrc_eq] at hder
    have hroot : ∀ j, 2 * |κ / (N : ℝ)| < ‖z - ((qAct L κ N m) j : ℂ)‖ := hP.1.1
    have hd1 : DifferentiableAt ℂ (sNf L (κ / N) (qAct L κ N m)) z := (hasDerivAt_sN L hroot).differentiableAt
    constructor
    · have h0 := hder 0
      simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul] at h0
      exact lt_of_le_of_lt h0 hsmN.1
    · have h1 := hder 1
      rw [iteratedDeriv_one, deriv_fun_sub hd1 (hsfd z (hzN z hz))] at h1
      simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul] at h1
      exact lt_of_le_of_lt h1 hsmN.2
  -- pointwise identification of the extensions on `Γ_N`
  have hfz : ∀ z ∈ Gam (-(a N)) (a N) h, f z (sNf L (κ / N) (qAct L κ N m) z) = logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z := fun z hz =>
    (hf z _ (hsN z hz).1).trans (logaNf_eq_lam L κ (κ / N) (Gfull μ) (qAct L κ N m) z).symm
  have hqz : ∀ z ∈ Gam (-(a N)) (a N) h, qt z (sNf L (κ / N) (qAct L κ N m) z) (deriv (sNf L (κ / N) (qAct L κ N m)) z) =
      corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z := fun z hz => by
    rw [hqt z _ _ (hsN z hz).1 (hsN z hz).2]
    have hP := hevN m hm z (hzN z hz)
    have hGc : ∀ᶠ w in 𝓝 z, Df L κ (Gfull μ) w ≠ 0 := by
      filter_upwards [hball z hz] with w hw
      have := (hevN m hm w hw).2.2.2.2.2.1
      intro h0; rw [h0, norm_zero] at this; linarith
    have hW : 1 + Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ∈ slitPlane := by
      refine Or.inl ?_
      have h1 := Complex.abs_re_le_norm (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z)
      have h2 := hP.1.2.1
      simp only [add_re, one_re]
      linarith [neg_abs_le (Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z).re]
    have hM0 : 0 < 1 / (2 * M) := by positivity
    have ha0 : aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.1; rw [h0, norm_zero] at this; linarith
    have hDN0 : DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z ≠ 0 := fun h0 => by
      have := hP.1.2.2.2.1; rw [h0, norm_zero] at this; linarith
    exact (corrf_eq_qch hP.2.2.2.2.1 hGc hP.1.1 hW ha0 hDN0).symm
  -- continuity on `Γ_N`
  have hcont : ∀ z ∈ Gam (-(a N)) (a N) h, ContinuousAt (logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m)) z ∧
      ContinuousAt (corrf L κ (κ / N) (Gfull μ) (qAct L κ N m)) z ∧ ContinuousAt (ellf (κ / N) (qAct L κ N m)) z := fun z hz => by
    have hP := hevN m hm z (hzN z hz)
    have hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (Gfull μ) w := by
      filter_upwards [hball z hz] with w hw
      exact (hevN m hm w hw).2.2.2.2.1
    have hDz : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hc := contAt_gen (by linarith : (0 : ℝ) < M) hη hGnear hP.1.1 hDz hP.1.2.1 hP.1.2.2.1 hP.1.2.2.2.1
      hP.1.2.2.2.2.1 hP.2.2.2.2.2.2.2.1
    exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  have hremz : ∀ z ∈ Gam (-(a N)) (a N) h, ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
      I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ max C 0 / (N : ℝ) ^ 2 := fun z hz =>
    ((hevN m hm z (hzN z hz)).1.2.2.2.2.2).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  -- assemble
  have hC0 : C0ev L κ f a h p d N m = -(1 / (2 * Real.pi * κ)) *
      (rectIntegral (fun z => poly p d z * logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z) (-(a N)) (a N) h).re := by
    unfold C0ev
    rw [QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam (by linarith) hh.le fun z hz => by rw [hfz z hz]]
  have hC1 : C1ev L κ qt a h p d N m =
      ((I / (2 * Real.pi)) * rectIntegral (fun z => poly p d z * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z) (-(a N)) (a N) h).re := by
    unfold C1ev
    rw [QuantumNLS.HaarNonlinearAbstract.rect_congr_Gam (by linarith) hh.le fun z hz => by rw [hqz z hz]]
  rw [charge_symbol hκ hN m p d, hC0, hC1]
  exact phase_det hκ hN ha2 hh (le_max_right _ _) hroots hcN'.1 hcN'.2 (fun z hz => (hevN m hm z (hzN z hz)).1.1)
    hcont hremz p d



end QuantumNLS.Prop018SequencePhase

#print axioms QuantumNLS.Prop018SequencePhase.phase_of_bundle

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop018SequencePhase." then
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
