import Mathlib
import NlsGge.Atomic.G5.G5002Host
import NlsGge.Atomic.G5.G5001
import NlsGge.Atomic.G4.G4036
import NlsGge.Atomic.G4.G4036H1
import NlsGge.Atomic.G4.G4036H3
import NlsGge.Atomic.G4.G4032
import NlsGge.GK38.TauGamma
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.GK38.AngleDirichletAnalytic

/- G5-002 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5002.lean.
   Head `G5002` verbatim from STATEMENTS/G5.md (followup12; round 14 retains the head). No lexical edits.
   Route: at the real collapsed gap mu = tau (gkMu in [lower,upper], lower = upper), G4032 gives Z_{+-1} = 0, hence
   A := 2(tau-mu) = 0 and R := terminalRoot = 0.  On V (G5001) R = I * q * delta (signedRadius identity), so
   Z_a = (A + 2aR) exp(-aRC) and cartesianLeading = A + 2aR agree to first order: Leibniz at a zero of the first factor. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5002_Z_formula (n a : ℤ) (ha : a = 1 ∨ a = -1) (ψ : PotPair) :
    cartesianZExtended n a ψ =
      (2 * (tauN ψ n - muSeq ψ n) + 2 * (a : ℂ) * terminalRoot n ψ) *
        Complex.exp (-((a : ℂ) * (terminalRoot n ψ * ownCorrection n ψ (muSeq ψ n)))) := by
  rcases ha with rfl | rfl
  · simp [cartesianZExtended]
  · simp [cartesianZExtended]
    try ring_nf

theorem g5002_mu_eq_tau (n : ℤ) (u : PhysicalL2) (hu : gamma2 (realSlice u) n = 0) :
    muSeq (realSlice u) n = tauN (realSlice u) n := by
  obtain ⟨h1, h2⟩ := tauGamma_real38 u n
  have hsq : (actualGapUpperAllE02_38 u n - actualGapLowerAllE02_38 u n) ^ 2 = 0 := by
    rw [hu] at h2
    exact_mod_cast h2.symm
  have hle : actualGapUpperAllE02_38 u n = actualGapLowerAllE02_38 u n := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
    linarith
  have hm := gkMu_mem_gap38 u n
  have hmu : gkMu u n = actualGapLowerAllE02_38 u n := by
    have := hm.1; have := hm.2; linarith
  rw [muSeq_eq_gkMu38, h1, hmu]
  congr 1
  rw [hle]; ring

theorem g5002_complex (n a : ℤ) (ha : a = 1 ∨ a = -1)
    (u : PhysicalL2) (hu : gamma2 (realSlice u) n = 0) :
  ∃ D : PotPair →L[ℂ] ℂ,
    HasFDerivAt (cartesianZExtended n a) D (realSlice u) ∧
    HasFDerivAt (cartesianLeading n a) D (realSlice u) ∧
    cartesianZExtended n a (realSlice u) = 0 ∧ cartesianLeading n a (realSlice u) = 0 := by
  classical
  set φ : PotPair := realSlice u with hφdef
  have hφB : φ ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  have hgk : φ ∈ gkW := g5001_gk φ hφB
  obtain ⟨V, hVn, hVo, hVS, hq, hψ, -⟩ := G5001 n u
  have hφV : φ ∈ V := mem_of_mem_nhds hVn
  have hμ : muSeq φ n = tauN φ n := g5002_mu_eq_tau n u hu
  -- both sheets vanish at φ
  have hz1 := (G4032 n 1 (Or.inl rfl) φ hφB hu hμ).1
  have hz2 := (G4032 n (-1) (Or.inr rfl) φ hφB hu hμ).1
  have hf1 := g5002_Z_formula n 1 (Or.inl rfl) φ
  have hf2 := g5002_Z_formula n (-1) (Or.inr rfl) φ
  rw [hz1] at hf1
  rw [hz2] at hf2
  have e1 := (mul_eq_zero.1 hf1.symm).resolve_right (Complex.exp_ne_zero _)
  have e2 := (mul_eq_zero.1 hf2.symm).resolve_right (Complex.exp_ne_zero _)
  push_cast at e1 e2
  have hA : 2 * (tauN φ n - muSeq φ n) = 0 := by linear_combination (e1 + e2) / 2
  have hR : terminalRoot n φ = 0 := by linear_combination (e1 - e2) / 4
  -- analytic ingredients
  have hτ : AnalyticAt ℂ (fun ψ : PotPair => tauN ψ n) φ := tauN_analytic n φ hgk
  have hμa : AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ n) φ := analyticOnNhd_muSeq_complex38 n φ hgk
  have hT : AnalyticAt ℂ (terminalRoot n) φ := terminalRoot_analytic n φ hφB
  have hC : AnalyticAt ℂ (fun ψ : PotPair => ownCorrection n ψ (muSeq ψ n)) φ :=
    ownCorrection_at_dirichlet_analytic n φ hφB
  have hJ : AnalyticAt ℂ (fun ψ : PotPair => (ψ, muSeq ψ n)) φ := analyticAt_id.prod hμa
  have hδ : AnalyticAt ℂ (fun ψ : PotPair => antiDiscrim ψ (muSeq ψ n)) φ :=
    AnalyticAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ n))
      (analyticOnNhd_antiDiscrim (φ, muSeq φ n) (Set.mem_univ _)) hJ
  have hqa : AnalyticAt ℂ (radiusQuotient n) φ := hq φ hφV
  -- the first factor and the leading function
  set L : PotPair → ℂ := fun ψ => 2 * (tauN ψ n - muSeq ψ n) + 2 * (a : ℂ) * terminalRoot n ψ with hLdef
  set c' : PotPair → ℂ := fun ψ => -((a : ℂ) * (terminalRoot n ψ * ownCorrection n ψ (muSeq ψ n))) with hcdef
  have hLa : AnalyticAt ℂ L φ :=
    (analyticAt_const.mul (hτ.sub hμa)).add (analyticAt_const.mul hT)
  have hca : AnalyticAt ℂ c' φ := (analyticAt_const.mul (hT.mul hC)).neg
  have hLead_a : AnalyticAt ℂ (cartesianLeading n a) φ := by
    have : cartesianLeading n a = fun ψ : PotPair =>
        2 * (tauN ψ n - muSeq ψ n) + 2 * (a : ℂ) * Complex.I * radiusQuotient n ψ *
          antiDiscrim ψ (muSeq ψ n) := by
      funext ψ; rfl
    rw [this]
    exact (analyticAt_const.mul (hτ.sub hμa)).add
      ((((analyticAt_const.mul analyticAt_const).mul hqa)).mul hδ)
  have hLeq : L =ᶠ[𝓝 φ] cartesianLeading n a := by
    filter_upwards [hVo.mem_nhds hφV] with ψ hψV
    have hs := signedRadius_eq_radiusQuotient_mul_antiDiscrim n ψ (hVS hψV) (hψ ψ hψV)
    have hs' : -Complex.I * terminalRoot n ψ = radiusQuotient n ψ * antiDiscrim ψ (muSeq ψ n) := hs
    have hRI : terminalRoot n ψ = Complex.I * (radiusQuotient n ψ * antiDiscrim ψ (muSeq ψ n)) := by
      linear_combination Complex.I * hs' + terminalRoot n ψ * Complex.I_mul_I
    show 2 * (tauN ψ n - muSeq ψ n) + 2 * (a : ℂ) * terminalRoot n ψ =
      2 * (tauN ψ n - muSeq ψ n) + 2 * (a : ℂ) * Complex.I * radiusQuotient n ψ *
        antiDiscrim ψ (muSeq ψ n)
    rw [hRI]; ring
  have hL0 : L φ = 0 := by
    show 2 * (tauN φ n - muSeq φ n) + 2 * (a : ℂ) * terminalRoot n φ = 0
    rw [hA, hR]; ring
  have hc0 : c' φ = 0 := by
    show -((a : ℂ) * (terminalRoot n φ * ownCorrection n φ (muSeq φ n))) = 0
    rw [hR]; ring
  have hLead0 : cartesianLeading n a φ = 0 := by
    exact hLeq.eq_of_nhds.symm.trans hL0
  -- Z = L * exp c'
  have hZeq : cartesianZExtended n a = fun ψ => L ψ * Complex.exp (c' ψ) := by
    funext ψ; exact g5002_Z_formula n a ha ψ
  set D : PotPair →L[ℂ] ℂ := fderiv ℂ (cartesianLeading n a) φ with hD
  have hHLead : HasFDerivAt (cartesianLeading n a) D φ := hLead_a.differentiableAt.hasFDerivAt
  have hHL : HasFDerivAt L D φ := hHLead.congr_of_eventuallyEq hLeq
  have hHc : HasFDerivAt c' (fderiv ℂ c' φ) φ := hca.differentiableAt.hasFDerivAt
  have hHE : HasFDerivAt (fun ψ => Complex.exp (c' ψ)) (Complex.exp (c' φ) • fderiv ℂ c' φ) φ :=
    hHc.cexp
  have hHZ0 := hHL.mul hHE
  have hHZ : HasFDerivAt (cartesianZExtended n a) D φ := by
    rw [hZeq]
    have : D = L φ • (Complex.exp (c' φ) • fderiv ℂ c' φ) + Complex.exp (c' φ) • D := by
      rw [hL0, hc0]; refine ContinuousLinearMap.ext fun x => ?_; simp
    rw [this]; exact hHZ0
  exact ⟨D, hHZ, hHLead, (G4032 n a ha φ hφB hu hμ).1, hLead0⟩

theorem G5002 (n a : ℤ) (ha : a = 1 ∨ a = -1)
    (u : PhysicalL2) (hu : gamma2 (realSlice u) n = 0) :
  cartesianZExtended n a (realSlice u) = 0 ∧ cartesianLeading n a (realSlice u) = 0 ∧
  DifferentiableAt ℝ (fun v : PhysicalL2 => cartesianZExtended n a (realSlice v)) u ∧
  DifferentiableAt ℝ (fun v : PhysicalL2 => cartesianLeading n a (realSlice v)) u ∧
  fderiv ℝ (fun v : PhysicalL2 => cartesianZExtended n a (realSlice v)) u =
    fderiv ℝ (fun v : PhysicalL2 => cartesianLeading n a (realSlice v)) u := by
  obtain ⟨D, hHZ, hHLead, hz, hl⟩ := g5002_complex n a ha u hu
  have hR1 : HasFDerivAt (fun v : PhysicalL2 => cartesianZExtended n a (realSlice v))
      ((D.restrictScalars ℝ).comp (realSlice : PhysicalL2 →L[ℝ] PotPair)) u :=
    HasFDerivAt.comp (g := cartesianZExtended n a) u (hHZ.restrictScalars ℝ) realSlice.hasFDerivAt
  have hR2 : HasFDerivAt (fun v : PhysicalL2 => cartesianLeading n a (realSlice v))
      ((D.restrictScalars ℝ).comp (realSlice : PhysicalL2 →L[ℝ] PotPair)) u :=
    HasFDerivAt.comp (g := cartesianLeading n a) u (hHLead.restrictScalars ℝ) realSlice.hasFDerivAt
  exact ⟨hz, hl, hR1.differentiableAt, hR2.differentiableAt, by rw [hR1.fderiv, hR2.fderiv]⟩

end
end NlsGge.GKDefinitionDesign
