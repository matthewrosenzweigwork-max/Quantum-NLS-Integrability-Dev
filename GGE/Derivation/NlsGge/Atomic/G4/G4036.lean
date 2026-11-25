import Mathlib
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036H1
import NlsGge.Atomic.G4.G4036H2
import NlsGge.Atomic.G4.G4036H3
import NlsGge.Atomic.G5.G5001
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.TauGamma

/- G4-036 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4036.lean.
   Head `G4036` verbatim from Pro round 9 section 11 / round 10 section 9 (commit 178f84d6), over the host
   G4036Host (cartesianZExtended etc.) and the three proved inputs terminalRoot_analytic (G4036H1),
   ownCorrection_analytic_and_ode (G4036H2) and ownCorrection_at_dirichlet_analytic (G4036H3). The landed
   public `cartesianX`/`cartesianY` (G5033Host) are untouched. Assembly: split a = 1 / a = -1, then
   products, sums and Complex.exp of the analytic functions tauN, muSeq, terminalRoot and
   phi -> ownCorrection n phi (muSeq phi n) on sourceBetaW. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G4036 (n a : ℤ) (ha : a = 1 ∨ a = -1) :
  AnalyticOnNhd ℂ (cartesianZExtended n a) sourceBetaW := by
  intro φ hφ
  have hgk : φ ∈ gkW := g5001_gk φ hφ
  have hτ : AnalyticAt ℂ (fun ψ : PotPair => tauN ψ n) φ := tauN_analytic n φ hgk
  have hμ : AnalyticAt ℂ (fun ψ : PotPair => muSeq ψ n) φ := analyticOnNhd_muSeq_complex38 n φ hgk
  have hT : AnalyticAt ℂ (terminalRoot n) φ := terminalRoot_analytic n φ hφ
  have hC : AnalyticAt ℂ (fun ψ : PotPair => ownCorrection n ψ (muSeq ψ n)) φ :=
    ownCorrection_at_dirichlet_analytic n φ hφ
  have hd : AnalyticAt ℂ (fun ψ : PotPair => 2 * (tauN ψ n - muSeq ψ n)) φ :=
    analyticAt_const.mul (hτ.sub hμ)
  have hTC : AnalyticAt ℂ (fun ψ : PotPair => terminalRoot n ψ * ownCorrection n ψ (muSeq ψ n)) φ :=
    hT.mul hC
  have h2T : AnalyticAt ℂ (fun ψ : PotPair => 2 * terminalRoot n ψ) φ := analyticAt_const.mul hT
  rcases ha with rfl | rfl
  · have hfun : cartesianZExtended n 1 = fun ψ : PotPair =>
        (2 * (tauN ψ n - muSeq ψ n) + 2 * terminalRoot n ψ) *
          Complex.exp (-(terminalRoot n ψ * ownCorrection n ψ (muSeq ψ n))) := by
      funext ψ
      simp [cartesianZExtended]
    rw [hfun]
    exact (hd.add h2T).mul hTC.neg.cexp
  · have hfun : cartesianZExtended n (-1) = fun ψ : PotPair =>
        (2 * (tauN ψ n - muSeq ψ n) - 2 * terminalRoot n ψ) *
          Complex.exp (terminalRoot n ψ * ownCorrection n ψ (muSeq ψ n)) := by
      funext ψ
      simp [cartesianZExtended]
    rw [hfun]
    exact (hd.sub h2T).mul hTC.cexp

end
end NlsGge.GKDefinitionDesign
