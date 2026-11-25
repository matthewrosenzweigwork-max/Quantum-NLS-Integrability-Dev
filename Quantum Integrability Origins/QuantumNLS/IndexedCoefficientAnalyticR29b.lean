import QuantumNLS.IndexedInverseSeriesR28b
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Holomorphy in the contour variable of the actual scalar inverse
coefficients. Partial derivatives are used to avoid assuming parameter
regularity of a chosen power-series expansion. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Set Metric Filter Topology
namespace QuantumNLS.IndexedCoefficientAnalyticR29b

/-- Repeated differentiation in the second coordinate. -/
def partialSecond (F : ℂ × ℂ → ℂ) : ℕ → (ℂ × ℂ → ℂ)
  | 0 => F
  | k+1 => fun p => fderiv ℂ (partialSecond F k) p (0,1)

theorem analytic_partialSecond {F : ℂ × ℂ → ℂ} {U : Set (ℂ × ℂ)}
    (hF : AnalyticOnNhd ℂ F U) (k : ℕ) : AnalyticOnNhd ℂ (partialSecond F k) U := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    intro p hp
    exact ((ContinuousLinearMap.apply ℂ ℂ (0,1)).analyticAt _).comp (ih p hp).fderiv

theorem partialSecond_eq_slice {F : ℂ × ℂ → ℂ} {U V : Set ℂ}
    (hF : AnalyticOnNhd ℂ F (U ×ˢ V)) (hV : IsOpen V)
    (k : ℕ) {z x : ℂ} (hz : z ∈ U) (hx : x ∈ V) :
    partialSecond F k (z,x) = iteratedDeriv k (fun a => F (z,a)) x := by
  induction k generalizing x with
  | zero => simp only [partialSecond,iteratedDeriv_zero]
  | succ k ih =>
    have he : (fun a => partialSecond F k (z,a)) =ᶠ[𝓝 x]
        iteratedDeriv k (fun a => F (z,a)) := by
      filter_upwards [hV.mem_nhds hx] with a ha
      exact ih ha
    have hd := ((analytic_partialSecond hF k) (z,x) ⟨hz,hx⟩).differentiableAt.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_const x z).prodMk (hasDerivAt_id x))
    rw [partialSecond,iteratedDeriv_succ]
    exact hd.deriv.symm.trans he.deriv_eq

open PhysicalTensor KernelDefinition KernelConvergence LocalPlacement
  IndexedInverseR28b IndexedTransferR28b IndexedInverseSeriesR28b Ext025A7
variable {L κ : ℝ} [Fact (0 < L)]

def jointCentered (κ : ℝ) (p : ℂ × ℂ) : ℂ := centered (L := L) κ p.1 p.2

theorem analytic_jointCentered (hκ : 0 < κ) (n : ℤ) :
    AnalyticOnNhd ℂ (jointCentered (L := L) κ) (tube L n ×ˢ ball 0 rstar) := by
  intro p hp
  have hi := (inverse_disk hκ n hp.1 (y := spectralMap κ L p.1 0+p.2)
    (by simpa only [add_sub_cancel_left] using mem_ball_zero_iff.mp hp.2)).2.2.2.1
  have hc : AnalyticAt ℂ (fun q : ℂ × ℂ => (q.1,spectralMap κ L q.1 0+q.2)) p :=
    analyticAt_fst.prod (((spectralMap_analyticAt κ L (p.1,0)).comp (x := p) (f := fun q : ℂ × ℂ => (q.1,0))
      (analyticAt_fst.prod analyticAt_const)).add analyticAt_snd)
  exact hi.comp (x := p) (f := fun q : ℂ × ℂ => (q.1,spectralMap κ L q.1 0+q.2)) hc

theorem coeff_eq_partial (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (k : ℕ) :
    coeff (L := L) κ z k = partialSecond (jointCentered (L := L) κ) k (z,0)/(k.factorial : ℂ) := by
  have hs := (series_represents hκ n hz).factorial_smul (1 : ℂ) k
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hs
  change k.factorial • coeff (L := L) κ z k = iteratedDeriv k (centered (L := L) κ z) 0 at hs
  have hp := partialSecond_eq_slice (analytic_jointCentered hκ n) isOpen_ball k hz
    (show (0 : ℂ) ∈ ball 0 rstar by simp [rstar])
  rw [hp]
  apply (eq_div_iff (by exact_mod_cast k.factorial_ne_zero : (k.factorial : ℂ) ≠ 0)).mpr
  simpa only [jointCentered,nsmul_eq_mul,mul_comm] using hs

/-- Each actual inverse coefficient is holomorphic on every source tube. -/
theorem analytic_coeff (hκ : 0 < κ) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (fun z => coeff (L := L) κ z k) (tube L n) := by
  intro z hz
  have hp := (analytic_partialSecond (analytic_jointCentered hκ n) k) (z,0)
    ⟨hz,by simp [rstar]⟩
  have ha := (hp.comp (x := z) (f := fun a : ℂ => (a,0))
    (analyticAt_id.prod analyticAt_const)).div_const (c := (k.factorial : ℂ))
  exact ha.congr (by
    filter_upwards [(LOCAL009R22Geometry.band_open _ _).mem_nhds hz] with w hw
    exact (coeff_eq_partial hκ n hw k).symm)

end QuantumNLS.IndexedCoefficientAnalyticR29b
#print axioms QuantumNLS.IndexedCoefficientAnalyticR29b.analytic_coeff
