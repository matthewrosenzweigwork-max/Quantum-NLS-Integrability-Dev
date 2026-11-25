import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.GK38.AbelianStdRootAverage
import NlsGge.GK38.StdRootBranchesSlit
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.GK38.IsolatingDistance

/- G2-020 PROOF01 (proof development, AUTHOR; not self-reviewed).
   Statement copied from STATEMENTS/G2.md G2-020 (no weakening).
   Imports the landed G2019 module for `standardRoot` (NlsGge.GKDefinitionDesign) and
   `g2019_standardRoot_pair`, `g2019_closed_ball_dist`.
   Production used: p2StdRoot_cosine_average38 (AbelianStdRootAverage.lean) for the
   diagonal m = n case at f = 1 (value -i * 2 pi), stdRoot_slit38 / stdRoot_analyticAt38
   / stdRoot_ne_zero38 for analyticity off the cut, and Mathlib
   Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (Cauchy disc) for m != n. -/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g2020_stdRoot_analytic (a b z : ℂ) (hz : z ∉ segment ℝ a b) :
    AnalyticAt ℂ (stdRoot38 ((a + b) / 2) ((b - a) ^ 2)) z := by
  have hs := stdRoot_slit38 a b z hz
  exact stdRoot_analyticAt38 analyticAt_const analyticAt_const analyticAt_id hs.1 hs.2

theorem g2020_diag (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (n : ℤ) (hr : 0 < R n)
    (hsp : IsolatingSpectral38 φ C R) :
    CircleIntegrable (fun z => (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
        ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹) (C n) (R n) ∧
    circleIntegral (fun z => (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
        ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹) (C n) (R n) = -2 * (Real.pi : ℂ) * Complex.I := by
  have hcut := (hsp.1 n).1
  have hk := p2StdRoot_cosine_average38 (lamMinus φ n) (lamPlus φ n) (C n) (R n) hr hcut
    (fun _ => (1 : ℂ)) analyticOnNhd_const
  obtain ⟨hint, -, hval⟩ := hk
  refine ⟨?_, ?_⟩
  · simpa only [one_div] using hint
  · have hv : circleIntegral (fun z => (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
        ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹) (C n) (R n) = -Complex.I * (2 * (Real.pi : ℂ)) := by
      simpa [one_div, intervalIntegral.integral_const, Complex.real_smul] using hval
    rw [hv]
    ring

theorem g2020_off (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (hsp : IsolatingSpectral38 φ C R) (m n : ℤ) (hmn : m ≠ n) :
    CircleIntegrable (fun z => (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
        ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹) (C m) (R m) ∧
    circleIntegral (fun z => (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
        ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹) (C m) (R m) = 0 := by
  have hr : 0 < R m := (hg.1 m).1
  have hcut := (hsp.1 n).1
  have hc1 : 1 ≤ c := hg.2.2.1
  have hc0 : 0 < c := by linarith
  have hd1 : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hD : c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ballDistance38 (C m) (C n) (R m) (R n) :=
    (hg.2.2.2.1 m n hmn).1
  have hpos : 0 < c⁻¹ * |((m - n : ℤ) : ℝ)| := mul_pos (inv_pos.mpr hc0) (by linarith)
  have hnot : ∀ z ∈ closedBall (C m) (R m), z ∉ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
    intro z hz hzs
    have h0 := g2019_closed_ball_dist C R c N hg hz (hcut hzs)
    rw [dist_self] at h0
    linarith
  have hdiff : ∀ z ∈ closedBall (C m) (R m),
      AnalyticAt ℂ (fun z => (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
        ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹) z := fun z hz =>
    (g2020_stdRoot_analytic (lamMinus φ n) (lamPlus φ n) z (hnot z hz)).inv
      (stdRoot_ne_zero38 (lamMinus φ n) (lamPlus φ n) z (hnot z hz))
  have hcont : ContinuousOn (fun z => (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
      ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹) (closedBall (C m) (R m)) :=
    fun z hz => (hdiff z hz).continuousAt.continuousWithinAt
  refine ⟨ContinuousOn.circleIntegrable hr.le (hcont.mono sphere_subset_closedBall), ?_⟩
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    Set.countable_empty hcont (fun z hz => (hdiff z (ball_subset_closedBall hz.1)).differentiableAt)

theorem G2_020 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hCR : IsolatingFamily38 φ C R) (m n : ℤ) :
    CircleIntegrable (fun z => (standardRoot φ n z)⁻¹) (C m) (R m) ∧
    circleIntegral (fun z => (standardRoot φ n z)⁻¹) (C m) (R m) =
      if m=n then -2*(Real.pi : ℂ)*Complex.I else 0 := by
  obtain ⟨c, N, hg, hsp⟩ := hCR
  have hfun : (fun z => (standardRoot φ n z)⁻¹) = fun z =>
      (stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2) ((lamPlus φ n - lamMinus φ n) ^ 2) z)⁻¹ :=
    funext fun z => by rw [g2019_standardRoot_pair φ hφ n z]
  rw [hfun]
  by_cases hmn : m = n
  · rw [if_pos hmn, hmn]
    exact g2020_diag φ C R n (hg.1 n).1 hsp
  · rw [if_neg hmn]
    exact g2020_off φ C R c N hg hsp m n hmn

end
end NlsGge.GKDefinitionDesign
