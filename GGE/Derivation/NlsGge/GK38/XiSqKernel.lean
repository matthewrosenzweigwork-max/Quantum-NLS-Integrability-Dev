import NlsGge.GK38.XiSqCandidates
import NlsGge.GK38.XiSqChi

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

/-- Actual analytic coefficient already identified by D4, including complex collapsed gaps. -/
def a5CriticalA38 (n : ℤ) (φ : PotPair) : ℂ :=
  criticalCoefficient38 discC discR φ n

theorem a5CriticalA_analytic38 (n : ℤ) : AnalyticOnNhd ℂ (a5CriticalA38 n) gkW := by
  intro φ hφ
  change AnalyticAt ℂ (fun ψ => deriv (exteriorFactor38 ψ n) (lamDot ψ n) /
    (4 * criticalDenominator38 discC discR ψ n)) φ
  exact (exterior_deriv_critical_analytic38 n φ hφ).div
    (analyticAt_const.mul (critical_denominator_analytic38 discC discR
      isolating_selectors_admissible38 n φ hφ))
    (mul_ne_zero (by norm_num) (critical_denominator_nonzero38 discC discR
      isolating_selectors_admissible38 φ hφ n))

theorem a5CriticalA_identity38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) :
    lamDot φ n - tauN φ n = gamma2 φ n * a5CriticalA38 n φ :=
  critical_coefficient_identity38 discC discR isolating_selectors_admissible38 φ hφ n

def a5BoundaryQ38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  Complex.sqrt (1 - (gamma2 p.1 n / 4) / (tauN p.1 n - p.2)^2)

/-- Actual cut geometry fixes the principal branch and its nonzero denominators. -/
theorem a5BoundaryQ_properties38 (n : ℤ) (p : PotPair × ℂ) (hp : p ∈ rootDomain38) :
    tauN p.1 n - p.2 ≠ 0 ∧ a5BoundaryQ38 n p ≠ 0 ∧ 1 + a5BoundaryQ38 n p ≠ 0 ∧
      a5BoundaryQ38 n p ^ 2 = 1 - (gamma2 p.1 n / 4) / (tauN p.1 n - p.2)^2 := by
  have hs := stdRoot_slit38 (lamMinus p.1 n) (lamPlus p.1 n) p.2
    (rootDomain_avoids38 hp n)
  rw [add_comm (lamMinus p.1 n), ← tauN_value38 p.1 hp.1 n,
    ← gamma2_value38 p.1 hp.1 n] at hs
  have hstd : stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2 ≠ 0 := by
    intro he
    exact rootFactor_ne_zero38 n p hp (by simp [rootFactor38, he])
  have hq : a5BoundaryQ38 n p ≠ 0 := by
    intro he
    apply hstd
    change (tauN p.1 n - p.2) * a5BoundaryQ38 n p = 0
    rw [he, mul_zero]
  have hplus : 1 + a5BoundaryQ38 n p ≠ 0 := by
    have hre := Lib.re_sqrt_nonneg
      (1 - (gamma2 p.1 n / 4) / (tauN p.1 n - p.2)^2)
    change 0 ≤ (a5BoundaryQ38 n p).re at hre
    intro he
    have hreal := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hreal
    linarith
  exact ⟨hs.1, hq, hplus, Lib.sqrt_sq _⟩

theorem a5BoundaryQ_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (a5BoundaryQ38 n) rootDomain38 := by
  intro p hp
  have hs := stdRoot_slit38 (lamMinus p.1 n) (lamPlus p.1 n) p.2
    (rootDomain_avoids38 hp n)
  rw [add_comm (lamMinus p.1 n), ← tauN_value38 p.1 hp.1 n,
    ← gamma2_value38 p.1 hp.1 n] at hs
  have hτ := (tauN_analytic n p.1 hp.1).comp analyticAt_fst
  have hg := (gamma2_analytic n p.1 hp.1).comp analyticAt_fst
  have hw := hτ.sub analyticAt_snd
  have hr : AnalyticAt ℂ (fun q : PotPair × ℂ =>
      1 - (gamma2 q.1 n / 4) / (tauN q.1 n - q.2)^2) p :=
    analyticAt_const.sub ((hg.div_const (c := (4 : ℂ))).div (hw.pow 2) (pow_ne_zero 2 hs.1))
  exact hr.cpow analyticAt_const hs.2

/-- Scalar rationalization has no gap-square nonzero hypothesis. -/
theorem a5InverseRootDecomposition38 (w q g : ℂ) (hw : w ≠ 0) (hq : q ≠ 0)
    (hplus : 1 + q ≠ 0) (hsq : q^2 = 1 - (g / 4) / w^2) :
    1 / q = 1 + g * (1 / (4 * w^2 * q * (1 + q))) := by
  have hpoly : 4 * w^2 * q^2 = 4 * w^2 - g := by
    calc
      4 * w^2 * q^2 = 4 * w^2 * (1 - (g / 4) / w^2) := by rw [hsq]
      _ = 4 * w^2 - g := by field_simp
  field_simp
  linear_combination -hpoly

def a5NormalizedKernel38 (n : ℤ) (p : PotPair × ℂ) : ℂ :=
  (p.2 * a5Chi38 n p / Complex.I) *
    (1 / (4 * (tauN p.1 n - p.2)^2 * a5BoundaryQ38 n p * (1 + a5BoundaryQ38 n p)) +
      a5CriticalA38 n p.1 / ((tauN p.1 n - p.2) * a5BoundaryQ38 n p))

/-- This identity includes every complex collapsed gap; no normalized action is assumed. -/
theorem a5ActionIntegrand_divisibility38 (n : ℤ) (p : PotPair × ℂ)
    (hp : p ∈ rootDomain38) :
    actionIntegrand38 p.1 p.2 = p.2 * a5Chi38 n p / Complex.I +
      gamma2 p.1 n * a5NormalizedKernel38 n p := by
  let w := tauN p.1 n - p.2
  let q := a5BoundaryQ38 n p
  let g := gamma2 p.1 n
  let a := a5CriticalA38 n p.1
  obtain ⟨hw, hq, hplus, hsq⟩ := a5BoundaryQ_properties38 n p hp
  have hinv := a5InverseRootDecomposition38 w q g hw hq hplus hsq
  have hδ := a5CriticalA_identity38 n p.1 hp.1
  have hdot : lamDot p.1 n - p.2 = w + g * a := by
    dsimp [w, g, a]
    linear_combination hδ
  have hratio := a5Chi_discrimDeriv_ratio38 n p hp
  have hstd : stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2 = w * q := rfl
  rw [hdot, hstd] at hratio
  have halgebra : (w + g * a) / (Complex.I * (w * q)) * a5Chi38 n p =
      (a5Chi38 n p / Complex.I) * (1 + g *
        (1 / (4 * w^2 * q * (1 + q)) + a / (w * q))) := by
    calc
      _ = (a5Chi38 n p / Complex.I) * (1 / q + g * (a / (w * q))) := by
        field_simp [show w ≠ 0 from hw, show q ≠ 0 from hq, Complex.I_ne_zero]
      _ = _ := by rw [hinv]; ring
  rw [halgebra] at hratio
  rw [actionIntegrand38, mul_div_assoc, hratio]
  dsimp [a5NormalizedKernel38]
  change p.2 * ((a5Chi38 n p / Complex.I) * (1 + g *
    (1 / (4 * w^2 * q * (1 + q)) + a / (w * q)))) =
    p.2 * a5Chi38 n p / Complex.I + g * ((p.2 * a5Chi38 n p / Complex.I) *
      (1 / (4 * w^2 * q * (1 + q)) + a / (w * q)))
  ring

theorem a5NormalizedKernel_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (a5NormalizedKernel38 n) rootDomain38 := by
  intro p hp
  have hp' : p ∈ a5OmittedRootDomain38 n :=
    ⟨hp.1, fun m _ => rootDomain_avoids38 hp m⟩
  have hw := ((tauN_analytic n p.1 hp.1).comp analyticAt_fst).sub analyticAt_snd
  have hq := a5BoundaryQ_analytic38 n p hp
  have ha := (a5CriticalA_analytic38 n p.1 hp.1).comp analyticAt_fst
  have hc := a5Chi_analytic38 n p hp'
  obtain ⟨hwne, hqne, hplus, _⟩ := a5BoundaryQ_properties38 n p hp
  have hfirst : AnalyticAt ℂ (fun q : PotPair × ℂ =>
      1 / (4 * (tauN q.1 n - q.2)^2 * a5BoundaryQ38 n q * (1 + a5BoundaryQ38 n q))) p :=
    analyticAt_const.div
    (((analyticAt_const.mul (hw.pow 2)).mul hq).mul (analyticAt_const.add hq))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hwne)) hqne) hplus)
  have hsecond := ha.div (hw.mul hq) (mul_ne_zero hwne hqne)
  exact ((analyticAt_snd.mul hc).div_const).mul (hfirst.add hsecond)

end
end NlsGge.GK38
