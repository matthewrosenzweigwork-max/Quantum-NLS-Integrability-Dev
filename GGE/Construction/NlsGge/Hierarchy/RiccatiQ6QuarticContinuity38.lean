import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! Batch 38, A01.05 (continuity part): the quartic functional
`F(f) = ∫₀¹ (14 f² (f'')² - 7 (f')⁴)` (paper/v2.tex line 2457) is
Lipschitz under uniform `C²` closeness. Tactic-level variation: the source uses
continuity on `H²`; uniform `C²` convergence of the approximants is a stronger
input and makes this step elementary. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff

/-- The pointwise quartic density `14 a² c² - 7 b⁴` (`a = f`, `b = f'`, `c = f''`). -/
def quarticDensity38 (a b c : ℝ) : ℝ := 14 * a ^ 2 * c ^ 2 - 7 * b ^ 4

theorem quarticDensity38_lipschitz (R δ a b c a0 b0 c0 : ℝ) (hR : 0 ≤ R)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ha0 : |a0| ≤ R) (hb0 : |b0| ≤ R) (hc0 : |c0| ≤ R)
    (ha : |a - a0| ≤ δ) (hb : |b - b0| ≤ δ) (hc : |c - c0| ≤ δ) :
    |quarticDensity38 a b c - quarticDensity38 a0 b0 c0| ≤ 100 * (R + 1) ^ 3 * δ := by
  have ha' : |a| ≤ R + 1 := by
    calc |a| = |(a - a0) + a0| := by ring_nf
      _ ≤ |a - a0| + |a0| := abs_add_le _ _
      _ ≤ R + 1 := by linarith
  have hb' : |b| ≤ R + 1 := by
    calc |b| = |(b - b0) + b0| := by ring_nf
      _ ≤ |b - b0| + |b0| := abs_add_le _ _
      _ ≤ R + 1 := by linarith
  have hc' : |c| ≤ R + 1 := by
    calc |c| = |(c - c0) + c0| := by ring_nf
      _ ≤ |c - c0| + |c0| := abs_add_le _ _
      _ ≤ R + 1 := by linarith
  have hac : |a * c - a0 * c0| ≤ (2 * R + 1) * δ := by
    have : a * c - a0 * c0 = a * (c - c0) + c0 * (a - a0) := by ring
    rw [this]
    calc |a * (c - c0) + c0 * (a - a0)| ≤ |a| * |c - c0| + |c0| * |a - a0| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ (R + 1) * δ + R * δ := by
          gcongr
      _ = (2 * R + 1) * δ := by ring
  have hacs : |a * c + a0 * c0| ≤ 2 * (R + 1) ^ 2 := by
    calc |a * c + a0 * c0| ≤ |a| * |c| + |a0| * |c0| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ (R + 1) * (R + 1) + R * R := by
          gcongr
      _ ≤ 2 * (R + 1) ^ 2 := by nlinarith
  have hbb : |b + b0| ≤ 2 * R + 1 := by
    calc |b + b0| ≤ |b| + |b0| := abs_add_le _ _
      _ ≤ 2 * R + 1 := by linarith
  have hbs : |b ^ 2 + b0 ^ 2| ≤ 2 * (R + 1) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have h1 : b ^ 2 ≤ (R + 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
    have h2 : b0 ^ 2 ≤ (R + 1) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb0.trans (by linarith)) 2
    linarith
  have e : quarticDensity38 a b c - quarticDensity38 a0 b0 c0 =
      14 * ((a * c - a0 * c0) * (a * c + a0 * c0)) -
        7 * ((b - b0) * (b + b0) * (b ^ 2 + b0 ^ 2)) := by
    unfold quarticDensity38; ring
  rw [e]
  have t1 : |a * c - a0 * c0| * |a * c + a0 * c0| ≤ (2 * R + 1) * δ * (2 * (R + 1) ^ 2) :=
    mul_le_mul hac hacs (abs_nonneg _) (by positivity)
  have t2 : |b - b0| * |b + b0| * |b ^ 2 + b0 ^ 2| ≤ δ * (2 * R + 1) * (2 * (R + 1) ^ 2) :=
    mul_le_mul (mul_le_mul hb hbb (abs_nonneg _) hδ0) hbs (abs_nonneg _) (by positivity)
  calc |14 * ((a * c - a0 * c0) * (a * c + a0 * c0)) -
        7 * ((b - b0) * (b + b0) * (b ^ 2 + b0 ^ 2))|
      ≤ 14 * (|a * c - a0 * c0| * |a * c + a0 * c0|) +
          7 * (|b - b0| * |b + b0| * |b ^ 2 + b0 ^ 2|) := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
        norm_num
    _ ≤ 14 * ((2 * R + 1) * δ * (2 * (R + 1) ^ 2)) +
          7 * (δ * (2 * R + 1) * (2 * (R + 1) ^ 2)) := by gcongr
    _ ≤ 100 * (R + 1) ^ 3 * δ := by nlinarith [mul_nonneg hδ0 (pow_nonneg (by linarith : (0:ℝ) ≤ R + 1) 2)]

private theorem contDiff_iteratedDeriv_continuous38 (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (k : ℕ) : Continuous (iteratedDeriv k g) :=
  hg.continuous_iteratedDeriv k (by exact_mod_cast le_top)

/-- The quartic functional is Lipschitz in uniform `C²` distance (on `[0,1]`). -/
theorem quarticFunctional38_close (f P : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hP : ContDiff ℝ ∞ P) (R δ : ℝ) (hR : 0 ≤ R) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hfR : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |f x| ≤ R ∧ |deriv f x| ≤ R ∧ |iteratedDeriv 2 f x| ≤ R)
    (hclose : ∀ x, |P x - f x| ≤ δ ∧ |deriv P x - deriv f x| ≤ δ ∧
      |iteratedDeriv 2 P x - iteratedDeriv 2 f x| ≤ δ) :
    |(∫ x in (0:ℝ)..1, quarticDensity38 (P x) (deriv P x) (iteratedDeriv 2 P x)) -
      ∫ x in (0:ℝ)..1, quarticDensity38 (f x) (deriv f x) (iteratedDeriv 2 f x)| ≤
      100 * (R + 1) ^ 3 * δ := by
  have hcont : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
      Continuous (fun x => quarticDensity38 (g x) (deriv g x) (iteratedDeriv 2 g x)) := by
    intro g hg
    have h0 : Continuous g := hg.continuous
    have h1 : Continuous (deriv g) := hg.continuous_deriv (by exact_mod_cast le_top)
    have h2 : Continuous (iteratedDeriv 2 g) :=
      contDiff_iteratedDeriv_continuous38 g hg 2
    unfold quarticDensity38
    fun_prop
  rw [← intervalIntegral.integral_sub ((hcont P hP).intervalIntegrable _ _)
    ((hcont f hf).intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := 100 * (R + 1) ^ 3 * δ)
    (f := fun x => quarticDensity38 (P x) (deriv P x) (iteratedDeriv 2 P x) -
      quarticDensity38 (f x) (deriv f x) (iteratedDeriv 2 f x)) (by
      intro x hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx.1.le, hx.2⟩
      obtain ⟨h0, h1, h2⟩ := hfR x hx'
      obtain ⟨c0, c1, c2⟩ := hclose x
      rw [Real.norm_eq_abs]
      exact quarticDensity38_lipschitz R δ _ _ _ _ _ _ hR hδ0 hδ1 h0 h1 h2 c0 c1 c2)
  simpa [Real.norm_eq_abs] using this

end NlsGge.HierarchyRiccati.Core

end
