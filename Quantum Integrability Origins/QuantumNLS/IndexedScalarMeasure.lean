import Mathlib
import QuantumNLS.SpatialTransfer
import QuantumNLS.IndexedMasses

/-!
# DEF-043: indexed scalar measure used in the separation argument

Source: `DEFINITIONS_LEDGER.md:949` (DEF-043), `chapters/propagation/label_periods.tex`, `def:PF-indexed-scalar`.
Ledger text (summarized): `μ` is a nonatomic probability measure on `ℝ`, `G_μ(z) = ∫ dμ(t)/(z−t)`,
`F(x) = Lx − 2κ G_μ(x)` for `x ∉ supp μ`.  Assume the upper boundary value of `Re G_μ` exists and is the locally
uniform limit on compact real intervals of `Re G_μ(· + iε)` as `ε ↓ 0` (the weaker condition — local boundedness
uniform in `ε` together with pointwise convergence `μ`-a.e. — also suffices).  Put
`n(t) = Lt/(2π) − κ Re G_μ(t + i0)/π` and assume it is integer valued `μ`-a.e.  At each regular cut `x` with
`2πa < F(x) < 2π(a+1)` assume `n(t) ≤ a` for `μ`-a.e. `t < x` and `n(t) ≥ a + 1` for `μ`-a.e. `t > x`.  These are scalar
assumptions (properties of the quantum-derived indexed rapidity measure in the intended application); no
classical nonlinear Fourier map is part of the definition.

## Realization (literal; the hypotheses are explicit structure fields)
`IndexedScalarMeasure L κ` bundles `L, κ > 0`, a measure `μ` that is a probability measure (`isProb`) without atoms
(`noAtoms`), the boundary function `reG` of `Re G_μ`, and the fields
* `boundary`: `LocallyUniformBoundary μ reG ∨ BoundedAEBoundary μ reG` (the displayed locally-uniform alternative, or
  the weaker bounded-a.e. alternative);
* `integer_ae`: `n(t) = L t/(2π) − κ reG(t)/π` is integer valued `μ`-a.e.;
* `separation`: for every `x ∉ supp μ` (a *regular cut*, where `F` is defined) and integer `a` with
  `2πa < F(x) < 2π(a+1)`: `n ≤ a` a.e. on `t < x` and `a + 1 ≤ n` a.e. on `t > x`.
The regular-cut reading `x ∉ supp μ` is the only place where the ledger's wording ("regular cut") is interpreted
(the ledger defines `F` on `ℝ \ supp μ`); the order `a` is taken integer.

## Facts proved (the ones the ledger asserts as part of the definition)
* `exteriorForce_eq`: for `x ∉ supp μ` — in fact for every real `x` — `G_μ(x)` is real, so `F(x)` is real and
  `F(x) = Lx − 2κ ∫ dμ(t)/(x−t)` (`cauchyTransform_real`).
* Link to DEF-013: `F(x) = 2 Re γ(x)` with `γ = boundaryPhase L κ μ` (`exteriorForce_eq_two_re_phase`), and
  `n(t) = φ(t)/π` for `φ(t) = Lt/2 − κ reG(t)` (`indexLabel_eq_phase_div`), so the DEF-014 separator level
  `φ(b_n) = (n + 1/2)π` is `n(b_n) = n + 1/2`.
Not proved here (not part of the definition): that any particular `μ` (e.g. `M_{κ,u}/‖u‖²`) satisfies the fields.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace QuantumNLS.IndexedScalarMeasure

open QuantumNLS.EmpiricalRapidity (cauchyTransform)

/-- `Re G_μ(t + iε)`. -/
def reCauchy (μ : Measure ℝ) (t ε : ℝ) : ℝ := (cauchyTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).re

/-- The upper boundary value of `Re G_μ` is the locally uniform limit on compact real intervals. -/
def LocallyUniformBoundary (μ : Measure ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn (fun ε t => reCauchy μ t ε) g (𝓝[>] 0) K

/-- The weaker alternative: local boundedness uniformly in `ε`, with `μ`-a.e. pointwise convergence. -/
def BoundedAEBoundary (μ : Measure ℝ) (g : ℝ → ℝ) : Prop :=
  (∀ K : Set ℝ, IsCompact K → ∃ C δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo 0 δ, ∀ t ∈ K, |reCauchy μ t ε| ≤ C) ∧
    ∀ᵐ t ∂μ, Tendsto (fun ε => reCauchy μ t ε) (𝓝[>] 0) (𝓝 (g t))

/-- Exterior force `F(x) = Lx − 2κ G_μ(x)` (real part; `G_μ(x)` is real for real `x`, see
`cauchyTransform_real`). -/
def exteriorForce (L κ : ℝ) (μ : Measure ℝ) (x : ℝ) : ℝ :=
  L * x - 2 * κ * (cauchyTransform μ (x : ℂ)).re

/-- The label function `n(t) = Lt/(2π) − κ reG(t)/π`. -/
def indexLabel (L κ : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ := L * t / (2 * Real.pi) - κ * g t / Real.pi

/-- **DEF-043**: indexed scalar measure with the displayed hypotheses as explicit fields. -/
structure IndexedScalarMeasure (L κ : ℝ) where
  hL : 0 < L
  hκ : 0 < κ
  μ : Measure ℝ
  isProb : IsProbabilityMeasure μ
  noAtoms : NoAtoms μ
  reG : ℝ → ℝ
  boundary : LocallyUniformBoundary μ reG ∨ BoundedAEBoundary μ reG
  integer_ae : ∀ᵐ t ∂μ, ∃ k : ℤ, indexLabel L κ reG t = k
  separation : ∀ x : ℝ, x ∉ μ.support → ∀ a : ℤ,
    2 * Real.pi * a < exteriorForce L κ μ x → exteriorForce L κ μ x < 2 * Real.pi * (a + 1) →
      (∀ᵐ t ∂μ, t < x → indexLabel L κ reG t ≤ a) ∧
      (∀ᵐ t ∂μ, x < t → (a : ℝ) + 1 ≤ indexLabel L κ reG t)

/-- `G_μ(x)` is real for real `x` (the integrand `(x − t)⁻¹` is real). -/
theorem cauchyTransform_real (μ : Measure ℝ) (x : ℝ) :
    cauchyTransform μ (x : ℂ) = ((∫ t : ℝ, (x - t)⁻¹ ∂μ : ℝ) : ℂ) := by
  unfold cauchyTransform
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp

theorem cauchyTransform_im_real (μ : Measure ℝ) (x : ℝ) : (cauchyTransform μ (x : ℂ)).im = 0 := by
  rw [cauchyTransform_real]; exact Complex.ofReal_im _

/-- For real `x`: `F(x) = Lx − 2κ ∫ dμ(t)/(x − t)`. -/
theorem exteriorForce_eq (L κ : ℝ) (μ : Measure ℝ) (x : ℝ) :
    exteriorForce L κ μ x = L * x - 2 * κ * ∫ t : ℝ, (x - t)⁻¹ ∂μ := by
  unfold exteriorForce
  rw [cauchyTransform_real, Complex.ofReal_re]

/-- Link to DEF-013: `F(x) = 2 Re γ(x)` for `γ = boundaryPhase L κ μ`. -/
theorem exteriorForce_eq_two_re_phase (L κ : ℝ) (μ : Measure ℝ) (x : ℝ) :
    exteriorForce L κ μ x = 2 * (QuantumNLS.SpatialTransfer.boundaryPhase L κ μ (x : ℂ)).re := by
  unfold exteriorForce QuantumNLS.SpatialTransfer.boundaryPhase
  simp only [Complex.sub_re, Complex.mul_re, Complex.div_ofNat_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- `n(t) = φ(t)/π` with `φ(t) = L t/2 − κ reG(t)`; the DEF-014 separator level `φ(b_n) = (n + 1/2)π` reads
`n(b_n) = n + 1/2`. -/
theorem indexLabel_eq_phase_div (L κ : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    indexLabel L κ g t = (L * t / 2 - κ * g t) / Real.pi := by
  unfold indexLabel
  have := Real.pi_pos.ne'
  field_simp

end QuantumNLS.IndexedScalarMeasure

#print axioms QuantumNLS.IndexedScalarMeasure.cauchyTransform_real
#print axioms QuantumNLS.IndexedScalarMeasure.exteriorForce_eq
#print axioms QuantumNLS.IndexedScalarMeasure.exteriorForce_eq_two_re_phase
#print axioms QuantumNLS.IndexedScalarMeasure.indexLabel_eq_phase_div
