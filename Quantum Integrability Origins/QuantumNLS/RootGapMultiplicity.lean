import Mathlib
import QuantumNLS.RootGapLocal
import QuantumNLS.PhysicalContinuousBoundary
import QuantumNLS.RootDensityIdentification
import QuantumNLS.RootDensityFormula

/-!
# R-0908DFDE `prop:root-gap-multiplicity` (`ROOT_gap_multiplicity.tex:8`)

For every `L²` input `u` and `κ > 0` (`Δ = L2SpatialTransfer.discriminant κ u`, `θ = Re (PhysicalContinuousBoundary.boundary hκ u)` the real boundary phase `θ_u`,
`M = PhysicalQuantumMeasure.measure hκ u`, `ρ = RootDensityIdentification.dens κ u` its density):

* (A) every zero of `Δ² - 4` is real and has `analyticOrderAt ≤ 2`;
* (B) a double zero `x` (`analyticOrderAt (Δ² - 4) x = 2`) has `|Δ| < 2` immediately on both sides;
* (D) for every `n` there are separators `a` with `θ a = (n+1/2)π` (onto);
* (C) for every integer `n`, `{x | θ x = nπ} = [b⁻,b⁺]` is a nonempty bounded closed interval lying strictly between any `a, a'` with `θ a = (n-1/2)π`, `θ a' = (n+1/2)π`
  (so a fortiori between the separators `a_{n-1}(u), a_n(u)` of R-2EAD2BB6), and exactly one of
  1. `b⁻ < b⁺`, `ρ > 0` on `(b⁻,b⁺)`, both endpoints are simple zeros of `Δ - 2(-1)^n`; or
  2. `b⁻ = b⁺`, the common point is a double zero of `Δ - 2(-1)^n`, and `I_n = M(a,a') = 0`;
  and `I_n = M(a,a') > 0 ↔ b⁻ < b⁺`.
The Hahn-Banach/series argument of the source is replaced where noted in `RootGapLocal` (vertical-ray limit instead of the extension of `v`).
Zero multiplicities are Mathlib's `analyticOrderAt` (orders of the entire functions `Δ² - 4` and `Δ - 2σ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootGapMultiplicity

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.PhysicalQuantumMeasure (measure)
open QuantumNLS.SpatialTransfer (boundaryPhase)
open QuantumNLS.EmpiricalRapidity (cauchyTransform)
open QuantumNLS.PhysicalContinuousBoundary (boundary continuous_boundary boundary_limit boundary_cosine boundary_im
  gap_constancy monotone_all onto_all boundary_zero)
open QuantumNLS.RootGapLocal
open QuantumNLS.RootDensityIdentification (dens)

variable {L κ : ℝ} [Fact (0 < L)]

/-- `σ_n = (-1)^n`. -/
def sgn (n : ℤ) : ℝ := (-1 : ℝ) ^ n

theorem sgn_cases (n : ℤ) : sgn n = 1 ∨ sgn n = -1 := by
  rcases Int.even_or_odd n with h | h
  · left; simp [sgn, h.neg_one_zpow]
  · right; simp [sgn, h.neg_one_zpow]

theorem sgn_sq (n : ℤ) : sgn n ^ 2 = 1 := by rcases sgn_cases n with h | h <;> simp [h]

abbrev Dl (κ : ℝ) (u : L2T L) : ℂ → ℂ := QuantumNLS.L2SpatialTransfer.discriminant κ u

/-! ## Basic facts -/

theorem re_cos (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cosh_ofReal_re,
    Complex.sinh_ofReal_re, Complex.cosh_ofReal_im, Complex.sinh_ofReal_im, Complex.cos_ofReal_im,
    Complex.sin_ofReal_im]
  simp

theorem cos_add_sgn (n : ℤ) (w : ℂ) : Complex.cos (w + (n : ℂ) * Real.pi) = (sgn n : ℂ) * Complex.cos w := by
  have h1 : Complex.sin ((n : ℂ) * Real.pi) = 0 := Complex.sin_int_mul_pi n
  have h2 : Complex.cos ((n : ℂ) * Real.pi) = (sgn n : ℂ) := by
    have := Complex.ofReal_cos ((n : ℝ) * Real.pi)
    rw [Real.cos_int_mul_pi] at this
    simp only [sgn]
    push_cast at this ⊢
    exact this.symm
  rw [Complex.cos_add, h1, h2]; ring

theorem cos_sgn (n : ℤ) : Complex.cos ((n : ℂ) * Real.pi) = (sgn n : ℂ) := by
  simpa using cos_add_sgn n 0

theorem im_phase_ge (hκ : 0 < κ) (u : L2T L) {z : ℂ} (hz : 0 < z.im) :
    L * z.im / 2 ≤ (boundaryPhase L κ (measure hκ u) z).im := by
  have hint := QuantumNLS.EmpiricalRapidity.integrable_cauchyIntegrand (measure hκ u) z hz.ne'
  have him : (cauchyTransform (measure hκ u) z).im = ∫ q : ℝ, (((z - (q : ℂ))⁻¹).im) ∂(measure hκ u) := by
    unfold cauchyTransform
    have := Complex.imCLM.integral_comp_comm hint
    simp only [Complex.imCLM_apply] at this
    exact this.symm
  have hneg : (cauchyTransform (measure hκ u) z).im ≤ 0 := by
    rw [him]
    refine integral_nonpos fun q => ?_
    simp only [Pi.zero_apply]
    rw [Complex.inv_im]
    have : (z - (q : ℂ)).im = z.im := by simp
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Complex.normSq_nonneg _)
  have : (boundaryPhase L κ (measure hκ u) z).im = L * z.im / 2 - κ * (cauchyTransform (measure hκ u) z).im := by
    unfold boundaryPhase
    simp [Complex.mul_im, Complex.sub_im]
    try ring
  rw [this]
  nlinarith

/-! ## Real zeros -/

theorem zeros_real' (hκ : 0 < κ) (u : L2T L) {z : ℂ} (hz : Dl κ u z ^ 2 - 4 = 0) : z.im = 0 :=
  zeros_real (QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ u)
    (fun x => QuantumNLS.L2DiscriminantRegularity.discriminant_real κ u x)
    (fun z hz => QuantumNLS.PhysicalUnconditionalTrace.upper_cosine hκ u hz)
    (fun z hz => QuantumNLS.PhysicalQuantumMeasure.im_phase_pos hκ u hz) hz

theorem hD (κ : ℝ) (u : L2T L) : Differentiable ℂ (Dl κ u) :=
  QuantumNLS.PhysicalUpperTraceIdentity.entire_discriminant κ u

theorem hreal (κ : ℝ) (u : L2T L) (x : ℝ) : (Dl κ u (x : ℂ)).im = 0 :=
  QuantumNLS.L2DiscriminantRegularity.discriminant_real κ u x

/-! ## The vertical ray at a point where the boundary phase is `nπ` -/

theorem ray_of_boundary (hκ : 0 < κ) (u : L2T L) (x0 : ℝ) (n : ℤ)
    (hb : boundary hκ u x0 = (n : ℂ) * Real.pi) :
    Dl κ u (x0 : ℂ) = 2 * (sgn n : ℂ) ∧ Ray (Dl κ u) L (sgn n) x0 := by
  have hL : 0 < L := Fact.out
  have hDx : Dl κ u (x0 : ℂ) = 2 * (sgn n : ℂ) := by
    have h := boundary_cosine hκ u x0
    rw [hb, cos_sgn] at h
    exact h.symm
  refine ⟨hDx, fun y => (boundaryPhase L κ (measure hκ u) ((x0 : ℂ) + (y : ℂ) * Complex.I) - (n : ℂ) * Real.pi) / 2,
    ?_, ?_, ?_⟩
  · have hr : Tendsto (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * Complex.I) (𝓝[>] 0)
        (𝓝[QuantumNLS.PhysicalPhaseHolomorphic.upper] (x0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨ray_tendsto x0, ?_⟩
      filter_upwards [eventually_mem_nhdsWithin] with y hy
      simpa [QuantumNLS.PhysicalPhaseHolomorphic.upper] using hy
    have h1 := (boundary_limit hκ u x0).comp hr
    have h2 := (h1.sub_const ((n : ℂ) * Real.pi)).div_const 2
    rw [hb, sub_self, zero_div] at h2
    exact h2
  · intro y hy
    have hz : 0 < ((x0 : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
    have h1 := im_phase_ge hκ u hz
    have e : ((x0 : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    rw [e] at h1
    have : ((boundaryPhase L κ (measure hκ u) ((x0 : ℂ) + (y : ℂ) * Complex.I) - (n : ℂ) * Real.pi) / 2).im =
        (boundaryPhase L κ (measure hκ u) ((x0 : ℂ) + (y : ℂ) * Complex.I)).im / 2 := by
      simp
    rw [this]
    linarith
  · intro y hy
    show Dl κ u ((x0 : ℂ) + (y : ℂ) * Complex.I) - 2 * (sgn n : ℂ) = -4 * (sgn n : ℂ) *
      Complex.sin ((boundaryPhase L κ (measure hκ u) ((x0 : ℂ) + (y : ℂ) * Complex.I) - (n : ℂ) * Real.pi) / 2) ^ 2
    have hz : 0 < ((x0 : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
    set γ := boundaryPhase L κ (measure hκ u) ((x0 : ℂ) + (y : ℂ) * Complex.I) with hγ
    set w := (γ - (n : ℂ) * Real.pi) / 2 with hw
    have hγw : γ = 2 * w + (n : ℂ) * Real.pi := by rw [hw]; ring
    have hc : Dl κ u ((x0 : ℂ) + (y : ℂ) * Complex.I) = 2 * Complex.cos γ :=
      (QuantumNLS.PhysicalUnconditionalTrace.upper_cosine hκ u hz).symm
    rw [hc, hγw, cos_add_sgn, Complex.cos_two_mul]
    have hs := Complex.sin_sq_add_cos_sq w
    linear_combination (4 * (sgn n : ℂ)) * hs

/-! ## Orders -/

theorem order_sq_sub (hκ : 0 < κ) (u : L2T L) (x0 : ℝ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hx0 : Dl κ u (x0 : ℂ) = 2 * (σ : ℂ)) :
    analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) (x0 : ℂ) =
      analyticOrderAt (fun z => Dl κ u z - 2 * (σ : ℂ)) (x0 : ℂ) := by
  have hf : AnalyticAt ℂ (fun z => Dl κ u z - 2 * (σ : ℂ)) (x0 : ℂ) := analytic_f (hD κ u) _
  have hg : AnalyticAt ℂ (fun z => Dl κ u z + 2 * (σ : ℂ)) (x0 : ℂ) :=
    ((hD κ u).add_const (2 * (σ : ℂ))).analyticAt _
  have hσsq : (σ : ℂ) ^ 2 = 1 := by rcases hσ with h | h <;> simp [h]
  have hfun : (fun w => Dl κ u w ^ 2 - 4) =
      (fun z => Dl κ u z - 2 * (σ : ℂ)) * (fun z => Dl κ u z + 2 * (σ : ℂ)) := by
    funext w
    simp only [Pi.mul_apply]
    linear_combination 4 * hσsq
  rw [hfun, analyticOrderAt_mul hf hg]
  have : analyticOrderAt (fun z => Dl κ u z + 2 * (σ : ℂ)) (x0 : ℂ) = 0 := by
    rw [hg.analyticOrderAt_eq_zero, hx0]
    rcases hσ with h | h <;> simp [h] <;> norm_num
  rw [this, add_zero]

/-- A real zero of `Δ² - 4`: the boundary phase is `nπ`, `Δ = 2σ_n`. -/
theorem zero_data (hκ : 0 < κ) (u : L2T L) (x : ℝ) (hx : Dl κ u (x : ℂ) ^ 2 - 4 = 0) :
    ∃ n : ℤ, boundary hκ u x = (n : ℂ) * Real.pi := by
  have hcos := boundary_cosine hκ u x
  set β := boundary hκ u x with hβ
  have hc : Complex.cos β ^ 2 = 1 := by
    have : (2 * Complex.cos β) ^ 2 = 4 := by rw [hcos]; linear_combination hx
    linear_combination this / 4
  have hs : Complex.sin β = 0 := by
    have := Complex.sin_sq_add_cos_sq β
    have h2 : Complex.sin β ^ 2 = 0 := by linear_combination this - hc
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.1 hs
  exact ⟨k, hk⟩

/-- (A): order at most two. -/
theorem order_le_two' (hκ : 0 < κ) (u : L2T L) (x : ℝ) (hx : Dl κ u (x : ℂ) ^ 2 - 4 = 0) :
    analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) (x : ℂ) ≤ 2 := by
  obtain ⟨n, hn⟩ := zero_data hκ u x hx
  obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u x n hn
  rw [order_sq_sub hκ u x (sgn_cases n) hDx]
  exact order_le_two (hD κ u) (sgn_cases n) Fact.out hray

theorem order_cases' (hκ : 0 < κ) (u : L2T L) (x : ℝ) (n : ℤ) (hn : boundary hκ u x = (n : ℂ) * Real.pi) :
    analyticOrderAt (fun z => Dl κ u z - 2 * (sgn n : ℂ)) (x : ℂ) = 1 ∨
      analyticOrderAt (fun z => Dl κ u z - 2 * (sgn n : ℂ)) (x : ℂ) = 2 := by
  obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u x n hn
  exact order_cases (hD κ u) (sgn_cases n) Fact.out hray hDx

/-- (A) and (B). -/
theorem zeros_and_double (hκ : 0 < κ) (u : L2T L) :
    (∀ z : ℂ, Dl κ u z ^ 2 - 4 = 0 → z.im = 0 ∧ analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) z ≤ 2) ∧
    (∀ x : ℝ, analyticOrderAt (fun w => Dl κ u w ^ 2 - 4) (x : ℂ) = 2 →
      (∀ᶠ t : ℝ in 𝓝[<] x, |(Dl κ u (t : ℂ)).re| < 2) ∧ (∀ᶠ t : ℝ in 𝓝[>] x, |(Dl κ u (t : ℂ)).re| < 2)) := by
  constructor
  · intro z hz
    have him := zeros_real' hκ u hz
    refine ⟨him, ?_⟩
    have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hz'] at hz ⊢
    exact order_le_two' hκ u _ hz
  · intro x h2
    have hx : Dl κ u (x : ℂ) ^ 2 - 4 = 0 := by
      have := (analyticOrderAt_ne_zero.1 (by rw [h2]; decide)).2
      simpa using this
    obtain ⟨n, hn⟩ := zero_data hκ u x hx
    obtain ⟨hDx, hray⟩ := ray_of_boundary hκ u x n hn
    rw [order_sq_sub hκ u x (sgn_cases n) hDx] at h2
    have := double_strict (hD κ u) (hreal κ u) (sgn_cases n) Fact.out hray hDx h2
    exact ⟨this.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_lt ht)),
      this.filter_mono (nhdsWithin_mono _ (fun t ht => ne_of_gt ht))⟩

end QuantumNLS.RootGapMultiplicity

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RootGapMultiplicity.zeros_and_double
