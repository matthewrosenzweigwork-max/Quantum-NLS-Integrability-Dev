import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB1TimeConv

/-! # Track B, step B1: the Bourgain spaces `X^{s,b}` (interaction-profile definition)

Internal analytic spaces for the `L²` NLS theory; they occur in no final statement.

Pro's norm (time Fourier transform `e^{-itτ}`) is
`‖v‖²_{X^{s,b}} = Σ_n ∫ ρ_n^{2s} ⟨τ + (2πn)²⟩^{2b} |ṽ(τ,n)|² dτ`.
Writing `v̂_n(t) = e^{-it(2πn)²} w_n(t)` (interaction profiles `w_n`), one has
`ṽ(τ,n) = ŵ_n(τ + (2πn)²)`, so the norm is `Σ_n ρ_n^{2s} ‖w_n‖²_{H^b(ℝ)}` with the
time-Sobolev norm `‖w‖²_{H^b} = ∫ ⟨σ⟩^{2b} |ŵ(σ)|² dσ`.

Formal choices (recorded for review):
* `w_n ∈ L²(ℝ)` and `ŵ` is Mathlib's `L²` Fourier transform `MeasureTheory.Lp.fourierTransformₗᵢ`
  (phase `e^{-2πitξ}`); Pro's `σ = 2πξ`, hence the weight `⟨2πξ⟩^{2b}` below. This differs from
  Pro's norm only by the Jacobian factor `2π`, independent of `s, b, n`.
* The spatial weight is the project bracket `⟨n⟩ = √(1+n²)` (equivalent to `ρ_n`); for `s = 0` it is
  absent.
* Norms are nonnegative extended reals (`ℝ≥0∞`); membership is finiteness. No totalized real `tsum`
  is used.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory
open scoped ENNReal

/-- Time profiles: square-integrable functions of `t ∈ ℝ`. -/
abbrev TimeL2 : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- The `L²(ℝ)` Fourier transform of a time profile (Mathlib convention `e^{-2πitξ}`). -/
def profileFourier (w : TimeL2) : TimeL2 := Lp.fourierTransformₗᵢ ℝ ℂ w

/-- The time-Sobolev weight `⟨2πξ⟩^{2b}` (Pro's `⟨σ⟩^{2b}` with `σ = 2πξ`). -/
def hbWeight (b ξ : ℝ) : ℝ := brk (2 * Real.pi * ξ) ^ (2 * b)

/-- `‖w‖²_{H^b(ℝ)} = ∫ ⟨2πξ⟩^{2b} |𝓕w(ξ)|² dξ`, as an extended nonnegative real. -/
def hbNormSq (b : ℝ) (w : TimeL2) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (hbWeight b ξ) * ‖profileFourier w ξ‖ₑ ^ 2

/-- Interaction-profile families indexed by spatial modes. -/
abbrev XsbProfile : Type := ℤ → TimeL2

/-- `‖W‖²_{X^{s,b}} = Σ_n ⟨n⟩^{2s} ‖W_n‖²_{H^b}` (extended nonnegative). -/
def xsbNormSq (s b : ℝ) (W : XsbProfile) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (brk (n : ℝ) ^ (2 * s)) * hbNormSq b (W n)

/-- Membership in `X^{s,b}`: finite norm. -/
def MemXsb (s b : ℝ) (W : XsbProfile) : Prop := xsbNormSq s b W ≠ ⊤

/-- The `H^b` weight is positive. -/
theorem hbWeight_pos (b ξ : ℝ) : 0 < hbWeight b ξ := Real.rpow_pos_of_pos (brk_pos _) _

/-- The `H^b` weight is monotone in `b`. -/
theorem hbWeight_mono {b b' : ℝ} (h : b ≤ b') (ξ : ℝ) : hbWeight b ξ ≤ hbWeight b' ξ :=
  Real.rpow_le_rpow_of_exponent_le (one_le_brk _) (by linarith)

/-- The `H^0` weight is one. -/
theorem hbWeight_zero (ξ : ℝ) : hbWeight 0 ξ = 1 := by
  simp [hbWeight]

/-- `‖w‖_{H^b}` is monotone in `b`. -/
theorem hbNormSq_mono {b b' : ℝ} (h : b ≤ b') (w : TimeL2) : hbNormSq b w ≤ hbNormSq b' w :=
  lintegral_mono fun ξ => by
    gcongr
    exact hbWeight_mono h ξ

/-- Plancherel: `‖𝓕w‖ₑ = ‖w‖ₑ`. -/
theorem enorm_profileFourier (w : TimeL2) : ‖profileFourier w‖ₑ = ‖w‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact congrArg _ ((Lp.fourierTransformₗᵢ ℝ ℂ).nnnorm_map w)

/-- `∫ |g|² = ‖g‖²` for `g ∈ L²(ℝ)`, as extended reals. -/
theorem lintegral_enorm_sq_eq (g : TimeL2) : ∫⁻ ξ, ‖g ξ‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure ℝ)) (p := (2 : NNReal))
    (by norm_num) (Lp.aestronglyMeasurable g)
  have h2 : ((2 : NNReal) : ℝ≥0∞) = 2 := rfl
  rw [h2, ← Lp.enorm_def] at h
  simp only [NNReal.coe_ofNat, ENNReal.rpow_two] at h
  exact h.symm

/-- `H^0(ℝ) = L²(ℝ)` isometrically (Plancherel). -/
theorem hbNormSq_zero (w : TimeL2) : hbNormSq 0 w = ‖w‖ₑ ^ 2 := by
  unfold hbNormSq
  simp only [hbWeight_zero, ENNReal.ofReal_one, one_mul]
  rw [lintegral_enorm_sq_eq, enorm_profileFourier]

/-- For `b ≥ 0`, `‖w‖_{L²} ≤ ‖w‖_{H^b}`. -/
theorem enorm_sq_le_hbNormSq {b : ℝ} (hb : 0 ≤ b) (w : TimeL2) : ‖w‖ₑ ^ 2 ≤ hbNormSq b w := by
  rw [← hbNormSq_zero]
  exact hbNormSq_mono hb w

/-- `‖W‖_{X^{s,b}}` is monotone in `b`. -/
theorem xsbNormSq_mono_b {s b b' : ℝ} (h : b ≤ b') (W : XsbProfile) :
    xsbNormSq s b W ≤ xsbNormSq s b' W :=
  ENNReal.tsum_le_tsum fun n => by
    gcongr
    exact hbNormSq_mono h (W n)

/-- `‖W‖_{X^{s,b}}` is monotone in `s`. -/
theorem xsbNormSq_mono_s {s s' b : ℝ} (h : s ≤ s') (W : XsbProfile) :
    xsbNormSq s b W ≤ xsbNormSq s' b W :=
  ENNReal.tsum_le_tsum fun n => by
    gcongr
    exact one_le_brk _

/-- `X^{s,b'} ⊂ X^{s,b}` for `b ≤ b'`. -/
theorem MemXsb.mono_b {s b b' : ℝ} (h : b ≤ b') {W : XsbProfile} (hW : MemXsb s b' W) :
    MemXsb s b W :=
  ne_top_of_le_ne_top hW (xsbNormSq_mono_b h W)

/-- `X^{s',b} ⊂ X^{s,b}` for `s ≤ s'`. -/
theorem MemXsb.mono_s {s s' b : ℝ} (h : s ≤ s') {W : XsbProfile} (hW : MemXsb s' b W) :
    MemXsb s b W :=
  ne_top_of_le_ne_top hW (xsbNormSq_mono_s h W)

/-- `X^{0,0}` is `ℓ²(ℤ; L²(ℝ))`: `‖W‖²_{X^{0,0}} = Σ_n ‖W_n‖²`. -/
theorem xsbNormSq_zero_zero (W : XsbProfile) : xsbNormSq 0 0 W = ∑' n : ℤ, ‖W n‖ₑ ^ 2 := by
  unfold xsbNormSq
  congr 1
  funext n
  rw [hbNormSq_zero]
  simp

/-- For `b ≥ 0`, `Σ_n ‖W_n‖² ≤ ‖W‖²_{X^{0,b}}` (so `X^{0,b}` profiles are spacetime-`L²`). -/
theorem tsum_enorm_sq_le_xsbNormSq {b : ℝ} (hb : 0 ≤ b) (W : XsbProfile) :
    ∑' n : ℤ, ‖W n‖ₑ ^ 2 ≤ xsbNormSq 0 b W := by
  rw [← xsbNormSq_zero_zero]
  exact xsbNormSq_mono_b hb W

end LiebLiniger.FixedPeriod.ALLS.PdeB
