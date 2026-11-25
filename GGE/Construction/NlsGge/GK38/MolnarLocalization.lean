import NlsGge.GK38.MolnarLocalizationA
import NlsGge.GK38.MolnarLocalizationB4

/-!
# Mo2: Molnár's Theorem 5 with polynomial constants (assembly)

Source: Molnár, arXiv:1403.1369, Theorem 5 (proof: Lemmas 5-10).  Plan: `campaign/E01_PLAN.md`
§6.12 "Mo2".  **Status: proved except for ONE explicit goal (`MolnarBridge38`, below).**

Pieces:
* part A (`MolnarLocalizationA`): from localization of the real zeros of `Δh(τu)² - 1` (for all
  couplings `τ ∈ [0,1]`) to the whole labelled gap `[λ_n^-, λ_n^+]` (replaces Molnár's "standard
  counting argument" by a homotopy in `τ`, using only repository facts);
* parts B1-B4: the Lyapunov-Schmidt estimate on the Fourier side with Molnár's constants
  (`Mo2.molnar_ls_core`: Lemmas 5, 6, 9, 10, `⟨n⟩ ≥ 8‖φ‖₁²`, radius `‖φ‖₁²/⟨n⟩ + √2 ‖φ‖₁/⟨2n⟩`);
* this file: the statement, the dictionary between `u` and Molnár's `φ`, and the bridge
  statement `MolnarBridge38` (proved in `MolnarLocalizationC.molnarBridge38_holds`; the
  unconditional theorem is `MolnarLocalizationD.molnar_localization38`).

**Norm and bracket conventions (deviation from the plan text, forced by the source).**
Molnár's `⟨x⟩ = 1 + |x|`, and `‖φ‖₁² = Σ_m ⟨m⟩² (|φ⁻_m|² + |φ⁺_m|²)` over the Fourier coefficients
with respect to `e^{imπx}` of the 2-periodic extension of `φ = (u, ū)`; for a 1-periodic `u` only
`m = 2j` occurs: `‖φ‖₁² = 2 Σ_j (1 + 2|j|)² |û_j|²` (`molnarNormSq`).  This is NOT the repository's
`‖u‖_{H¹}² = Σ (1 + j²) |û_j|²`; `molnarNormSq u ≤ 16 ‖u‖²_{H¹}` (`molnarNormSq_le`).  The plan's
`∃ c` is vacuous (`c` does not occur in the inequality) and is dropped.

**The bridge** (`MolnarBridge38 v R2`, proved in `MolnarLocalizationC`): a real zero `x` of `Δh(v)² - 1`, i.e. a doubled-period
periodic eigenvalue of the Zakharov-Shabat operator of `v` (repository: `actualSourceEigenvalue_iff_halfTrace_E02_38`:
`Δh(v)(-z) = spectralSign m ⟺` `z` is a sector-`m` eigenvalue of `actualSourcePerturbedDiracPMapAfterAE m v (star v)`),
yields a nonzero `ℓ²`-solution of the Fourier system `Mo2.Setup` with `c₁(k) = û(k/2)`,
`c₂(k) = conj û(k/2)` (`k` even, else `0`), `λ = -x`, index `-n`.  See the report for the route
(`actualSourcePerturbedDirac_eigenvalue_iff_coordinate_kernel38V1`,
`coveredH1ParityPairPotential_upper_entry/_lower_entry`, `HilbertBasis.hasSum_repr`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology

namespace NlsGge.GK38

open NlsGge.SpectralFoundations NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

noncomputable section

/-- Molnár's `‖φ‖₁²` for `φ = (u, ū)` (period-one `u`, 2-periodic extension, bracket `1 + |m|`). -/
def molnarNormSq (u : PhysicalL2) : ℝ :=
  2 * ∑' j : ℤ, molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier u j‖ ^ 2

theorem molnarNormSq_nonneg (u : PhysicalL2) : 0 ≤ molnarNormSq u := by
  unfold molnarNormSq
  exact mul_nonneg (by norm_num) (tsum_nonneg fun j => by positivity)

theorem molnarNormSq_smul (τ : ℝ) (u : PhysicalL2) :
    molnarNormSq ((τ : ℂ) • u) = τ ^ 2 * molnarNormSq u := by
  unfold molnarNormSq
  have : ∀ j : ℤ, molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier ((τ : ℂ) • u : PhysicalL2) j‖ ^ 2 =
      τ ^ 2 * (molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier u j‖ ^ 2) := by
    intro j
    rw [physicalFourier_smul38, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [tsum_congr this, tsum_mul_left]
  ring

/-- Comparison with the repository `H¹` norm: `‖φ‖₁² ≤ 16 ‖u‖²_{H¹}`. -/
theorem molnarNormSq_le (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    molnarNormSq u ≤ 16 * ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  rw [physicalSobolevL2_norm_sq]
  unfold molnarNormSq
  have hw : ∀ j : ℤ, Real.rpow (japaneseBracket j) (2 * 1) = 1 + (j : ℝ) ^ 2 := fun j =>
    japaneseBracket_h1_weight j
  have hs : Summable fun j : ℤ => Real.rpow (japaneseBracket j) (2 * 1) * ‖physicalFourier u j‖ ^ 2 := by
    exact hu
  have hle : ∀ j : ℤ, molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier u j‖ ^ 2 ≤
      8 * (Real.rpow (japaneseBracket j) (2 * 1) * ‖physicalFourier u j‖ ^ 2) := by
    intro j
    rw [hw j]
    have : molnarBracket38 (2 * j) ^ 2 ≤ 8 * (1 + (j : ℝ) ^ 2) := by
      unfold molnarBracket38
      push_cast
      rw [abs_mul]
      have h2 : |(2 : ℝ)| = 2 := by norm_num
      rw [h2]
      nlinarith [sq_abs (j : ℝ), abs_nonneg (j : ℝ), sq_nonneg (|(j : ℝ)| - 1 / 2)]
    calc molnarBracket38 (2 * j) ^ 2 * ‖physicalFourier u j‖ ^ 2
        ≤ 8 * (1 + (j : ℝ) ^ 2) * ‖physicalFourier u j‖ ^ 2 := by gcongr
      _ = _ := by ring
  have hsum := (hs.mul_left 8)
  have := (Summable.of_nonneg_of_le (fun j => by positivity) hle hsum).tsum_le_tsum hle hsum
  rw [tsum_mul_left] at this
  linarith

/-- **The bridge of Mo2** (the Fourier-side bridge; proved as `molnarBridge38_holds`).  For `v` with `‖φ(v)‖₁² ≤ R2`: every
real zero `x` of `Δh(v)² - 1` with `|x - nπ| ≤ π/2`, `⟨n⟩ ≥ 8 R2`, is the eigenvalue `λ = -x` of the
Fourier system of `Mo2.Setup` at index `-n`, with a nonzero `H¹` solution. -/
def MolnarBridge38 (v : PhysicalL2) (R2 : ℝ) : Prop :=
  ∀ (n : ℤ) (x : ℝ), 8 * R2 ≤ molnarBracket38 n → |x - n * Real.pi| ≤ Real.pi / 2 →
    actualPhysicalUnitHalfTrace32 v (x : ℂ) ^ 2 = 1 →
    ∃ c₁ c₂ f₁ f₂ : ℤ → ℂ, Mo2.Setup (-n) (-x) c₁ c₂ f₁ f₂ R2 ∧
      ((∃ m, f₁ m ≠ 0) ∨ (∃ m, f₂ m ≠ 0))

/-- Bridge + Lyapunov-Schmidt = zero localization. -/
theorem zeroLoc_of_bridge (v : PhysicalL2) (R2 : ℝ) (hb : MolnarBridge38 v R2) :
    MolnarZeroLoc38 v R2 := by
  intro n hn x hx hz
  obtain ⟨c₁, c₂, f₁, f₂, S, hne⟩ := hb n x hn hx hz
  have h := Mo2.molnar_ls_core S hne
  have e1 : |(-x) - ((-n : ℤ) : ℝ) * Real.pi| = |x - n * Real.pi| := by
    rw [show (-x) - ((-n : ℤ) : ℝ) * Real.pi = -(x - n * Real.pi) by push_cast; ring, abs_neg]
  have e2 : (1 + |(((-n : ℤ)) : ℝ)|) = molnarBracket38 n := by
    unfold molnarBracket38; push_cast; rw [abs_neg]
  have e3 : (1 + |((2 * (-n) : ℤ) : ℝ)|) = molnarBracket38 (2 * n) := by
    unfold molnarBracket38; push_cast; rw [show (2 * -(n : ℝ)) = -(2 * n) by ring, abs_neg]
  rw [e1, e2, e3] at h
  exact h

/-- **Mo2 (Molnár Theorem 5), conditional on the bridge.**  For `u ∈ H¹` and every `n` with
`⟨n⟩ = 1 + |n| ≥ 8 ‖φ(u)‖₁²`, every `λ` of the labelled gap `g_n = [λ_n^-, λ_n^+]` satisfies
`|λ - nπ| ≤ ‖φ‖₁²/⟨n⟩ + √2 ‖φ‖₁/⟨2n⟩` (`‖φ‖₁² = molnarNormSq u`). -/
theorem molnar_localization_of_bridge
    (hb : ∀ (v : PhysicalL2) (R2 : ℝ), SobolevSquareSummable 1 (physicalFourier v) →
      molnarNormSq v ≤ R2 → MolnarBridge38 v R2)
    (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ)
    (hn : 8 * molnarNormSq u ≤ molnarBracket38 n) (l : ℝ)
    (hl : l ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n)) :
    |l - n * Real.pi| ≤
      molnarNormSq u / molnarBracket38 n +
        Real.sqrt 2 * Real.sqrt (molnarNormSq u) / molnarBracket38 (2 * n) := by
  refine gap_localization_of_zeroLoc38 u hu (molnarNormSq u) (molnarNormSq_nonneg u) ?_ n hn l hl
  intro τ hτ
  refine zeroLoc_of_bridge _ _ (hb _ _ (sobolevSquareSummable_smul38 (τ : ℂ) u hu) ?_)
  rw [molnarNormSq_smul]
  have h1 : τ ^ 2 ≤ 1 := by nlinarith [hτ.1, hτ.2]
  nlinarith [molnarNormSq_nonneg u]

end

end NlsGge.GK38
