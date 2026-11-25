import Mathlib
import QuantumNLS.RootMeasureTransfer

/-!
# R-09E1EAE9 `thm:root-measure`, Step 3 (pointwise part): the limiting Cauchy transform `g(z)` and the concentration of `G_N(z)`

Source: `ROOT_spectral_measure.tex`, Step 3 ("construction without an a priori measure"): for `Im z = η ≥ η₀`, the scalar equation
`f_z(w) = s(z;u)` has a unique solution `g(z)` in `|w| ≤ η⁻¹`, obtained by compactness from outcomes with small residual, and
`G_N(z) → g(z)` in mean square (`eq:root-G-concentration`, in the form `E|G_N − g|² ≤ C/N` with `C` depending on `L, κ` only;
the printed extra factor `η⁻²` is not tracked: the PROP-008 physical moment constant `Cunif L κ 0 1` replaces the explicit series
estimates, so the constant is not uniform in `η`).  Imports `RootMeasureComplex` (Steps 1-2) and `RootMeasureTransfer`
(eigenvalue identification and the PROP-008 `p = 1` bound).  No EXT-025 contract; the compactness is mathlib's
Bolzano-Weierstrass in `ℂ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.RootMeasureConcentration

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.RootMeasureComplex (sProd GN fz HighHalf fz_lower product_error)
open QuantumNLS.NormalizedTransfer (productSymbol)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
open QuantumNLS.HighMomentsTransfer (Cunif)
open QuantumNLS.RootMeasureTransfer (hasSum_born_variance born_variance_le)

theorem continuous_fz (L κ : ℝ) (z : ℂ) : Continuous (fz L κ z) := by
  unfold fz; fun_prop

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ)

theorem norm_GN_le {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : 0 < z.im) : ‖GN N q z‖ ≤ (z.im)⁻¹ := by
  by_cases hN : N = 0
  · subst hN; simp [GN]; exact hz.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  unfold GN
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ j, (z - (q j : ℂ))⁻¹‖ ≤ N * (z.im)⁻¹ := by
    calc ‖∑ j, (z - (q j : ℂ))⁻¹‖ ≤ ∑ j : Fin N, ‖(z - (q j : ℂ))⁻¹‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin N, (z.im)⁻¹ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_inv]
          have hzq : z.im ≤ ‖z - (q j : ℂ)‖ := by
            have := Complex.abs_im_le_norm (z - (q j : ℂ))
            simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
            exact (le_abs_self _).trans this
          exact inv_anti₀ hz hzq
      _ = N * (z.im)⁻¹ := by simp
  calc (N : ℝ)⁻¹ * ‖∑ j, (z - (q j : ℂ))⁻¹‖ ≤ (N : ℝ)⁻¹ * (N * (z.im)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (z.im)⁻¹ := by field_simp

include hκ

variable {N : ℕ} (hN : 0 < N)

include hN in
/-- **Averaging**: some label has residual at most the Born mean. -/
theorem exists_good_label (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : 0 < z.im) :
    ∃ m : MArr N, ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2 ≤
      Cunif L κ 0 1 / N := by
  by_contra hcon
  push Not at hcon
  have hp1 := QuantumNLS.BetheCoefficientTransform.hasSum_bornLaw_unit (meanField_physicalBasis L N hN hκ) u hu
  have hs := hasSum_born_variance hκ hN u z hz
  have hle := born_variance_le hκ hN u hu z hz
  have hf : HasSum (fun m : MArr N => bornLaw (meanField_physicalBasis L N hN hκ) u m * (Cunif L κ 0 1 / N))
      (Cunif L κ 0 1 / N) := by simpa using hp1.mul_right (Cunif L κ 0 1 / N)
  obtain ⟨i, hi⟩ : ∃ i, 0 < bornLaw (meanField_physicalBasis L N hN hκ) u i := by
    by_contra h0
    push Not at h0
    have : ∀ i, bornLaw (meanField_physicalBasis L N hN hκ) u i = 0 := fun i =>
      le_antisymm (h0 i) (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _)
    have h00 : HasSum (fun m : MArr N => bornLaw (meanField_physicalBasis L N hN hκ) u m) 0 := by
      simp [this]
    exact one_ne_zero (hp1.unique h00)
  have hlt := hasSum_lt (f := fun m : MArr N => bornLaw (meanField_physicalBasis L N hN hκ) u m *
      (Cunif L κ 0 1 / N)) (g := fun m => bornLaw (meanField_physicalBasis L N hN hκ) u m *
        ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2) (i := i)
    (fun m => mul_le_mul_of_nonneg_left (hcon m).le
      (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _))
    (mul_lt_mul_of_pos_left (hcon i) hi) hf hs
  have h2 := hs.tsum_eq
  linarith


include hN in
/-- Residual bound of the good label. -/
theorem good_label_residual (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    ∃ w : ℂ, ‖w‖ ≤ (z.im)⁻¹ ∧
      ‖fz L κ z w - productSymbol L κ u z‖ ≤ 3 * (κ / z.im) ^ 2 / N + Real.sqrt (Cunif L κ 0 1 / N) := by
  have hη : 0 < z.im := by linarith [hz.1]
  obtain ⟨m, hm⟩ := exists_good_label hκ hN u hu hη
  refine ⟨GN N (arrRoots L (κ / N) m) z, norm_GN_le _ hη, ?_⟩
  have h1 := product_error hκ hz hN (arrRoots L (κ / N) m)
  have h2 : ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ≤
      Real.sqrt (Cunif L κ 0 1 / N) := Real.le_sqrt_of_sq_le hm
  calc ‖fz L κ z (GN N (arrRoots L (κ / N) m) z) - productSymbol L κ u z‖
      ≤ ‖fz L κ z (GN N (arrRoots L (κ / N) m) z) - sProd L κ N (arrRoots L (κ / N) m) z‖ +
        ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ := by
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
        have h1' : ‖fz L κ z (GN N (arrRoots L (κ / N) m) z) - sProd L κ N (arrRoots L (κ / N) m) z‖ ≤
            3 * (κ / z.im) ^ 2 / N := by rw [norm_sub_rev]; exact h1
        linarith


/-- **Existence of the limiting Cauchy value** (Step 3): `f_z(w) = s(z;u)` has a solution in `|w| ≤ η⁻¹`. -/
theorem exists_fixed (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    ∃ g : ℂ, ‖g‖ ≤ (z.im)⁻¹ ∧ fz L κ z g = productSymbol L κ u z := by
  have hη : 0 < z.im := by linarith [hz.1]
  have key : ∀ n : ℕ, ∃ w : ℂ, ‖w‖ ≤ (z.im)⁻¹ ∧
      ‖fz L κ z w - productSymbol L κ u z‖ ≤
        3 * (κ / z.im) ^ 2 / ((n + 1 : ℕ) : ℝ) + Real.sqrt (Cunif L κ 0 1 / ((n + 1 : ℕ) : ℝ)) :=
    fun n => good_label_residual (N := n + 1) hκ (Nat.succ_pos n) u hu hz
  choose w hw1 hw2 using key
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) ((z.im)⁻¹)) := isCompact_closedBall _ _
  obtain ⟨g, hg, φ, hφ, hlim⟩ := hcomp.tendsto_subseq (fun n => by simpa using hw1 n)
  refine ⟨g, by simpa using hg, ?_⟩
  have h1 : Tendsto (fun k => fz L κ z (w (φ k))) atTop (𝓝 (fz L κ z g)) :=
    ((continuous_fz L κ z).tendsto g).comp hlim
  have hε : Tendsto (fun n : ℕ => 3 * (κ / z.im) ^ 2 / ((n + 1 : ℕ) : ℝ) +
      Real.sqrt (Cunif L κ 0 1 / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have a1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have a2 : Tendsto (fun n : ℕ => 3 * (κ / z.im) ^ 2 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop a1
    have a3 : Tendsto (fun n : ℕ => Real.sqrt (Cunif L κ 0 1 / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => Cunif L κ 0 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop a1
      have := (Real.continuous_sqrt.tendsto 0).comp h0
      simpa [Function.comp_def] using this
    simpa using a2.add a3
  have h2 : Tendsto (fun k => fz L κ z (w (φ k)) - productSymbol L κ u z) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hw2 (φ k)) (hε.comp hφ.tendsto_atTop)
  have h3 : Tendsto (fun k => fz L κ z (w (φ k))) atTop (𝓝 (productSymbol L κ u z)) := by
    simpa using h2.add_const (productSymbol L κ u z)
  exact tendsto_nhds_unique h1 h3

/-- **Uniqueness** (`eq:root-inverse-bound`). -/
theorem unique_fixed {z : ℂ} (hz : HighHalf L κ z) {g g' : ℂ} (hg : ‖g‖ ≤ (z.im)⁻¹)
    (hg' : ‖g'‖ ≤ (z.im)⁻¹) (h : fz L κ z g = fz L κ z g') : g = g' := by
  have := fz_lower hκ hz hg hg'
  rw [h, sub_self, norm_zero] at this
  have h0 : ‖g - g'‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (g - g')]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)

open Classical in
/-- The limiting Cauchy transform `g(z)` of `μ_{κ,u}` on the high half-plane (unique solution in `|w| ≤ η⁻¹`). -/
def gStar (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ) : ℂ :=
  if h : HighHalf L κ z then Classical.choose (exists_fixed hκ u hu h) else 0

theorem gStar_spec (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    ‖gStar L κ hκ u hu z‖ ≤ (z.im)⁻¹ ∧ fz L κ z (gStar L κ hκ u hu z) = productSymbol L κ u z := by
  unfold gStar
  rw [dif_pos hz]
  exact Classical.choose_spec (exists_fixed hκ u hu hz)

end QuantumNLS.RootMeasureConcentration

#print axioms QuantumNLS.RootMeasureConcentration.exists_good_label
#print axioms QuantumNLS.RootMeasureConcentration.exists_fixed
#print axioms QuantumNLS.RootMeasureConcentration.unique_fixed
#print axioms QuantumNLS.RootMeasureConcentration.gStar_spec
