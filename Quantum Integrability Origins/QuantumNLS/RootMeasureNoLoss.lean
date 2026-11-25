import Mathlib
import QuantumNLS.RootMeasureTransfer

/-!
# R-09E1EAE9 `thm:root-measure`, Step 4 ("no loss of mass"): `iY g(iY) → 1`

Source: `ROOT_spectral_measure.tex`, `thm:root-measure`, Step 4.  Every ingredient is derived from accepted objects; no EXT-025 contract and no
vague-compactness theorem is used.

* `hasSum_a1`: the one-particle coefficient `a_1(z) = ⟨u, K_{1,z}u⟩` equals `∑_m |⟨Ψ_{1,m}, u⟩|² · i(1−e^{izL})/(z−q_m)` (spectral expansion in the
  accepted physical basis at `N = 1` (UBB1); `N = 1` of `eq:root-quantum-input`).  This replaces the printed approximate-identity formula
  `eq:root-approximate-identity` (translation correlation) by the Fourier-diagonal computation; the two are equal but the former avoids the
  `L²`-translation theory.
* `a1_tendsto`: `Y a_1(iY) → 1` (dominated convergence for the series: each summand `Y·i(1−e^{-YL})/(iY−q) → 1` and is bounded by `2`; the Born weights sum to `1`).
* `productSymbol_approx`: `|s(z;u) − 1 − e^{izL} − κ a_1(z)| ≤ (8/3)(κ/η)²` (the `r ≥ 2` terms, from `lem_root_placement`, `‖K_{r,z}‖ ≤ 2η^{-r}`).
* `fz_taylor`: Taylor expansion of `f_z` to first order on `|w| ≤ η⁻¹`.
* `iYg_tendsto`: any family `g(Y)` with `|g(Y)| ≤ Y⁻¹`, `f_{iY}(g(Y)) = s(iY;u)` satisfies `iY g(Y) → 1` as `Y → ∞`; hence `1 + Y Im g(Y) → 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.RootMeasureNoLoss

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.NormalityBridge (eigen)
open QuantumNLS.RootMeasureComplex (sProd fz HighHalf norm_exp_izL_le)
open QuantumNLS.NormalizedTransfer (normalizedTransfer productSymbol symbolTerm orderedKernel)
open QuantumNLS.KernelDefinition (kernelProductSymbol)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis transfer_physicalBasis)
open QuantumNLS.HighMomentsOps (wvec inner_wvec)
open QuantumNLS.RootMeasureTransfer (hasSum_inner_diag eigen_eq_sProd)
open QuantumNLS.RootPlacementBound (inner_genericU lem_root_placement)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### The one-particle coefficient -/

theorem inner_S1 (u : L2T L) (hu : ‖u‖ = 1) (z : ℂ) :
    ⟪wvec 1 u, normalizedTransfer L κ 1 z (wvec 1 u)⟫_ℂ =
      (1 + Complex.exp (Complex.I * z * L)) + (κ : ℂ) * kernelProductSymbol (orderedKernel L 1 z) u := by
  have key := inner_genericU u hu (N := 1) (r := 1) le_rfl (orderedKernel L 1 z)
  have hw := inner_wvec 1 u hu
  unfold normalizedTransfer
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.sum_apply, Fin.sum_univ_one, ContinuousLinearMap.smul_apply, inner_add_right,
    inner_smul_right, inner_smul_right]
  simp only [Fin.val_zero, zero_add]
  rw [hw]
  have hf : QuantumNLS.HighMomentsRank.fallR 1 1 = 1 := by
    simp [QuantumNLS.HighMomentsRank.fallR]
  rw [key, hf]
  simp

/-- **Spectral expansion of `a_1(z)`** in the accepted `N = 1` physical basis: `a_1(z) = ∑_m born_m · i(1−e^{izL})/(z−q_m)`. -/
theorem hasSum_a1 (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun m : MArr 1 =>
        ((bornLaw (meanField_physicalBasis L 1 Nat.one_pos hκ) u m : ℝ) : ℂ) *
          (Complex.I * (1 - Complex.exp (Complex.I * z * L)) / (z - (arrRoots L (κ / ((1 : ℕ) : ℝ)) m 0 : ℂ))))
      (kernelProductSymbol (orderedKernel L 1 z) u) := by
  classical
  have h1 := hasSum_inner_diag (meanField_physicalBasis L 1 Nat.one_pos hκ) (normalizedTransfer L κ 1 z)
    (fun m => eigen (L := L) κ hκ Nat.one_pos m z) (fun m => transfer_physicalBasis hκ Nat.one_pos z m)
    (wvec 1 u)
  rw [inner_S1 u hu z] at h1
  have hp : HasSum (fun m : MArr 1 => ((bornLaw (meanField_physicalBasis L 1 Nat.one_pos hκ) u m : ℝ) : ℂ)) 1 := by
    have := QuantumNLS.BetheCoefficientTransform.hasSum_bornLaw_unit
      (meanField_physicalBasis L 1 Nat.one_pos hκ) u hu
    have h2 := (Complex.hasSum_ofReal (f := fun m : MArr 1 => bornLaw (meanField_physicalBasis L 1 Nat.one_pos hκ) u m)
      (x := 1)).2 this
    simpa using h2
  have h2 := h1.sub (hp.mul_right (1 + Complex.exp (Complex.I * z * L)))
  have h3 := h2.mul_left (κ : ℂ)⁻¹
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  convert h3 using 1
  · funext m
    have hbl : ((bornLaw (meanField_physicalBasis L 1 Nat.one_pos hκ) u m : ℝ) : ℂ) =
        ((‖⟪(meanField_physicalBasis L 1 Nat.one_pos hκ) m, wvec 1 u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := rfl
    rw [hbl, eigen_eq_sProd hκ Nat.one_pos m z hz]
    simp only [sProd, Fin.prod_univ_one, Nat.cast_one, one_mul]
    have hzq : z - (arrRoots L (κ / ((1 : ℕ) : ℝ)) m 0 : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this; linarith
    field_simp
    ring
  · field_simp
    ring

/-! ### `Y a_1(iY) → 1` -/

theorem norm_exp_iY (Y : ℝ) : ‖Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))‖ = Real.exp (-(Y * L)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem lam_bound (q Y : ℝ) (hY : 0 < Y) :
    ‖(Y : ℂ) * (Complex.I * (1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) /
      (Complex.I * (Y : ℂ) - (q : ℂ)))‖ ≤ 2 := by
  have hden : Y ≤ ‖Complex.I * (Y : ℂ) - (q : ℂ)‖ := by
    have := Complex.abs_im_le_norm (Complex.I * (Y : ℂ) - (q : ℂ))
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, add_zero, sub_zero, zero_add] at this
    exact (le_abs_self Y).trans (by simpa using this)
  have hE : ‖Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))‖ ≤ 1 := by
    rw [norm_exp_iY]
    exact Real.exp_le_one_iff.2 (by nlinarith [Fact.out (p := 0 < L)])
  have hnum : ‖1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  rw [norm_mul, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hY]
  calc Y * (‖1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))‖ /
        ‖Complex.I * (Y : ℂ) - (q : ℂ)‖) ≤ Y * (2 / Y) := by
        gcongr
    _ = 2 := by field_simp

theorem lam_tendsto (q : ℝ) :
    Tendsto (fun Y : ℝ => (Y : ℂ) * (Complex.I * (1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) /
      (Complex.I * (Y : ℂ) - (q : ℂ)))) atTop (𝓝 1) := by
  have hb : Tendsto (fun Y : ℝ => Real.exp (-(Y * L)) + |q| / Y) atTop (𝓝 0) := by
    have hL : 0 < L := Fact.out
    have h1 : Tendsto (fun Y : ℝ => Real.exp (-(Y * L))) atTop (𝓝 0) := by
      have : Tendsto (fun Y : ℝ => -(Y * L)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hL)
      exact Real.tendsto_exp_atBot.comp this
    have h2 : Tendsto (fun Y : ℝ => |q| / Y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using h1.add h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [eventually_gt_atTop 0] with Y hY
  set E := Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ)) with hE
  have hden : Y ≤ ‖Complex.I * (Y : ℂ) - (q : ℂ)‖ := by
    have := Complex.abs_im_le_norm (Complex.I * (Y : ℂ) - (q : ℂ))
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, add_zero, sub_zero, zero_add] at this
    exact (le_abs_self Y).trans (by simpa using this)
  have hne : Complex.I * (Y : ℂ) - (q : ℂ) ≠ 0 := by
    intro h; rw [h, norm_zero] at hden; linarith
  have halg : (Y : ℂ) * (Complex.I * (1 - E) / (Complex.I * (Y : ℂ) - (q : ℂ))) - 1 =
      (-(Complex.I * (Y : ℂ) * E) + (q : ℂ)) / (Complex.I * (Y : ℂ) - (q : ℂ)) := by
    rw [eq_div_iff hne]
    have hc : (Y : ℂ) * (Complex.I * (1 - E) / (Complex.I * (Y : ℂ) - (q : ℂ))) *
        (Complex.I * (Y : ℂ) - (q : ℂ)) = (Y : ℂ) * (Complex.I * (1 - E)) := by
      rw [mul_assoc, div_mul_cancel₀ _ hne]
    linear_combination hc
  rw [halg, norm_div]
  have hnum : ‖-(Complex.I * (Y : ℂ) * E) + (q : ℂ)‖ ≤ Y * Real.exp (-(Y * L)) + |q| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hY, hE, norm_exp_iY, Complex.norm_real, Real.norm_eq_abs]
  have hden0 : 0 < ‖Complex.I * (Y : ℂ) - (q : ℂ)‖ := lt_of_lt_of_le hY hden
  calc ‖-(Complex.I * (Y : ℂ) * E) + (q : ℂ)‖ / ‖Complex.I * (Y : ℂ) - (q : ℂ)‖
      ≤ (Y * Real.exp (-(Y * L)) + |q|) / Y := by
        apply div_le_div₀ (by positivity) hnum hY hden
    _ = Real.exp (-(Y * L)) + |q| / Y := by field_simp

/-- **`Y a_1(iY) → 1`** (the one-sided approximate identity of `eq:root-approximate-identity`). -/
theorem a1_tendsto (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    Tendsto (fun Y : ℝ => (Y : ℂ) * kernelProductSymbol (orderedKernel L 1 (Complex.I * (Y : ℂ))) u)
      atTop (𝓝 1) := by
  set bl : MArr 1 → ℝ := fun m => bornLaw (meanField_physicalBasis L 1 Nat.one_pos hκ) u m with hbl
  have hpr : HasSum bl 1 := QuantumNLS.BetheCoefficientTransform.hasSum_bornLaw_unit
      (meanField_physicalBasis L 1 Nat.one_pos hκ) u hu
  have hp : HasSum (fun m : MArr 1 => (bl m : ℂ)) 1 := by
    have := hpr
    simpa using (Complex.hasSum_ofReal (f := bl) (x := 1)).2 this
  have hs : ∀ Y : ℝ, 0 < Y →
      (Y : ℂ) * kernelProductSymbol (orderedKernel L 1 (Complex.I * (Y : ℂ))) u =
        ∑' m : MArr 1, (bl m : ℂ) * ((Y : ℂ) * (Complex.I * (1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) /
          (Complex.I * (Y : ℂ) - (arrRoots L (κ / ((1 : ℕ) : ℝ)) m 0 : ℂ)))) := by
    intro Y hY
    have hz : 0 < (Complex.I * (Y : ℂ)).im := by simpa using hY
    have h := (hasSum_a1 hκ u hu hz).mul_left (Y : ℂ)
    rw [← h.tsum_eq]
    congr 1; ext m
    ring
  have hlim : Tendsto (fun Y : ℝ => ∑' m : MArr 1, (bl m : ℂ) *
      ((Y : ℂ) * (Complex.I * (1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) /
        (Complex.I * (Y : ℂ) - (arrRoots L (κ / ((1 : ℕ) : ℝ)) m 0 : ℂ))))) atTop
      (𝓝 (∑' m : MArr 1, (bl m : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => 2 * bl m) ?_ ?_ ?_
    · exact hpr.summable.mul_left 2
    · intro m
      have := (lam_tendsto (L := L) (arrRoots L (κ / ((1 : ℕ) : ℝ)) m 0)).const_mul (bl m : ℂ)
      simpa using this
    · filter_upwards [eventually_gt_atTop 0] with Y hY m
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _)]
      have := lam_bound (L := L) (arrRoots L (κ / ((1 : ℕ) : ℝ)) m 0) Y hY
      have hb0 : 0 ≤ bl m := QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _
      nlinarith
  rw [hp.tsum_eq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with Y hY
  exact (hs Y hY).symm

/-! ### The `r ≥ 2` terms and the Taylor expansion of `f_z` -/

theorem symbolTerm_le (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : 0 < z.im) (r : ℕ) (hr : 1 ≤ r) :
    ‖symbolTerm L κ u z r‖ ≤ 2 * (κ / z.im) ^ r := by
  unfold symbolTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hκ r)]
  have h1 : ‖kernelProductSymbol (orderedKernel L r z) u‖ ≤ ‖orderedKernel L r z‖ := by
    have := QuantumNLS.HighMomentsRank.norm_aa_le u hu (fun r => orderedKernel L r z) r
    simpa [QuantumNLS.HighMomentsRank.aa] using this
  have h2 : ‖orderedKernel L r z‖ ≤ 2 * (z.im)⁻¹ ^ r :=
    (lem_root_placement u hu (N := r) hr le_rfl z hz).1
  calc κ ^ r * ‖kernelProductSymbol (orderedKernel L r z) u‖ ≤ κ ^ r * (2 * (z.im)⁻¹ ^ r) := by
        gcongr; exact h1.trans h2
    _ = 2 * (κ / z.im) ^ r := by rw [div_pow, div_eq_mul_inv, inv_pow]; ring

theorem productSymbol_approx (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    ‖productSymbol L κ u z - (1 + Complex.exp (Complex.I * z * L)) -
        (κ : ℂ) * kernelProductSymbol (orderedKernel L 1 z) u‖ ≤ 8 / 3 * (κ / z.im) ^ 2 := by
  have hη : 0 < z.im := by linarith [hz.1]
  set x : ℝ := κ / z.im with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ≤ 1 / 4 := by rw [hx, div_le_iff₀ hη]; linarith [hz.1]
  set t : ℕ → ℂ := fun j => symbolTerm L κ u z (j + 1) with ht
  have htb : ∀ j, ‖t j‖ ≤ 2 * x ^ (j + 1) := fun j => symbolTerm_le hκ u hu hη (j + 1) (by omega)
  have hsum : Summable t := by
    refine Summable.of_norm_bounded (g := fun j => 2 * x ^ (j + 1)) ?_ htb
    exact ((summable_geometric_of_lt_one hx0 (by linarith)).mul_left (2 * x)).congr
      (fun j => by ring)
  have hps : productSymbol L κ u z - (1 + Complex.exp (Complex.I * z * L)) = ∑' j, t j := by
    unfold productSymbol; ring
  have h0 : t 0 = (κ : ℂ) * kernelProductSymbol (orderedKernel L 1 z) u := by
    simp [ht, symbolTerm]
  have hsplit : ∑' j, t j = t 0 + ∑' j, t (j + 1) := hsum.tsum_eq_zero_add
  have htail : ‖∑' j, t (j + 1)‖ ≤ 2 * x ^ 2 / (1 - x) := by
    have hg : HasSum (fun j : ℕ => 2 * x ^ 2 * x ^ j) (2 * x ^ 2 * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 (by linarith)).mul_left (2 * x ^ 2)
    have := tsum_of_norm_bounded hg (f := fun j => t (j + 1)) (fun j => by
      refine (htb (j + 1)).trans (le_of_eq ?_); ring)
    simpa [div_eq_mul_inv] using this
  calc ‖productSymbol L κ u z - (1 + Complex.exp (Complex.I * z * L)) -
        (κ : ℂ) * kernelProductSymbol (orderedKernel L 1 z) u‖
      = ‖∑' j, t (j + 1)‖ := by
        rw [hps, hsplit, h0]; congr 1; ring
    _ ≤ 2 * x ^ 2 / (1 - x) := htail
    _ ≤ 8 / 3 * x ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [sq_nonneg x]

theorem fz_taylor (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {w : ℂ} (hw : ‖w‖ ≤ (z.im)⁻¹) :
    ‖fz L κ z w - (1 + Complex.exp (Complex.I * z * L)) -
        Complex.I * κ * (1 - Complex.exp (Complex.I * z * L)) * w‖ ≤ 2 * (κ / z.im) ^ 2 := by
  have hη : 0 < z.im := by linarith [hz.1]
  have hx4 : κ / z.im ≤ 1 / 4 := by rw [div_le_iff₀ hη]; linarith [hz.1]
  set a : ℂ := Complex.I * κ * w with ha
  have han : ‖a‖ ≤ κ / z.im := by
    rw [ha, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      one_mul, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hw hκ.le
  have ha1 : ‖a‖ ≤ 1 := han.trans (hx4.trans (by norm_num))
  have h1 := Complex.norm_exp_sub_one_sub_id_le ha1
  have h2 := Complex.norm_exp_sub_one_sub_id_le (x := -a) (by rwa [norm_neg])
  rw [norm_neg] at h2
  set E := Complex.exp (Complex.I * z * L) with hE
  have hEn : ‖E‖ ≤ 1 := (norm_exp_izL_le hz).trans (by norm_num)
  have hrew : fz L κ z w - (1 + E) - Complex.I * κ * (1 - E) * w =
      (Complex.exp a - 1 - a) + E * (Complex.exp (-a) - 1 - (-a)) := by
    unfold fz
    rw [← hE, ← ha]
    ring
  rw [hrew]
  have hsq : ‖a‖ ^ 2 ≤ (κ / z.im) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) han 2
  calc ‖(Complex.exp a - 1 - a) + E * (Complex.exp (-a) - 1 - (-a))‖
      ≤ ‖Complex.exp a - 1 - a‖ + ‖E‖ * ‖Complex.exp (-a) - 1 - (-a)‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ ‖a‖ ^ 2 + 1 * ‖a‖ ^ 2 := by
        gcongr
    _ ≤ 2 * (κ / z.im) ^ 2 := by nlinarith

/-! ### `iY g(iY) → 1` -/

theorem highHalf_iY (hκ : 0 < κ) :
    ∀ᶠ Y : ℝ in atTop, HighHalf L κ (Complex.I * (Y : ℂ)) := by
  have hL : 0 < L := Fact.out
  filter_upwards [eventually_ge_atTop (max (4 * κ) (Real.log 16 / L)), eventually_gt_atTop 0] with Y hY hY0
  have him : (Complex.I * (Y : ℂ)).im = Y := by simp
  refine ⟨by rw [him]; exact (le_max_left _ _).trans hY, ?_⟩
  rw [him]
  have : Real.log 16 / L ≤ Y := (le_max_right _ _).trans hY
  rwa [div_le_iff₀ hL, mul_comm] at this

/-- **Step 4**: if `g(Y)` solves `f_{iY}(g(Y)) = s(iY;u)` in `|w| ≤ Y⁻¹`, then `iY g(Y) → 1`. -/
theorem iYg_tendsto (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (g : ℝ → ℂ)
    (hg : ∀ Y : ℝ, HighHalf L κ (Complex.I * (Y : ℂ)) →
      ‖g Y‖ ≤ Y⁻¹ ∧ fz L κ (Complex.I * (Y : ℂ)) (g Y) = productSymbol L κ u (Complex.I * (Y : ℂ))) :
    Tendsto (fun Y : ℝ => Complex.I * (Y : ℂ) * g Y) atTop (𝓝 1) := by
  have hev := highHalf_iY (L := L) hκ
  have ha := a1_tendsto hκ u hu
  have hE : Tendsto (fun Y : ℝ => Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) atTop (𝓝 0) := by
    have hL : 0 < L := Fact.out
    have h1 : Tendsto (fun Y : ℝ => Real.exp (-(Y * L))) atTop (𝓝 0) := by
      have : Tendsto (fun Y : ℝ => -(Y * L)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hL)
      exact Real.tendsto_exp_atBot.comp this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h1.congr (fun Y => ?_)
    rw [norm_exp_iY]
  have hkey : ∀ᶠ Y : ℝ in atTop,
      ‖Complex.I * (1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) * ((Y : ℂ) * g Y) -
        (Y : ℂ) * kernelProductSymbol (orderedKernel L 1 (Complex.I * (Y : ℂ))) u‖ ≤ 14 / 3 * κ / Y := by
    filter_upwards [hev, eventually_gt_atTop 0] with Y hY hY0
    obtain ⟨hgn, hgf⟩ := hg Y hY
    have him : (Complex.I * (Y : ℂ)).im = Y := by simp
    have hgn' : ‖g Y‖ ≤ (((Complex.I * (Y : ℂ)).im)⁻¹) := by rwa [him]
    have h1 := productSymbol_approx hκ u hu hY
    have h2 := fz_taylor hκ hY hgn'
    rw [hgf] at h2
    simp only [him] at h1 h2
    set E := Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ)) with hE
    set a1 := kernelProductSymbol (orderedKernel L 1 (Complex.I * (Y : ℂ))) u with ha1
    set s := productSymbol L κ u (Complex.I * (Y : ℂ)) with hs
    have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hid : (κ : ℂ) * (Complex.I * (1 - E) * g Y - a1) =
        (s - (1 + E) - κ * a1) - (s - (1 + E) - Complex.I * κ * (1 - E) * g Y) := by ring
    have hnorm : ‖(κ : ℂ) * (Complex.I * (1 - E) * g Y - a1)‖ ≤ 8 / 3 * (κ / Y) ^ 2 + 2 * (κ / Y) ^ 2 := by
      rw [hid]
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hform : Complex.I * (1 - E) * ((Y : ℂ) * g Y) - (Y : ℂ) * a1 =
        ((Y : ℂ) / κ) * ((κ : ℂ) * (Complex.I * (1 - E) * g Y - a1)) := by
      field_simp
    rw [hform, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hY0, abs_of_pos hκ]
    calc Y / κ * ‖(κ : ℂ) * (Complex.I * (1 - E) * g Y - a1)‖
        ≤ Y / κ * (8 / 3 * (κ / Y) ^ 2 + 2 * (κ / Y) ^ 2) := by gcongr
      _ = 14 / 3 * κ / Y := by field_simp; ring
  have hD : Tendsto (fun Y : ℝ => Complex.I * (1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) *
      ((Y : ℂ) * g Y) - (Y : ℂ) * kernelProductSymbol (orderedKernel L 1 (Complex.I * (Y : ℂ))) u)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hkey ?_
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hN : Tendsto (fun Y : ℝ => Complex.I * (1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) *
      ((Y : ℂ) * g Y)) atTop (𝓝 1) := by
    have := ha.add hD
    rw [add_zero] at this
    refine this.congr (fun Y => ?_)
    ring
  have hden : Tendsto (fun Y : ℝ => 1 - Complex.exp (Complex.I * (Complex.I * (Y : ℂ)) * (L : ℂ))) atTop
      (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).sub hE
  have hfin := hN.div hden one_ne_zero
  rw [div_one] at hfin
  have hne := hden.eventually_ne (one_ne_zero (α := ℂ))
  refine hfin.congr' ?_
  filter_upwards [hne] with Y hY
  simp only [Pi.div_apply]
  rw [div_eq_iff hY]
  ring

/-- **No loss of mass, scalar form**: `1 + Y Im g(Y) → 0`, i.e. `Re (iY g(Y)) → 1`. -/
theorem one_add_mul_im_tendsto (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (g : ℝ → ℂ)
    (hg : ∀ Y : ℝ, HighHalf L κ (Complex.I * (Y : ℂ)) →
      ‖g Y‖ ≤ Y⁻¹ ∧ fz L κ (Complex.I * (Y : ℂ)) (g Y) = productSymbol L κ u (Complex.I * (Y : ℂ))) :
    Tendsto (fun Y : ℝ => 1 + Y * (g Y).im) atTop (𝓝 0) := by
  have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp (iYg_tendsto hκ u hu g hg)
  have h' : Tendsto (fun Y : ℝ => 1 + Y * (g Y).im) atTop (𝓝 (1 - (1 : ℂ).re)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    refine this.congr (fun Y => ?_)
    simp [Complex.mul_re]
  simpa using h'

end QuantumNLS.RootMeasureNoLoss

#print axioms QuantumNLS.RootMeasureNoLoss.hasSum_a1
#print axioms QuantumNLS.RootMeasureNoLoss.a1_tendsto
#print axioms QuantumNLS.RootMeasureNoLoss.productSymbol_approx
#print axioms QuantumNLS.RootMeasureNoLoss.fz_taylor
#print axioms QuantumNLS.RootMeasureNoLoss.iYg_tendsto
#print axioms QuantumNLS.RootMeasureNoLoss.one_add_mul_im_tendsto
