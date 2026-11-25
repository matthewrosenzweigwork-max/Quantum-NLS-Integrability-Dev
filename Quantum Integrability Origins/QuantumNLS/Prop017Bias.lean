import QuantumNLS.RootMeasureConcentrationSharp
import QuantumNLS.HighMomentsAssembly

/-!
# PROP-017 physical assembly, step 1: the bias of the Born mean of `G_N`

Source: `source-text/chapters/propagation/window_reconstruction.tex:21-31` (model hypothesis 1, `Q7A:eq:tail`). The quantum
tail estimate is proved (module `Prop017Tail`) through Stieltjes kernels, whose Born expectations are linear in the Born mean of the
random Cauchy transform `G_N(z)`. This module proves that this mean has bias `O(1/(N η²))` (`Im z = η`, high half-plane), not
only the `O(1/(√N η))` that the mean-square estimate gives:

* `first_moment`: for the high-moment data `X_N = A_0 + Σ_r (N)_r/N^r U_{N,r}(A_r)`,
  `⟨u^{⊗N}, X_N u^{⊗N}⟩ = x + b_N` exactly (the centered part `Y_N` has vanishing product-state expectation: the single-factor
  case of the isolated-vertex lemma `HighMomentsOps.word_iso`);
* `norm_bN_Afam_le`: for the physical transfer data `A_r = κ^r K_{r,z}`, `|b_N| ≤ Cb x²/N`, `x = κ/η` (the `r = 1` term of `b_N`
  vanishes since `(N)_1/N = 1`; this is the improvement over the generic `O(x/N)`);
* `born_mean_sProd`: `Σ_m born_m s_N(m;z) = s(z;u) + b_N` under the Born law of the actual physical basis;
* **`born_mean_G`**: `|Σ_m born_m G_N(m;z) − g(z)| ≤ Cg κ/(N η²)` for every `z` in the high half-plane, with an absolute constant
  `Cg` (second-order expansion of `f_z(w) = e^{iκw} + e^{izL}e^{−iκw}` at `g`, using `eq:root-product-error` and the sharp
  concentration estimate).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop017Bias

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.RootMeasureComplex (sProd GN fz HighHalf norm_exp_izL_le norm_exp_le_four_thirds
  exp_quarter_le product_error)
open QuantumNLS.NormalizedTransfer (productSymbol normalizedTransfer orderedKernel)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.HighMomentsRank (Xop xlim Yop bN aa fallR centered_identity abs_fallR_sub_one_le
  norm_aa_le)
open QuantumNLS.HighMomentsOps (wvec Tf word_iso)
open QuantumNLS.HighMomentsAssembly (Yfull coe_Yop expect_expand)
open QuantumNLS.HighMomentsWord (wprod wprod_const)
open QuantumNLS.HighMomentsTransfer (Afam summable_rankSum)
open QuantumNLS.RootMeasureConcentration (norm_GN_le gStar gStar_spec)
open QuantumNLS.RootMeasureConcentrationSharp (T summable_T T_nonneg Csharp Kc_nonneg tsum_G_sharp)
open QuantumNLS.RootPlacementBound (lem_root_placement)
open QuantumNLS.KernelDefinition QuantumNLS.TensorCarrier

/-! ## 1. The first moment of the high-moment operator -/

section First

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The centered part has vanishing product-state expectation. -/
theorem inner_Yop (u : H) (hu : ‖u‖ = 1) (A : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) :
    ⟪wvec N u, Yop u A N (wvec N u)⟫_ℂ = 0 := by
  have h1 : ⟪wvec N u, Yop u A N (wvec N u)⟫_ℂ =
      ⟪(htpow N u : HilbertTensorPower ℂ H N), Yfull u A N (htpow N u)⟫_ℂ := by
    rw [Submodule.coe_inner, coe_Yop]; rfl
  rw [h1]
  have h2 : Yfull u A N = wprod 1 (fun _ : Fin 1 => Yfull u A N) := by rw [wprod_const, pow_one]
  rw [h2, expect_expand (m := 1) u (fun _ => A) (fun _ : Fin 1 => Yfull u A N) (fun _ => rfl)]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hw := word_iso (m := 0) u hu (fun _ => A) s 0 (fun i hi => absurd (Fin.fin_one_eq_zero i) hi)
  beta_reduce at hw ⊢
  rw [hw, mul_zero]

/-- **First moment**: `⟨u^{⊗N}, X_N u^{⊗N}⟩ = x + b_N`. -/
theorem first_moment (u : H) (hu : ‖u‖ = 1) (A0 : ℂ) (A : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (hsum : Summable (fun j : ℕ => aa u A (j + 1))) (N : ℕ) :
    ⟪wvec N u, Xop A0 A N (wvec N u)⟫_ℂ = xlim u A0 A + bN u A N := by
  have hc := centered_identity u A0 A N hsum
  have e : Xop A0 A N = xlim u A0 A • ContinuousLinearMap.id ℂ (SymSector ℂ H N) +
      (Yop u A N + bN u A N • ContinuousLinearMap.id ℂ (SymSector ℂ H N)) := by
    rw [← hc]; abel
  have hw : ⟪wvec N u, wvec N u⟫_ℂ = 1 := QuantumNLS.HighMomentsOps.inner_wvec N u hu
  rw [e]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right, hw, inner_Yop u hu A N]
  ring

end First

/-! ## 2. The refined bias bound for the physical transfer data -/

section Bias

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The absolute bias constant `Cb = 4 T₂ + 8/3`. -/
def Cb : ℝ := 4 * T 2 + 8 / 3

lemma Cb_nonneg : 0 ≤ Cb := by have := T_nonneg 2; unfold Cb; positivity

lemma norm_Afam_le_x (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) (j : ℕ) :
    ‖Afam L κ z (j + 1)‖ ≤ 2 * (κ / z.im) ^ (j + 1) := by
  have hη : 0 < z.im := by linarith [hz.1]
  have hK : ‖orderedKernel L (j + 1) z‖ ≤ 2 * (z.im)⁻¹ ^ (j + 1) :=
    (lem_root_placement u hu (N := j + 1) (by omega) le_rfl z hη).1
  unfold Afam
  calc ‖((κ ^ (j + 1) : ℝ) : ℂ) • orderedKernel L (j + 1) z‖
      ≤ ‖((κ ^ (j + 1) : ℝ) : ℂ)‖ * ‖orderedKernel L (j + 1) z‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ = κ ^ (j + 1) * ‖orderedKernel L (j + 1) z‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ.le _)]
    _ ≤ κ ^ (j + 1) * (2 * (z.im)⁻¹ ^ (j + 1)) := mul_le_mul_of_nonneg_left hK (pow_nonneg hκ.le _)
    _ = 2 * (κ / z.im) ^ (j + 1) := by rw [div_eq_mul_inv, mul_pow]; ring

lemma pow_le_inv_nat (N : ℕ) (hN : 0 < N) : (1 / 4 : ℝ) ^ (N - 1) ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) ≤ 4 ^ (N - 1) := by
    have h0 : N - 1 < 4 ^ (N - 1) := Nat.lt_pow_self (by norm_num)
    have : N ≤ 4 ^ (N - 1) := by omega
    exact_mod_cast this
  rw [div_pow, one_pow, one_div_le_one_div (by positivity) hNr]
  exact h1

/-- **Refined bias bound** `|b_N| ≤ Cb (κ/η)²/N` for `A_r = κ^r K_{r,z}`. -/
theorem norm_bN_Afam_le (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z)
    {N : ℕ} (hN : 0 < N) : ‖bN u (Afam L κ z) N‖ ≤ Cb * (κ / z.im) ^ 2 / N := by
  have hη : 0 < z.im := by linarith [hz.1]
  set x : ℝ := κ / z.im with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ≤ 1 / 4 := by rw [hx, div_le_iff₀ hη]; linarith [hz.1]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have haa : ∀ j : ℕ, ‖aa u (Afam L κ z) (j + 1)‖ ≤ 2 * x ^ (j + 1) := fun j =>
    (norm_aa_le u hu _ _).trans (norm_Afam_le_x hκ u hu hz j)
  -- head
  have hhead : ‖∑ j ∈ Finset.range N, (((fallR N (j + 1) : ℝ) : ℂ) - 1) * aa u (Afam L κ z) (j + 1)‖ ≤
      4 * T 2 * x ^ 2 / N := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range N, ‖(((fallR N (j + 1) : ℝ) : ℂ) - 1) * aa u (Afam L κ z) (j + 1)‖ ≤
        x ^ 2 / N * (4 * (((j + 1 : ℕ) : ℝ) ^ 2 * (1 / 4 : ℝ) ^ j)) := by
      intro j hj
      have hjN : j + 1 ≤ N := Finset.mem_range.mp hj
      rw [norm_mul, show (((fallR N (j + 1) : ℝ) : ℂ) - 1) = ((fallR N (j + 1) - 1 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      rcases Nat.eq_zero_or_pos j with h0 | hjpos
      · subst h0
        have : fallR N 1 = 1 := by
          unfold fallR; rw [Nat.descFactorial_one, pow_one]; exact div_self hNr.ne'
        rw [this, sub_self, abs_zero, zero_mul]
        positivity
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have h1 := abs_fallR_sub_one_le N hN (i + 1 + 1) hjN
        have h2 := haa (i + 1)
        have hxj : x ^ (i + 1 + 1) ≤ x ^ 2 * (1 / 4 : ℝ) ^ i := by
          rw [show i + 1 + 1 = 2 + i by omega, pow_add]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx4 _) (by positivity)
        calc |fallR N (i + 1 + 1) - 1| * ‖aa u (Afam L κ z) (i + 1 + 1)‖
            ≤ ((((i + 1 + 1 : ℕ) : ℝ)) ^ 2 / (2 * N)) * (2 * x ^ (i + 1 + 1)) :=
              mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
          _ = (((i + 1 + 1 : ℕ) : ℝ)) ^ 2 / N * x ^ (i + 1 + 1) := by field_simp
          _ ≤ (((i + 1 + 1 : ℕ) : ℝ)) ^ 2 / N * (x ^ 2 * (1 / 4 : ℝ) ^ i) :=
              mul_le_mul_of_nonneg_left hxj (by positivity)
          _ = x ^ 2 / N * (4 * (((i + 1 + 1 : ℕ) : ℝ) ^ 2 * (1 / 4 : ℝ) ^ (i + 1))) := by
              rw [pow_succ]; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hs := (summable_T 2).sum_le_tsum (Finset.range N) (fun j _ => by positivity)
    have hT : ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ 2 * (1 / 4 : ℝ) ^ j ≤ T 2 := hs
    calc x ^ 2 / N * (4 * ∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ) ^ 2 * (1 / 4 : ℝ) ^ j)
        ≤ x ^ 2 / N * (4 * T 2) := by gcongr
      _ = 4 * T 2 * x ^ 2 / N := by ring
  -- tail
  have htail : ‖∑' k : ℕ, aa u (Afam L κ z) (k + N + 1)‖ ≤ 8 / 3 * x ^ 2 / N := by
    have hgeo : HasSum (fun k : ℕ => 2 * x ^ (N + 1) * x ^ k) (2 * x ^ (N + 1) * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 (by linarith)).mul_left _
    have hb : ∀ k : ℕ, ‖aa u (Afam L κ z) (k + N + 1)‖ ≤ 2 * x ^ (N + 1) * x ^ k := fun k => by
      refine (haa (k + N)).trans (le_of_eq ?_)
      rw [show k + N + 1 = (N + 1) + k by omega, pow_add]; ring
    have hsumm : Summable (fun k : ℕ => aa u (Afam L κ z) (k + N + 1)) :=
      Summable.of_norm_bounded hgeo.summable hb
    refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
      hgeo.summable)).trans ?_
    refine (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hgeo.summable)
      hgeo.summable).trans ?_
    rw [hgeo.tsum_eq]
    have h1 : (1 - x)⁻¹ ≤ 4 / 3 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : x ^ (N + 1) ≤ x ^ 2 * (1 / 4 : ℝ) ^ (N - 1) := by
      rw [show N + 1 = 2 + (N - 1) by omega, pow_add]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx4 _) (by positivity)
    have h3 := pow_le_inv_nat N hN
    have h4 : x ^ (N + 1) ≤ x ^ 2 / N := by
      refine h2.trans ?_
      calc x ^ 2 * (1 / 4 : ℝ) ^ (N - 1) ≤ x ^ 2 * (1 / N) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = x ^ 2 / N := by ring
    have h5 : 0 ≤ x ^ (N + 1) := by positivity
    calc 2 * x ^ (N + 1) * (1 - x)⁻¹ ≤ 2 * x ^ (N + 1) * (4 / 3) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2 * (x ^ 2 / N) * (4 / 3) := by gcongr
      _ = 8 / 3 * x ^ 2 / N := by ring
  unfold bN
  refine (norm_sub_le _ _).trans ?_
  calc _ ≤ 4 * T 2 * x ^ 2 / N + 8 / 3 * x ^ 2 / N := add_le_add hhead htail
    _ = Cb * x ^ 2 / N := by unfold Cb; ring

end Bias

/-! ## 3. Born means -/

section Born

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- `E s_N(z) = s(z;u) + b_N` under the Born law of the actual physical basis. -/
theorem born_mean_sProd (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    HasSum (fun m : MArr N => (bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) u m : ℂ) *
        sProd L κ N (arrRoots L (κ / N) m) z)
      (productSymbol L κ u z + bN u (Afam L κ z) N) := by
  classical
  have hη : 0 < z.im := by linarith [hz.1]
  have h := QuantumNLS.RootMeasureTransfer.hasSum_inner_diag
    (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) (normalizedTransfer L κ N z)
    (fun m => QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m z)
    (fun m => QuantumNLS.UnconditionalBetheBasis.transfer_physicalBasis hκ hN z m) (wvec N u)
  have e1 : normalizedTransfer L κ N z = Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N :=
    QuantumNLS.NormalizedTransfer.normalizedTransfer_eq_Xop L κ N z
  have e2 : productSymbol L κ u z = xlim u (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) :=
    QuantumNLS.NormalizedTransfer.productSymbol_eq_xlim L κ u z
  have hsum : Summable (fun j : ℕ => aa u (Afam L κ z) (j + 1)) :=
    QuantumNLS.HighMomentsRank.summable_aa u hu _
      (by simpa using summable_rankSum (L := L) hκ.le (b := 0) le_rfl z (by simpa using hη.le) 1)
  have hfm := first_moment u hu (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) hsum N
  rw [← e1, ← e2] at hfm
  rw [hfm] at h
  refine h.congr_fun fun m => ?_
  rw [QuantumNLS.RootMeasureTransfer.eigen_eq_sProd hκ hN m z hη]
  rfl

lemma bornLaw_hasSum_one' (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) :
    HasSum (bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) u) 1 :=
  QuantumNLS.UnconditionalBetheBasis.bornLaw_hasSum_one L N hN (κ / N) (div_pos hκ (by exact_mod_cast hN)) u hu

/-- The derivative `f_z'(g) = iκ(e^{iκg} − e^{izL}e^{−iκg})`. -/
def fzd (L κ : ℝ) (z w : ℂ) : ℂ :=
  Complex.I * κ * (Complex.exp (Complex.I * κ * w) - Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * w)))

lemma norm_exp_ge {w : ℂ} (hw : ‖w‖ ≤ 1 / 4) : 3 / 4 ≤ ‖Complex.exp w‖ := by
  rw [Complex.norm_exp]
  have h1 : -(1 / 4 : ℝ) ≤ w.re := by
    have := Complex.abs_re_le_norm w; have := neg_abs_le w.re; linarith
  have h2 : Real.exp (-(1 / 4)) ≤ Real.exp w.re := Real.exp_le_exp.2 h1
  have h3 : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4)) := by
    have := exp_quarter_le
    have h4 : Real.exp (-(1 / 4)) * Real.exp (1 / 4) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-(1 / 4)), Real.exp_pos (1 / 4)]
  linarith

lemma norm_iκw_le (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {w : ℂ} (hw : ‖w‖ ≤ (z.im)⁻¹) :
    ‖Complex.I * κ * w‖ ≤ 1 / 4 := by
  have hη : 0 < z.im := by linarith [hz.1]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  calc κ * ‖w‖ ≤ κ * (z.im)⁻¹ := mul_le_mul_of_nonneg_left hw hκ.le
    _ ≤ 1 / 4 := by rw [← div_eq_mul_inv, div_le_iff₀ hη]; linarith [hz.1]

lemma norm_fzd_ge (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {g : ℂ} (hg : ‖g‖ ≤ (z.im)⁻¹) :
    2 * κ / 3 ≤ ‖fzd L κ z g‖ := by
  have h1 := norm_iκw_le hκ hz hg
  have he := norm_exp_izL_le hz
  have hA := norm_exp_ge h1
  have hB := norm_exp_le_four_thirds (x := -(Complex.I * κ * g)) (by rw [norm_neg]; exact h1)
  unfold fzd
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  have h2 : ‖Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * g))‖ ≤ 1 / 12 := by
    rw [norm_mul]
    calc _ ≤ 1 / 16 * (4 / 3) := mul_le_mul he hB (norm_nonneg _) (by norm_num)
      _ = 1 / 12 := by norm_num
  have h3 := norm_sub_norm_le (Complex.exp (Complex.I * κ * g))
    (Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * g)))
  nlinarith

/-- Second-order expansion of `f_z` at `g`. -/
lemma fz_taylor (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {g w : ℂ} (hg : ‖g‖ ≤ (z.im)⁻¹)
    (hw : ‖w‖ ≤ (z.im)⁻¹) :
    ‖fz L κ z w - fz L κ z g - fzd L κ z g * (w - g)‖ ≤ 2 * κ ^ 2 * ‖w - g‖ ^ 2 := by
  have hη : 0 < z.im := by linarith [hz.1]
  set t : ℂ := Complex.I * κ * (w - g) with ht
  have h1 := norm_iκw_le hκ hz hg
  have h2 := norm_iκw_le hκ hz hw
  have htn : ‖t‖ = κ * ‖w - g‖ := by
    rw [ht, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
  have ht1 : ‖t‖ ≤ 1 := by
    have : t = Complex.I * κ * w - Complex.I * κ * g := by rw [ht]; ring
    rw [this]; refine (norm_sub_le _ _).trans ?_; linarith
  have e : fz L κ z w - fz L κ z g - fzd L κ z g * (w - g) =
      Complex.exp (Complex.I * κ * g) * (Complex.exp t - 1 - t) +
        Complex.exp (Complex.I * z * L) * Complex.exp (-(Complex.I * κ * g)) *
          (Complex.exp (-t) - 1 - -t) := by
    unfold fz fzd
    have ea : Complex.exp (Complex.I * κ * w) = Complex.exp (Complex.I * κ * g) * Complex.exp t := by
      rw [← Complex.exp_add, ht]; ring_nf
    have eb : Complex.exp (-(Complex.I * κ * w)) =
        Complex.exp (-(Complex.I * κ * g)) * Complex.exp (-t) := by
      rw [← Complex.exp_add, ht]; ring_nf
    rw [ea, eb, ht]; ring
  rw [e]
  have hA := norm_exp_le_four_thirds h1
  have hB := norm_exp_le_four_thirds (x := -(Complex.I * κ * g)) (by rw [norm_neg]; exact h1)
  have he := norm_exp_izL_le hz
  have h3 : ‖Complex.exp t - 1 - t‖ ≤ ‖t‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le ht1
  have h4 : ‖Complex.exp (-t) - 1 - -t‖ ≤ ‖t‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := -t) (by rw [norm_neg]; exact ht1)
    rwa [norm_neg] at this
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul]
  have h5 : ‖Complex.exp (Complex.I * z * L)‖ * ‖Complex.exp (-(Complex.I * κ * g))‖ ≤ 1 / 12 := by
    calc _ ≤ 1 / 16 * (4 / 3) := mul_le_mul he hB (norm_nonneg _) (by norm_num)
      _ = 1 / 12 := by norm_num
  have h6 : ‖t‖ ^ 2 = κ ^ 2 * ‖w - g‖ ^ 2 := by rw [htn]; ring
  have := norm_nonneg (Complex.exp t - 1 - t)
  have := norm_nonneg (Complex.exp (-t) - 1 - -t)
  nlinarith

/-- The absolute constant of the `G`-bias. -/
def Cg : ℝ := 3 / 2 * (Cb + 3 + 2 * Csharp)

/-- **Bias of the Born mean of `G_N`**: `|E G_N(z) − g(z)| ≤ Cg κ/(N η²)` on the high half-plane. -/
theorem born_mean_G (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    ∃ EG : ℂ, HasSum (fun m : MArr N =>
        (bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) u m : ℂ) *
          GN N (arrRoots L (κ / N) m) z) EG ∧
      ‖EG - gStar L κ hκ u hu z‖ ≤ Cg * κ / (N * z.im ^ 2) := by
  have hη : 0 < z.im := by linarith [hz.1]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set Ψ := QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ with hΨ
  set p : MArr N → ℝ := bornLaw Ψ u with hp
  have hp0 : ∀ m, 0 ≤ p m := fun m => QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _
  have hp1 : HasSum p 1 := bornLaw_hasSum_one' hκ hN u hu
  set g := gStar L κ hκ u hu z with hgdef
  obtain ⟨hg1, hg2⟩ := gStar_spec hκ u hu hz
  set Gm : MArr N → ℂ := fun m => GN N (arrRoots L (κ / N) m) z with hGm
  have hGb : ∀ m, ‖Gm m‖ ≤ (z.im)⁻¹ := fun m => norm_GN_le _ hη
  set x : ℝ := κ / z.im with hx
  set d := fzd L κ z g with hd
  have hd0 : 2 * κ / 3 ≤ ‖d‖ := norm_fzd_ge hκ hz hg1
  have hdne : d ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hd0; linarith
  -- the pointwise expansion `G_m − g = (s_m − s)/d + E_m`
  set Em : MArr N → ℂ := fun m => (Gm m - g) - (sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z) / d
    with hEm
  have hEb : ∀ m, ‖Em m‖ ≤ (3 * x ^ 2 / N + 2 * κ ^ 2 * ‖Gm m - g‖ ^ 2) / ‖d‖ := by
    intro m
    have hpe := product_error hκ hz hN (arrRoots L (κ / N) m)
    have hT := fz_taylor hκ hz hg1 (hGb m)
    have e : Em m = -((sProd L κ N (arrRoots L (κ / N) m) z - fz L κ z (Gm m)) +
        (fz L κ z (Gm m) - fz L κ z g - d * (Gm m - g))) / d := by
      simp only [hEm, ← hg2]
      field_simp
      ring
    rw [e, norm_div, norm_neg]
    refine div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add hpe hT)) (norm_nonneg _)
  -- summability
  have hsG : Summable (fun m => (p m : ℂ) * Gm m) := by
    refine Summable.of_norm_bounded (hp1.summable.mul_right (z.im)⁻¹) fun m => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 m)]
    exact mul_le_mul_of_nonneg_left (hGb m) (hp0 m)
  obtain ⟨EG, hEG⟩ := hsG
  refine ⟨EG, hEG, ?_⟩
  -- the mean of the linear part
  have hS := born_mean_sProd hκ hN u hu hz
  have hlin : HasSum (fun m => (p m : ℂ) * ((sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z) / d))
      (bN u (Afam L κ z) N / d) := by
    have h1 := hS.sub ((Complex.hasSum_ofReal.2 hp1).mul_right (productSymbol L κ u z))
    have h2 := h1.div_const d
    have e : (productSymbol L κ u z + bN u (Afam L κ z) N - ((1 : ℝ) : ℂ) * productSymbol L κ u z) / d =
        bN u (Afam L κ z) N / d := by push_cast; ring
    rw [e] at h2
    refine h2.congr_fun fun m => ?_
    ring
  have hg' : HasSum (fun m => (p m : ℂ) * g) g := by
    have := (Complex.hasSum_ofReal.2 hp1).mul_right g; simpa using this
  -- the remainder mean
  have hEmS : HasSum (fun m => (p m : ℂ) * Em m) (EG - g - bN u (Afam L κ z) N / d) := by
    have := (hEG.sub hg').sub hlin
    refine this.congr_fun fun m => ?_
    simp only [hEm]; ring
  -- bounds
  have hvar := tsum_G_sharp hκ hN u hu hz
  have hvsum : Summable (fun m => p m * ‖Gm m - g‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hp0 m) (sq_nonneg _)) (fun m => ?_)
      (hp1.summable.mul_right ((2 * (z.im)⁻¹) ^ 2))
    refine mul_le_mul_of_nonneg_left ?_ (hp0 m)
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hGb m])) 2
  have hboundS : HasSum (fun m => p m * ((3 * x ^ 2 / N + 2 * κ ^ 2 * ‖Gm m - g‖ ^ 2) / ‖d‖))
      ((3 * x ^ 2 / N + 2 * κ ^ 2 * ∑' m, p m * ‖Gm m - g‖ ^ 2) / ‖d‖) := by
    have h1 := (hp1.mul_right (3 * x ^ 2 / N)).add (hvsum.hasSum.mul_left (2 * κ ^ 2))
    have h2 := h1.div_const ‖d‖
    rw [one_mul] at h2
    refine h2.congr_fun fun m => ?_
    ring
  have hEmb : ‖EG - g - bN u (Afam L κ z) N / d‖ ≤
      (3 * x ^ 2 / N + 2 * κ ^ 2 * ∑' m, p m * ‖Gm m - g‖ ^ 2) / ‖d‖ := by
    refine hEmS.norm_le_of_bounded hboundS fun m => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 m)]
    exact mul_le_mul_of_nonneg_left (hEb m) (hp0 m)
  have hbN := norm_bN_Afam_le hκ u hu hz hN
  have hdpos : 0 < ‖d‖ := lt_of_lt_of_le (by positivity) hd0
  have hvar' : ∑' m, p m * ‖Gm m - g‖ ^ 2 ≤ Csharp / (N * z.im ^ 2) := hvar
  have hx2 : x ^ 2 = κ ^ 2 / z.im ^ 2 := by rw [hx, div_pow]
  have hfin : ‖EG - g‖ ≤ (Cb * x ^ 2 / N + 3 * x ^ 2 / N + 2 * κ ^ 2 * (Csharp / (N * z.im ^ 2))) / ‖d‖ := by
    have e : EG - g = (EG - g - bN u (Afam L κ z) N / d) + bN u (Afam L κ z) N / d := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div]
    have h1 : (3 * x ^ 2 / N + 2 * κ ^ 2 * ∑' m, p m * ‖Gm m - g‖ ^ 2) / ‖d‖ ≤
        (3 * x ^ 2 / N + 2 * κ ^ 2 * (Csharp / (N * z.im ^ 2))) / ‖d‖ := by
      gcongr
    have h2 : ‖bN u (Afam L κ z) N‖ / ‖d‖ ≤ Cb * x ^ 2 / N / ‖d‖ :=
      div_le_div_of_nonneg_right hbN hdpos.le
    calc _ ≤ (3 * x ^ 2 / N + 2 * κ ^ 2 * (Csharp / (N * z.im ^ 2))) / ‖d‖ + Cb * x ^ 2 / N / ‖d‖ :=
          add_le_add (hEmb.trans h1) h2
      _ = _ := by ring
  refine hfin.trans ?_
  have hnum0 : 0 ≤ Cb * x ^ 2 / N + 3 * x ^ 2 / N + 2 * κ ^ 2 * (Csharp / (N * z.im ^ 2)) := by
    have := Cb_nonneg; have : 0 ≤ Csharp := by unfold Csharp; have := Kc_nonneg; positivity
    positivity
  calc (Cb * x ^ 2 / N + 3 * x ^ 2 / N + 2 * κ ^ 2 * (Csharp / (N * z.im ^ 2))) / ‖d‖
      ≤ (Cb * x ^ 2 / N + 3 * x ^ 2 / N + 2 * κ ^ 2 * (Csharp / (N * z.im ^ 2))) / (2 * κ / 3) :=
        div_le_div_of_nonneg_left hnum0 (by positivity) hd0
    _ = Cg * κ / (N * z.im ^ 2) := by
        rw [hx2]; unfold Cg; field_simp

end Born

end QuantumNLS.Prop017Bias

#print axioms QuantumNLS.Prop017Bias.first_moment
#print axioms QuantumNLS.Prop017Bias.norm_bN_Afam_le
#print axioms QuantumNLS.Prop017Bias.born_mean_sProd
#print axioms QuantumNLS.Prop017Bias.born_mean_G
