import Mathlib
import QuantumNLS.RootMeasureExistence

/-!
# R-09E1EAE9 `thm:root-measure`: the printed concentration estimate `eq:root-G-concentration`

Source: `ROOT_spectral_measure.tex`, `thm:root-measure`: for `Im z = η ≥ η₀`,
`E|G_N(z) − g(z)|² ≤ C/(N η²)` with `C` depending only on `L, κ`.

`RootMeasureExistence.tendsto_prob_G` used the uniform PROP-008 constant `Cunif` (no `η`-dependence).  This module recovers the printed `η⁻²`
decay from the abstract high-moment lemma `HighMomentsFinal.high_moments_of_normal` applied to the physical transfer with the SHARP rank sums
`S_q(A_z) = Σ_r r^q κ^r ‖K_{r,z}‖ ≤ 2 T_q x`, `x = κ/η ≤ 1/4`, `T_q = Σ_j (j+1)^q 4^{-j}`, from `‖K_{r,z}‖ ≤ 2η^{-r}` (accepted
`lem_root_placement`), instead of the `η`-uniform strip bound:

* `Sq_Afam_le`: `S_q ≤ 2 T_q x`;  `Cp_Afam_le`: `C_1(A_z) ≤ K x²` with the absolute constant `K = 2(2T_2+2T_1)² + 32(2T_4)²`;
* `moment_sharp`: `‖(S_N(z) − s(z))u^{⊗N}‖² ≤ K x²/N`, `born_variance_sharp` the same for `E|s_N − s|²` under the Born law;
* `tsum_G_sharp`, `concentration_sharp`: `E|G_N(z) − g(z)|² ≤ C/(Nη²)`, `C = 9/2 + 8K`, an absolute constant (a fortiori depending only on `L, κ`),
  for all `z` with `Im z ≥ η₀` (HighHalf), all `N ≥ 1` and unit `u`; the integral form is over the actual Born law
  (`bornMeasure` of the physical basis) of the random Cauchy transform of the DEF-010 empirical measure.
The deterministic inputs are `fz_lower` (injectivity) and `product_error`, as in the printed proof.  No EXT-025 contract is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.RootMeasureConcentrationSharp

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.RootMeasureComplex (sProd GN fz HighHalf)
open QuantumNLS.NormalizedTransfer (productSymbol normalizedTransfer orderedKernel)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.HighMomentsFinal (Sq Cp Zop high_moments_of_normal Sq_nonneg)
open QuantumNLS.HighMomentsTransfer (Afam summable_rankSum CpS CpS_mono)
open QuantumNLS.HighMomentsRank (Xop xlim)
open QuantumNLS.HighMomentsOps (wvec)
open QuantumNLS.RootPlacementBound (lem_root_placement)
open QuantumNLS.RootMeasureTransfer (hasSum_born_variance)
open QuantumNLS.RootMeasureConcentration (norm_GN_le gStar gStar_spec)
open QuantumNLS.RootMeasureExistence (GN_dist_le cauchy_empirical physBasis_eq)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb)
open QuantumNLS.CauchyUniqueness (cauchyTransform)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

instance instCountableMArr (N : ℕ) : Countable (MArr N) := by
  unfold MArr; infer_instance

/-- `T_q = Σ_{j ≥ 0} (j+1)^q 4^{-j}`. -/
def T (q : ℕ) : ℝ := ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ q * (1 / 4 : ℝ) ^ j

theorem summable_T (q : ℕ) : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * (1 / 4 : ℝ) ^ j) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ q * (1 / 4 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one q (by norm_num)
  have h1 := (summable_nat_add_iff 1).2 hg
  refine (h1.mul_left 4).congr (fun j => ?_)
  rw [pow_succ]; ring

/-- The absolute constant of the sharp second-moment bound. -/
def Kc : ℝ := 2 * (2 * T 2 + 2 * T 1) ^ 2 + 32 * (2 * T 4) ^ 2

theorem T_nonneg (q : ℕ) : 0 ≤ T q := tsum_nonneg (fun j => by positivity)

/-- `S_q(A_z) ≤ 2 T_q (κ/η)`. -/
theorem Sq_Afam_le (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) (q : ℕ) :
    Sq (Afam L κ z) q ≤ 2 * T q * (κ / z.im) := by
  have hη : 0 < z.im := by linarith [hz.1]
  set x : ℝ := κ / z.im with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ≤ 1 / 4 := by rw [hx, div_le_iff₀ hη]; linarith [hz.1]
  have hsumA := summable_rankSum (L := L) hκ.le (b := 0) le_rfl z (by simpa using hη.le) q
  have hg : Summable (fun j : ℕ => 2 * x * (((j + 1 : ℕ) : ℝ) ^ q * (1 / 4 : ℝ) ^ j)) :=
    (summable_T q).mul_left _
  unfold Sq
  refine (hsumA.tsum_le_tsum (fun j => ?_) hg).trans (le_of_eq ?_)
  · have hK : ‖orderedKernel L (j + 1) z‖ ≤ 2 * (z.im)⁻¹ ^ (j + 1) :=
      (lem_root_placement u hu (N := j + 1) (by omega) le_rfl z hη).1
    have hA : ‖Afam L κ z (j + 1)‖ ≤ 2 * x * (1 / 4 : ℝ) ^ j := by
      unfold Afam
      calc ‖((κ ^ (j + 1) : ℝ) : ℂ) • orderedKernel L (j + 1) z‖
          ≤ ‖((κ ^ (j + 1) : ℝ) : ℂ)‖ * ‖orderedKernel L (j + 1) z‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ = κ ^ (j + 1) * ‖orderedKernel L (j + 1) z‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hκ.le _)]
        _ ≤ κ ^ (j + 1) * (2 * (z.im)⁻¹ ^ (j + 1)) := mul_le_mul_of_nonneg_left hK (pow_nonneg hκ.le _)
        _ = 2 * x * x ^ j := by rw [hx, div_eq_mul_inv]; ring
        _ ≤ 2 * x * (1 / 4 : ℝ) ^ j := by gcongr
    calc ((j + 1 : ℕ) : ℝ) ^ q * ‖Afam L κ z (j + 1)‖
        ≤ ((j + 1 : ℕ) : ℝ) ^ q * (2 * x * (1 / 4 : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 2 * x * (((j + 1 : ℕ) : ℝ) ^ q * (1 / 4 : ℝ) ^ j) := by ring
  · rw [tsum_mul_left]; unfold T; ring

theorem Cp_Afam_le (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    Cp (Afam L κ z) 1 ≤ Kc * (κ / z.im) ^ 2 := by
  rw [QuantumNLS.HighMomentsTransfer.Cp_eq_CpS]
  refine (CpS_mono (S' := fun q => 2 * T q * (κ / z.im)) (fun q => Sq_nonneg _ q)
    (fun q => Sq_Afam_le hκ u hu hz q) 1).trans (le_of_eq ?_)
  unfold CpS Kc
  norm_num [Finset.sum_range_succ]
  ring

/-- **Sharp second moment**: `‖(S_N(z) − s(z))u^{⊗N}‖² ≤ K (κ/η)²/N`. -/
theorem moment_sharp (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    ‖(normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (wvec N u)‖ ^ 2 ≤
      Kc * (κ / z.im) ^ 2 / N := by
  have hη : 0 < z.im := by linarith [hz.1]
  have e1 : normalizedTransfer L κ N z = Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N :=
    QuantumNLS.NormalizedTransfer.normalizedTransfer_eq_Xop L κ N z
  have e2 : productSymbol L κ u z = xlim u (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) :=
    QuantumNLS.NormalizedTransfer.productSymbol_eq_xlim L κ u z
  have hZ : Zop u (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N =
      normalizedTransfer L κ N z - productSymbol L κ u z •
        (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N) := by
    unfold Zop
    rw [e2, ← e1]
  have hnormal : Commute (ContinuousLinearMap.adjoint (normalizedTransfer L κ N z))
      (normalizedTransfer L κ N z) := by
    have h := QuantumNLS.UnconditionalBetheBasis.normal_deriv_physical (L := L) (κ := κ) hκ hN 0 z
    simpa only [iteratedDeriv_zero] using h
  have hX : Commute (ContinuousLinearMap.adjoint (Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N))
      (Xop (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) N) := by
    rw [← e1]; exact hnormal
  have hsum : ∀ q : ℕ, Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ q * ‖Afam L κ z (j + 1)‖) :=
    fun q => summable_rankSum hκ.le (b := 0) le_rfl z (by simpa using hη.le) q
  have key := high_moments_of_normal u hu (1 + Complex.exp (Complex.I * z * L)) (Afam L κ z) hsum N hN hX
    1 le_rfl
  rw [hZ] at key
  have h2 := key.2
  simp only [pow_one] at h2
  exact h2.trans (div_le_div_of_nonneg_right (Cp_Afam_le hκ u hu hz) (by positivity))

/-- **`E|s_N(z) − s(z;u)|² ≤ K (κ/η)²/N`** under the Born law of the physical basis. -/
theorem born_variance_sharp (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    ∑' m : MArr N, bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) u m *
        ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2 ≤
      Kc * (κ / z.im) ^ 2 / N := by
  have hη : 0 < z.im := by linarith [hz.1]
  rw [(hasSum_born_variance hκ hN u z hη).tsum_eq]
  exact moment_sharp hκ hN u hu hz

/-- The absolute constant `C = 9/2 + 8K` of the printed estimate. -/
def Csharp : ℝ := 9 / 2 + 8 * Kc

theorem Kc_nonneg : 0 ≤ Kc := by
  unfold Kc
  have := T_nonneg 1; have := T_nonneg 2; have := T_nonneg 4
  positivity

/-- **Printed `eq:root-G-concentration`** (series form): `Σ_m born_m |G_N(m;z) − g(z)|² ≤ C/(Nη²)`. -/
theorem tsum_G_sharp (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    ∑' m : MArr N, bornLaw (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) u m *
        ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ^ 2 ≤ Csharp / (N * z.im ^ 2) := by
  have hη : 0 < z.im := by linarith [hz.1]
  obtain ⟨hg1, hg2⟩ := gStar_spec hκ u hu hz
  set Ψ := QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ with hΨ
  set x : ℝ := κ / z.im with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ≤ 1 / 4 := by rw [hx, div_le_iff₀ hη]; linarith [hz.1]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a : ℝ := 3 * x ^ 2 / N with ha
  -- pointwise
  have hpt : ∀ m : MArr N, ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ^ 2 ≤
      8 / κ ^ 2 * (a ^ 2 + ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2) := by
    intro m
    have h := GN_dist_le hκ hz hN (arrRoots L (κ / N) m) hg1 hg2
    have hb0 : 0 ≤ ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ := norm_nonneg _
    have ha0 : 0 ≤ a := by positivity
    have h2 : (κ / 2 * ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖) ^ 2 ≤
        (a + ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h 2
    have h3 : (a + ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖) ^ 2 ≤
        2 * (a ^ 2 + ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2) := by
      nlinarith [sq_nonneg (a - ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖)]
    have hκ2 : 0 < κ ^ 2 := by positivity
    have h4 : κ ^ 2 / 4 * ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ^ 2 ≤
        2 * (a ^ 2 + ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2) := by
      have : (κ / 2 * ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖) ^ 2 =
          κ ^ 2 / 4 * ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ^ 2 := by ring
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ2]
    nlinarith
  have hp1 : HasSum (fun m : MArr N => bornLaw Ψ u m) 1 :=
    QuantumNLS.BetheCoefficientTransform.hasSum_bornLaw_unit Ψ u hu
  have hvar := hasSum_born_variance hκ hN u z hη
  have hvle := moment_sharp hκ hN u hu hz
  have hbd : HasSum (fun m : MArr N => bornLaw Ψ u m * (8 / κ ^ 2 * (a ^ 2 +
      ‖sProd L κ N (arrRoots L (κ / N) m) z - productSymbol L κ u z‖ ^ 2)))
      (8 / κ ^ 2 * (a ^ 2 + (‖(normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (wvec N u)‖ ^ 2))) := by
    have h1 : HasSum (fun m : MArr N => bornLaw Ψ u m * a ^ 2) (a ^ 2) := by
      simpa using hp1.mul_right (a ^ 2)
    have h2 := (h1.add hvar).mul_left (8 / κ ^ 2)
    convert h2 using 1
    funext m; ring
  have hsumG : Summable (fun m : MArr N => bornLaw Ψ u m *
      ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _) (sq_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (hpt m) (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _)) hbd.summable
  refine (hsumG.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_left (hpt m)
    (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _)) hbd.summable).trans ?_
  rw [hbd.tsum_eq]
  -- final arithmetic
  have hκ2 : 0 < κ ^ 2 := by positivity
  have hxsq : x ^ 2 = κ ^ 2 / z.im ^ 2 := by rw [hx, div_pow]
  have ha2 : a ^ 2 ≤ x ^ 2 / N / 16 * 9 := by
    rw [ha, div_pow, mul_pow]
    have : x ^ 2 ≤ 1 / 16 := by nlinarith
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    have : 3 ^ 2 * (x ^ 2) ^ 2 ≤ x ^ 2 / ↑N / 16 * 9 * (N : ℝ) ^ 2 := by
      have hx2 : (x ^ 2) ^ 2 ≤ x ^ 2 * (1 / 16) := by nlinarith [sq_nonneg x]
      have : x ^ 2 / ↑N / 16 * 9 * (N : ℝ) ^ 2 = x ^ 2 * 9 * N / 16 := by field_simp
      rw [this]
      nlinarith [sq_nonneg x]
    exact this
  calc 8 / κ ^ 2 * (a ^ 2 + ‖(normalizedTransfer L κ N z - productSymbol L κ u z •
          (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) (wvec N u)‖ ^ 2)
      ≤ 8 / κ ^ 2 * (x ^ 2 / N / 16 * 9 + Kc * x ^ 2 / N) := by
        gcongr
    _ = Csharp / (N * z.im ^ 2) := by
        unfold Csharp
        rw [hxsq]
        field_simp
        ring

/-- **Printed `eq:root-G-concentration`, integral form** over the actual Born law: `E|G_{ν_N}(z) − g(z)|² ≤ C/(N η²)` for the random Cauchy
transform of the DEF-010 empirical measure, `Im z = η ≥ η₀`. -/
theorem concentration_sharp (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    ∫ m : MArr N, ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) z - gStar L κ hκ u hu z‖ ^ 2
        ∂(bornMeasure (physBasis L hκ N) u hu) ≤ Csharp / (N * z.im ^ 2) := by
  have hη : 0 < z.im := by linarith [hz.1]
  obtain ⟨hg1, hg2⟩ := gStar_spec hκ u hu hz
  rw [physBasis_eq hκ (by omega : 1 ≤ N)]
  set Ψ := QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ with hΨ
  have hf : ∀ m : MArr N, ‖cauchyTransform (empiricalProb L κ N m : Measure ℝ) z - gStar L κ hκ u hu z‖ ^ 2 =
      ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ^ 2 := by
    intro m; rw [cauchy_empirical hN m hη]
  simp_rw [hf]
  have hint : Integrable (fun m : MArr N => ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ^ 2)
      (bornMeasure Ψ u hu) := by
    refine Integrable.of_bound (C := (2 * (z.im)⁻¹) ^ 2) (Measurable.of_discrete.aestronglyMeasurable)
      (Eventually.of_forall fun m => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ‖GN N (arrRoots L (κ / N) m) z - gStar L κ hκ u hu z‖ ≤ 2 * (z.im)⁻¹ := by
      refine (norm_sub_le _ _).trans ?_
      have := norm_GN_le (arrRoots L (κ / N) m) hη
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  rw [integral_countable hint]
  have hmu : ∀ m : MArr N, (bornMeasure Ψ u hu).real {m} = bornLaw Ψ u m := by
    intro m
    rw [measureReal_def, QuantumNLS.EmpiricalRapidity.bornMeasure_singleton,
      ENNReal.toReal_ofReal (QuantumNLS.BetheCoefficientTransform.bornLaw_nonneg _ _ _)]
  simp_rw [hmu, smul_eq_mul]
  exact tsum_G_sharp hκ hN u hu hz

end QuantumNLS.RootMeasureConcentrationSharp

#print axioms QuantumNLS.RootMeasureConcentrationSharp.Sq_Afam_le
#print axioms QuantumNLS.RootMeasureConcentrationSharp.Cp_Afam_le
#print axioms QuantumNLS.RootMeasureConcentrationSharp.moment_sharp
#print axioms QuantumNLS.RootMeasureConcentrationSharp.born_variance_sharp
#print axioms QuantumNLS.RootMeasureConcentrationSharp.tsum_G_sharp
#print axioms QuantumNLS.RootMeasureConcentrationSharp.concentration_sharp
