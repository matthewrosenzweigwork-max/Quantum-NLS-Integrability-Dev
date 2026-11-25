import NlsGge.Schur.ActualSchurBallMapJacobian38V1
import NlsGge.Schur.BallChangeOfVariables38V1
import NlsGge.Schur.ActualSchurGapEnergyLower38V1
import NlsGge.Schur.ActualSchurBallConstants38V1
import NlsGge.Schur.ActualSchurBallBridges38V1
import NlsGge.Measure.FourierGaussian

/-!
# NEW-F05 (F:prop:ball): assembly

Helpers, the CONDITIONAL core `actualSchurBallIntegral_conditional38` (hypothesis: the energy
dominates the weighted actions of finite families of high labelled gaps), and later the
unconditional corollary for `fullEnergy38`.
-/

set_option autoImplicit false
noncomputable section
open NlsGge.Analysis NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Measure

namespace NlsGge.Schur

theorem natAbs_le_iff_abs_le38 (n : ℤ) (M : ℕ) : n.natAbs ≤ M ↔ |n| ≤ (M : ℤ) := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast Iff.rfl

/-- A single coordinate is bounded by the plane H¹ norm. -/
theorem plane_coord_le_H1Norm38 (N : ℕ) (z : FourierPlane N) (i : Fin (2 * N + 1)) :
    ‖z i‖ ≤ planeH1Norm38 N z := by
  have h := planeH1Embedding38_norm_sq N z
  have hle : ‖z i‖ ^ 2 ≤ ‖planeH1Embedding38 N z‖ ^ 2 := by
    rw [h]
    calc ‖z i‖ ^ 2 ≤ (1 + (modeIndex N i : ℝ) ^ 2) * ‖z i‖ ^ 2 := by
          have : (0 : ℝ) ≤ (modeIndex N i : ℝ) ^ 2 * ‖z i‖ ^ 2 := by positivity
          nlinarith
      _ ≤ ∑ j : Fin (2 * N + 1), (1 + (modeIndex N j : ℝ) ^ 2) * ‖z j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => (1 + (modeIndex N j : ℝ) ^ 2) * ‖z j‖ ^ 2)
            (fun j _ => by positivity) (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

/-- The plane H¹ ball is open (hence measurable). -/
theorem isOpen_planeH1Ball38 (N : ℕ) (R : ℝ) :
    IsOpen {z : FourierPlane N | planeH1Norm38 N z < R} := by
  have hc : Continuous (fun z : FourierPlane N => planeH1Norm38 N z) :=
    continuous_norm.comp (planeH1Embedding38_continuous N)
  exact isOpen_lt hc continuous_const

/-- Product of the inverse relative losses over high modes. -/
theorem high_rho_inv_prod_le38 (N M : ℕ) (hM1 : 1 ≤ M) (C R : ℝ) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hMR : R ^ 6 ≤ (M : ℝ)) :
    ∏ i ∈ Finset.univ.filter (fun i : Fin (2 * N + 1) => (M : ℤ) < |modeIndex N i|),
        (actualSchurRho38 C R (modeIndex N i))⁻¹ ≤ Real.exp (8 * C) := by
  set s := Finset.univ.filter (fun i : Fin (2 * N + 1) => (M : ℤ) < |modeIndex N i|) with hs
  set f : ℤ → ℝ := fun n => if M < n.natAbs then
      R ^ 3 * |(n : ℝ)| ^ (-(3 / 2) : ℝ) + R ^ 4 / (n : ℝ) ^ 2 else 0 with hf
  obtain ⟨hsum, htail⟩ := rhoTail_real38 R (by linarith) M hM1
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n; simp only [hf]; split_ifs <;> positivity
  have hprod : ∏ i ∈ s, (actualSchurRho38 C R (modeIndex N i))⁻¹ =
      Real.exp (C * ∑ i ∈ s, f (modeIndex N i)) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : M < (modeIndex N i).natAbs := by
      have := (Finset.mem_filter.mp hi).2
      have h2 : ¬ (modeIndex N i).natAbs ≤ M := by
        rw [natAbs_le_iff_abs_le38]; exact not_le.mpr this
      omega
    simp only [actualSchurRho38, hf, if_pos hi', ← Real.exp_neg]
    ring_nf
  rw [hprod]
  apply Real.exp_le_exp.mpr
  have hfin : ∑ i ∈ s, f (modeIndex N i) ≤ ∑' n : ℤ, f n := by
    rw [← Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]
    exact hsum.sum_le_tsum _ (fun n _ => hf0 n)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hR0 : 0 < R := by linarith
  -- `R^3 M^{-1/2} ≤ 1` and `R^4/M ≤ 1`
  have h1 : R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    have hsq : R ^ 3 ≤ Real.sqrt M := by
      rw [show R ^ 3 = Real.sqrt ((R ^ 3) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      apply Real.sqrt_le_sqrt; nlinarith
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hMpos.le,
      ← Real.sqrt_eq_rpow]
    rw [mul_inv_le_iff₀ (Real.sqrt_pos.mpr hMpos)]
    linarith
  have h2 : R ^ 4 / M ≤ 1 := by
    rw [div_le_one hMpos]
    have : R ^ 4 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
    linarith
  calc C * ∑ i ∈ s, f (modeIndex N i) ≤ C * ∑' n : ℤ, f n :=
        mul_le_mul_of_nonneg_left hfin hC
    _ ≤ C * (4 * (R ^ 3 * (M : ℝ) ^ (-1 / 2 : ℝ) + R ^ 4 / M)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa [hf] using htail
    _ ≤ C * (4 * (1 + 1)) := by gcongr
    _ = 8 * C := by ring

/-- The weighted gap action of the labelled gap of `planeField38 N z` at `-n`. -/
def planeGapAction38 (c : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) (n : ℤ) : ℝ :=
  (2 / Real.pi) * ∫ lam in actualGapLowerE02_38 (planeField38 N z) (-n)..
      actualGapUpperE02_38 (planeField38 N z) (-n),
    NlsGge.Weights.weight c (2 * lam) * actualGapHeightE02_38 (planeField38 N z) lam

/-- F:eq:highenergy on the plane, given the per-gap bound (W-F05b) and the conditional
domination hypothesis. -/
theorem ball_highEnergy38 (lo up : ℝ) (Kb Cb : ℝ)
    (hgb : ∀ c : ℕ → ℝ, (∀ j, lo ≤ c j) → (∀ j, c j ≤ up) →
      ∀ R : ℝ, 1 ≤ R → ∀ n : ℤ, Kb * R ^ 3 ≤ |(n : ℝ)| →
      ∀ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)), ‖w‖ ≤ R →
        actualSchurRho38 Cb R n * NlsGge.Weights.weight c (2 * Real.pi * n) *
            ‖actualSchurQn38 R n (w, actualH1Conj38 w)‖ ^ 2 ≤
          (2 / Real.pi) * ∫ lam in
              actualGapLowerE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n)..
              actualGapUpperE02_38 (physicalH1ComplexCarrierToL2Actual22 w) (-n),
            NlsGge.Weights.weight c (2 * lam) *
              actualGapHeightE02_38 (physicalH1ComplexCarrierToL2Actual22 w) lam)
    (c : ℕ → ℝ) (hb : ∀ j, lo ≤ c j) (hu : ∀ j, c j ≤ up)
    (R : ℝ) (hR : 1 ≤ R) (N M : ℕ) (K : ℝ)
    (hMK : ∀ n : ℤ, ¬ n.natAbs ≤ M →
      Kb * R ^ 3 ≤ |(n : ℝ)| ∧ actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| ∧
        K * R ^ 3 ≤ |(n : ℝ)|)
    (E : FourierPlane N → ℝ)
    (hgap : ∀ z, planeH1Norm38 N z < R → ∀ S : Finset ℤ,
      (∀ n ∈ S, K * R ^ 3 ≤ |(n : ℝ)| ∧ |n| ≤ N) →
      ∑ n ∈ S, planeGapAction38 c N z n ≤ E z)
    (z : FourierPlane N) (hz : planeH1Norm38 N z < R) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * N + 1) => (M : ℤ) < |modeIndex N i|),
        actualSchurRho38 Cb R (modeIndex N i) *
          NlsGge.Weights.weight c (2 * Real.pi * (modeIndex N i : ℝ)) *
          ‖actualSchurBallMap38 N M z i‖ ^ 2 ≤ E z := by
  set s := Finset.univ.filter (fun i : Fin (2 * N + 1) => (M : ℤ) < |modeIndex N i|) with hs
  set w := planeH1Embedding38 N z with hw
  have hwR : ‖w‖ ≤ R := hz.le
  have hw2 : ‖actualH1Conj38 w‖ ≤ R := by rw [actualH1Conj38_norm]; exact hwR
  have hhigh : ∀ i ∈ s, ¬ (modeIndex N i).natAbs ≤ M := by
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    rw [natAbs_le_iff_abs_le38]; exact not_le.mpr this
  have hterm : ∀ i ∈ s, actualSchurRho38 Cb R (modeIndex N i) *
      NlsGge.Weights.weight c (2 * Real.pi * (modeIndex N i : ℝ)) *
      ‖actualSchurBallMap38 N M z i‖ ^ 2 ≤ planeGapAction38 c N z (modeIndex N i) := by
    intro i hi
    obtain ⟨h1, h2, -⟩ := hMK (modeIndex N i) (hhigh i hi)
    rw [actualSchurBallMap38_high N M z i (hhigh i hi),
      actualSchurQnCanonical38_eq R hR (modeIndex N i) h2 (w, actualH1Conj38 w) hwR hw2]
    exact hgb c hb hu R hR (modeIndex N i) h1 w hwR
  calc _ ≤ ∑ i ∈ s, planeGapAction38 c N z (modeIndex N i) := Finset.sum_le_sum hterm
    _ = ∑ n ∈ s.image (modeIndex N), planeGapAction38 c N z n :=
        (Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)).symm
    _ ≤ E z := by
        apply hgap z hz
        intro n hn
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
        refine ⟨(hMK _ (hhigh i hi)).2.2, ?_⟩
        exact abs_le.mpr ⟨(modeIndex_bounds N i).1, (modeIndex_bounds N i).2⟩

/-- Real ratio identity: low disks and high Gaussian planes against `∏ π/a`. -/
theorem ball_ratio_identity38 (N M : ℕ) (R : ℝ) (a ρ : Fin (2 * N + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ∀ i, 0 < ρ i) :
    (∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), Real.pi * R ^ 2) *
      (∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), Real.pi / (ρ i * a i)) =
    (∏ i, Real.pi / a i) *
      ((∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), R ^ 2 * a i) *
        ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), (ρ i)⁻¹) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
    (p := fun i : Fin (2 * N + 1) => |modeIndex N i| ≤ (M : ℤ)) (f := fun i => Real.pi / a i)
  have hnot : (Finset.univ.filter (fun i : Fin (2 * N + 1) => ¬ |modeIndex N i| ≤ (M : ℤ))) =
      Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|) := by
    ext i; simp [not_le]
  rw [hnot] at hsplit
  rw [← hsplit]
  have hl : ∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), Real.pi * R ^ 2 =
      (∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), Real.pi / a i) *
        ∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), R ^ 2 * a i := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp [(ha i).ne']
  have hh : ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), Real.pi / (ρ i * a i) =
      (∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), Real.pi / a i) *
        ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), (ρ i)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    field_simp [(ha i).ne', (hρ i).ne']
  rw [hl, hh]
  ring

/-- **NEW-F05, F:prop:ball — CONDITIONAL core.**  Constants `C, K` depend only on the
coefficient bounds `lo, up`.  For every admitted `c`, `R ≥ 1`, `N`, and every nonnegative
measurable `E` on the plane that dominates, on the open H¹ ball of radius `R`, the weighted
actions of every finite family of labelled high gaps (`K R³ ≤ |n| ≤ N`), the Lebesgue
integral of `e^{-E}` over the ball is at most `∏ (π/a_n) · exp(C (1+R)^9)`.
The free parameter `K0` only lets a caller force the threshold constant `K ≥ K0`.
The domination hypothesis is discharged for `E = fullEnergy38` by the trace formula
(`actualSchurBallIntegral_fullEnergy38`). -/
theorem actualSchurBallIntegral_conditional38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up)
    (K0 : ℝ) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ K0 ≤ K ∧
    ∀ c : ℕ → ℝ, (∀ j, lo ≤ c j) → (∀ j, c j ≤ up) →
    ∀ R : ℝ, 1 ≤ R → ∀ N : ℕ, ∀ E : FourierPlane N → ℝ, Measurable E → (∀ z, 0 ≤ E z) →
    (∀ z, planeH1Norm38 N z < R → ∀ S : Finset ℤ,
      (∀ n ∈ S, K * R ^ 3 ≤ |(n : ℝ)| ∧ |n| ≤ N) →
      ∑ n ∈ S, planeGapAction38 c N z n ≤ E z) →
    ∫⁻ z in {z | planeH1Norm38 N z < R}, ENNReal.ofReal (Real.exp (-E z)) ∂planeVolume N ≤
      (∏ i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi / fullWeightRate c (modeIndex N i))) *
        ENNReal.ofReal (Real.exp (C * (1 + R) ^ 9)) := by
  obtain ⟨Kb, Cb, hKb, hCb, hgb⟩ := actualSchurGapEnergyLower38V1 lo up hl hlu
  set Aj := actualSchurJacobianMConstant38 with hAj
  have hAj1 : 1 ≤ Aj := actualSchurJacobianMConstant38_ge_one
  have hT0 : 0 ≤ actualSchurCenterThresholdConstant38 :=
    (actualSchurShiftedRootsConstant38_ge).2.2.2
  set A : ℝ := Aj + 64 * actualSchurCenterThresholdConstant38 + Kb + |K0| + 1 with hA
  have hK0 : 0 ≤ |K0| := abs_nonneg K0
  have hA1 : 1 ≤ A := by linarith
  set L : ℝ := ballLowConstant38 A up with hL
  have hL0 : 0 ≤ L := ballLowConstant38_nonneg A up (by linarith)
  refine ⟨L + 8 * Cb + 1, A, by positivity, by linarith, by linarith [le_abs_self K0], ?_⟩
  intro c hb hu R hR N E hEm hE0 hgap
  have hR0 : 0 < R := by linarith
  have hR6 : 1 ≤ R ^ 6 := one_le_pow₀ hR
  have hR36 : R ^ 3 ≤ R ^ 6 := pow_le_pow_right₀ hR (by norm_num)
  set M : ℕ := ⌈A * R ^ 6⌉₊ with hMdef
  have hMge : A * R ^ 6 ≤ (M : ℝ) := Nat.le_ceil _
  have hMle : (M : ℝ) ≤ A * R ^ 6 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := le_trans (by nlinarith) hMge
    exact_mod_cast this
  have hR9 : (1 : ℝ) ≤ (1 + R) ^ 9 := one_le_pow₀ (by linarith)
  set B := {z : FourierPlane N | planeH1Norm38 N z < R} with hB
  have hBm : MeasurableSet B := (isOpen_planeH1Ball38 N R).measurableSet
  set a : Fin (2 * N + 1) → ℝ := fun i => fullWeightRate c (modeIndex N i) with ha
  have hapos : ∀ i, 0 < a i := fun i =>
    fullWeightRate_pos lo up c hl hb hu _
  have hcoord : ∀ z ∈ B, ∀ i, ‖z i‖ < R := fun z hz i =>
    lt_of_le_of_lt (plane_coord_le_H1Norm38 N z i) hz
  -- the low product bound, for any family of at most 2M+1 modes with |n| ≤ M
  have hlow : ∀ t : Finset (Fin (2 * N + 1)), (∀ i ∈ t, |modeIndex N i| ≤ (M : ℤ)) →
      ∏ i ∈ t, R ^ 2 * a i ≤ Real.exp (L * (1 + R) ^ 9) := by
    intro t ht
    have hcard : (t.card : ℝ) ≤ 2 * M + 1 := by
      have hsub : t.image (modeIndex N) ⊆ Finset.Icc (-(M : ℤ)) M := by
        intro n hn
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_Icc.mpr (abs_le.mp (ht i hi))
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (modeIndex_injective N), Int.card_Icc] at h1
      have h2 : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
      rw [h2] at h1
      exact_mod_cast h1
    have := ballLowProduct_le38 lo up c ⟨hl, hlu, fun j => ⟨hb j, hu j⟩⟩ A R hA1 hR M hMle t
      (modeIndex N) (fun i hi => ht i hi) hcard
    simpa [ha, fullWeightRate] using this
  have hPall0 : 0 ≤ ∏ i, Real.pi / a i := Finset.prod_nonneg fun i _ => by
    have := hapos i; positivity
  have hRHS : (∏ i : Fin (2 * N + 1), ENNReal.ofReal (Real.pi / fullWeightRate c (modeIndex N i))) *
      ENNReal.ofReal (Real.exp ((L + 8 * Cb + 1) * (1 + R) ^ 9)) =
      ENNReal.ofReal ((∏ i, Real.pi / a i) * Real.exp ((L + 8 * Cb + 1) * (1 + R) ^ 9)) := by
    rw [ENNReal.ofReal_mul hPall0, ENNReal.ofReal_prod_of_nonneg (fun i _ => by
      have := hapos i; positivity)]
  rw [hRHS]
  by_cases hNM : N ≤ M
  · -- no coordinate change
    have hv := ballVolumeBound38 N B hBm E hE0 R hR0 hcoord
    refine le_trans hv ?_
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hall : ∀ i : Fin (2 * N + 1), |modeIndex N i| ≤ (M : ℤ) := by
      intro i
      have := modeIndex_bounds N i
      exact abs_le.mpr ⟨by omega, by omega⟩
    have hprod := hlow Finset.univ (fun i _ => hall i)
    have hid : ∏ _i : Fin (2 * N + 1), Real.pi * R ^ 2 =
        (∏ i, Real.pi / a i) * ∏ i, R ^ 2 * a i := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      field_simp [(hapos i).ne']
    rw [hid]
    apply mul_le_mul_of_nonneg_left _ hPall0
    refine le_trans hprod (Real.exp_le_exp.mpr ?_)
    nlinarith [hCb]
  · -- coordinate change by the Schur map
    have hNM : M < N := Nat.lt_of_not_le hNM
    have hK4 : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ (M : ℝ) := by
      have : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 =
          64 * actualSchurCenterThresholdConstant38 * R ^ 3 := by ring
      rw [this]
      nlinarith
    have hAjM : Aj * R ^ 6 ≤ (M : ℝ) := by nlinarith
    set ρ : Fin (2 * N + 1) → ℝ := fun i => actualSchurRho38 Cb R (modeIndex N i) with hρdef
    have hρpos : ∀ i, 0 < ρ i := fun i => Real.exp_pos _
    have hρ1 : ∀ i, ρ i ≤ 1 := by
      intro i
      simp only [hρdef, actualSchurRho38]
      rw [Real.exp_le_one_iff]
      have : 0 ≤ R ^ 3 * |((modeIndex N i : ℤ) : ℝ)| ^ (-(3 / 2) : ℝ) +
          R ^ 4 / ((modeIndex N i : ℤ) : ℝ) ^ 2 := by positivity
      nlinarith
    have hMK : ∀ n : ℤ, ¬ n.natAbs ≤ M →
        Kb * R ^ 3 ≤ |(n : ℝ)| ∧ actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| ∧
          A * R ^ 3 ≤ |(n : ℝ)| := by
      intro n hn
      have h1 := natAbs_gt_abs38 M n hn
      have hAR : A * R ^ 3 ≤ |(n : ℝ)| := by nlinarith
      refine ⟨by nlinarith, by nlinarith, hAR⟩
    have hE : ∀ z ∈ B, ∑ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|),
        ρ i * a i * ‖actualSchurBallMap38 N M z i‖ ^ 2 ≤ E z := by
      intro z hz
      have := ball_highEnergy38 lo up Kb Cb hgb c hb hu R hR N M A hMK E hgap z hz
      simpa [hρdef, ha, fullWeightRate] using this
    have hlowΨ : ∀ z ∈ B, ∀ i, |modeIndex N i| ≤ (M : ℤ) →
        actualSchurBallMap38 N M z i = z i ∧ ‖z i‖ < R := by
      intro z hz i hi
      exact ⟨actualSchurBallMap38_low N M z i ((natAbs_le_iff_abs_le38 _ _).mpr hi),
        hcoord z hz i⟩
    have hcv := ballChangeOfVariables38 N M hNM.le B hBm (actualSchurBallMap38 N M)
      (fun z => fderiv ℝ (actualSchurBallMap38 N M) z) a ρ hapos hρpos hρ1 E hEm hE0 R hR0
      (actualSchurBallMap38_injOn N M R hR hAjM hK4)
      (fun z hz => actualSchurBallMap38_hasFDerivWithinAt N M R hR hK4 z hz)
      (fun z hz => actualSchurBallMap38_abs_det_ge N M R hR hAjM hK4 z hz)
      hlowΨ hE
    refine le_trans hcv ?_
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by
        have := hapos i; have := hρpos i; positivity),
      ← ENNReal.ofReal_mul (by positivity),
      show (2 : ENNReal) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [ball_ratio_identity38 N M R a ρ hapos hρpos]
    have hlowP := hlow (Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)))
      (fun i hi => (Finset.mem_filter.mp hi).2)
    have hhighP := high_rho_inv_prod_le38 N M hM1 Cb R hCb.le hR (by nlinarith)
    have hlowP0 : 0 ≤ ∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)),
        R ^ 2 * a i := Finset.prod_nonneg fun i _ => by have := hapos i; positivity
    have h2 : (2 : ℝ) ≤ Real.exp ((1 + R) ^ 9) := by
      have := Real.add_one_le_exp ((1 + R) ^ 9); linarith
    have hP2 : (∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), R ^ 2 * a i) *
        ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), (ρ i)⁻¹ ≤
        Real.exp (L * (1 + R) ^ 9) * Real.exp (8 * Cb) :=
      mul_le_mul hlowP hhighP
        (Finset.prod_nonneg fun i _ => by have := hρpos i; positivity) (Real.exp_pos _).le
    have hP20 : 0 ≤ (∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), R ^ 2 * a i) *
        ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), (ρ i)⁻¹ :=
      mul_nonneg hlowP0 (Finset.prod_nonneg fun i _ => by have := hρpos i; positivity)
    have hexp : Real.exp ((1 + R) ^ 9) * (Real.exp (L * (1 + R) ^ 9) * Real.exp (8 * Cb)) ≤
        Real.exp ((L + 8 * Cb + 1) * (1 + R) ^ 9) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : 8 * Cb ≤ 8 * Cb * (1 + R) ^ 9 := by nlinarith
      nlinarith
    calc 2 * ((∏ i, Real.pi / a i) *
          ((∏ i ∈ Finset.univ.filter (fun i => |modeIndex N i| ≤ (M : ℤ)), R ^ 2 * a i) *
            ∏ i ∈ Finset.univ.filter (fun i => (M : ℤ) < |modeIndex N i|), (ρ i)⁻¹))
        ≤ Real.exp ((1 + R) ^ 9) * ((∏ i, Real.pi / a i) *
            (Real.exp (L * (1 + R) ^ 9) * Real.exp (8 * Cb))) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_left hP2 hPall0) (mul_nonneg hPall0 hP20)
            (Real.exp_pos _).le
      _ = (∏ i, Real.pi / a i) *
          (Real.exp ((1 + R) ^ 9) * (Real.exp (L * (1 + R) ^ 9) * Real.exp (8 * Cb))) := by ring
      _ ≤ (∏ i, Real.pi / a i) * Real.exp ((L + 8 * Cb + 1) * (1 + R) ^ 9) :=
          mul_le_mul_of_nonneg_left hexp hPall0

end NlsGge.Schur
