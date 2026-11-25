import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA5Coeff

/-! # Track A, step A5 (generic, part 3): stronger-space membership of the Taylor coefficients,
with factorial-geometric growth

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

At a center `v0 ∈ h^{r+σ}` of a real-analytic, rotation-equivariant `g : h^r → h^r`:

* `exists_setup`: Cauchy constants `C, ρ` at `ι v0` and an angle `δ ∈ (0, π]` with
  `‖S_θ ι v0 - ι v0‖ ≤ ρ` on `(0, δ]` (strong continuity of the rotation group);
* `coeff_mem_and_norm_le`: `y = D^k g(ι v0)[ι h_1, …, ι h_k]` lies in `h^{r+σ}` and its
  `h^{r+σ}`-norm is at most `coeffBound … k · ∏ ‖h_i‖_{h^{r+σ}}`;
* `coeffBound_le`: `coeffBound … k ≤ K · k! · (k+1)² · ρ^{-k}` with `K` independent of `k`.

These are the real-variable replacements of Pro's "Cauchy's estimate along complex lines" and
"monotone weighted sums prove membership and the same bound". -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ENNReal Nat

namespace NlsGge.ALLS.TransA

local instance carrierCompleteSpaceA5M (r : ℝ) : CompleteSpace (SobolevCarrier38 r) :=
  inferInstanceAs (CompleteSpace (SobolevHilbert r))

/-- The quantity `Q_k` of `diffSemi_coeff_le`. -/
def coeffQ (σ C ρ δ : ℝ) (v0n An : ℝ) (k : ℕ) : ℝ :=
  (k + 1) * kernelUp σ * ((C * (k + 1)! * (ρ⁻¹) ^ (k + 1)) ^ 2 * v0n ^ 2 + k * An ^ 2) +
    4 * An ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ))

/-- The coefficient bound `M_k = sqrt(‖A_k‖² + kernelLow⁻¹ Q_k)`. -/
def coeffBound (σ C ρ δ : ℝ) (v0n An : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (An ^ 2 + (kernelLow σ)⁻¹ * coeffQ σ C ρ δ v0n An k)

theorem coeffQ_nonneg {σ C ρ δ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hδ0 : 0 < δ) (v0n An : ℝ)
    (k : ℕ) : 0 ≤ coeffQ σ C ρ δ v0n An k := by
  unfold coeffQ
  have := kernelUp_pos hσ0 hσ1
  have := Real.rpow_nonneg hδ0.le (-(2 * σ))
  positivity

/-- Setup at a center. -/
theorem exists_setup {r σ : ℝ} (hrs : r ≤ r + σ)
    {g : SobolevCarrier38 r → SobolevCarrier38 r} (han : AnalyticOnNhd ℝ g Set.univ)
    (v0 : SobolevCarrier38 (r + σ)) :
    ∃ C ρ δ : ℝ, 0 < C ∧ 0 < ρ ∧ 0 < δ ∧ δ ≤ Real.pi ∧
      (∀ (k : ℕ) (y : SobolevCarrier38 r), ‖y‖ ≤ ρ →
        ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0 + y)‖ ≤ C * k ! * (ρ⁻¹) ^ k) ∧
      (∀ θ ∈ Ioc 0 δ, ‖rotC38 r θ (carrierIncl38 hrs v0) - carrierIncl38 hrs v0‖ ≤ ρ) := by
  obtain ⟨C, ρ, hC, hρ, hb⟩ := exists_iteratedFDeriv_bound (han (carrierIncl38 hrs v0) trivial)
  have hcont := (continuous_rotC38_apply r (carrierIncl38 hrs v0)).continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ', hδ', hball⟩ := hcont ρ hρ
  refine ⟨C, ρ, min (δ' / 2) Real.pi, hC, hρ, lt_min (by linarith) Real.pi_pos, min_le_right _ _,
    hb, fun θ hθ => ?_⟩
  have hθ' : dist θ 0 < δ' := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hθ.1]
    exact lt_of_le_of_lt (hθ.2.trans (min_le_left _ _)) (by linarith)
  have := hball hθ'
  have h0 : rotC38 r 0 (carrierIncl38 hrs v0) = carrierIncl38 hrs v0 := by
    apply carrierExt38; rw [rotC38_coe, rotSeq38_zero]
  rw [h0, dist_eq_norm] at this
  exact this.le

/-- **Coefficient membership and bound.** -/
theorem coeff_mem_and_norm_le {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hrs : r ≤ r + σ)
    {g : SobolevCarrier38 r → SobolevCarrier38 r} (han : AnalyticOnNhd ℝ g Set.univ)
    (hcomm : ∀ (θ : ℝ) (x : SobolevCarrier38 r), g (rotC38 r θ x) = rotC38 r θ (g x))
    (v0 : SobolevCarrier38 (r + σ)) {C ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hb : ∀ (k : ℕ) (y : SobolevCarrier38 r), ‖y‖ ≤ ρ →
      ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0 + y)‖ ≤ C * k ! * (ρ⁻¹) ^ k)
    (hδ : ∀ θ ∈ Ioc 0 δ, ‖rotC38 r θ (carrierIncl38 hrs v0) - carrierIncl38 hrs v0‖ ≤ ρ)
    (k : ℕ) (h : Fin k → SobolevCarrier38 (r + σ)) :
    ∃ hmem : carrierCoe38 r (iteratedFDeriv ℝ k g (carrierIncl38 hrs v0)
        (fun i => carrierIncl38 hrs (h i))) ∈ seqSobolev38 (r + σ),
      ‖carrierMk38 (r + σ) _ hmem‖ ≤
        coeffBound σ C ρ δ ‖v0‖ ‖iteratedFDeriv ℝ k g (carrierIncl38 hrs v0)‖ k * ∏ i, ‖h i‖ := by
  set A := iteratedFDeriv ℝ k g (carrierIncl38 hrs v0) with hA
  set y := A (fun i => carrierIncl38 hrs (h i)) with hy
  set P := ∏ i, ‖h i‖ with hP
  set Q := coeffQ σ C ρ δ ‖v0‖ ‖A‖ k with hQ
  have hQ0 : 0 ≤ Q := coeffQ_nonneg hσ0 hσ1 hδ0 _ _ k
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => norm_nonneg _
  have hD : diffSemi r σ y ≤ ENNReal.ofReal (P ^ 2 * Q) :=
    diffSemi_coeff_le hσ0 hσ1 hrs han hcomm v0 hρ hδ0 hδπ hb hδ k h
  have hfin : diffSemi r σ y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
  have hmem := mem_of_diffSemi_ne_top hσ0 hσ1 y hfin
  refine ⟨hmem, ?_⟩
  have hkl := kernelLow_pos σ
  have hN := norm_sq_le_of_diffSemi hσ0 hσ1 y hmem
  have hyA : ‖y‖ ≤ ‖A‖ * P := A.le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_carrierIncl38_le hrs _))
    (norm_nonneg _))
  have hsq : ‖carrierMk38 (r + σ) (carrierCoe38 r y) hmem‖ ^ 2 ≤
      (coeffBound σ C ρ δ ‖v0‖ ‖A‖ k * P) ^ 2 := by
    have h1 : ENNReal.ofReal (‖carrierMk38 (r + σ) (carrierCoe38 r y) hmem‖ ^ 2) ≤
        ENNReal.ofReal (‖y‖ ^ 2 + (kernelLow σ)⁻¹ * (P ^ 2 * Q)) := by
      refine hN.trans ?_
      rw [ENNReal.ofReal_add (sq_nonneg _) (by positivity), ENNReal.ofReal_mul (by positivity)]
      gcongr
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    refine h2.trans ?_
    rw [mul_pow, coeffBound, Real.sq_sqrt (by positivity)]
    have : ‖y‖ ^ 2 ≤ (‖A‖ * P) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyA 2
    nlinarith
  have hB0 : 0 ≤ coeffBound σ C ρ δ ‖v0‖ ‖A‖ k * P :=
    mul_nonneg (Real.sqrt_nonneg _) hP0
  exact (sq_le_sq₀ (norm_nonneg _) hB0).1 hsq

/-- **Growth of the coefficient bound**: `M_k ≤ K · k! · (k+1)² · ρ^{-k}`. -/
theorem coeffBound_le {σ C ρ δ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hδ0 : 0 < δ) (v0n : ℝ) (hv0 : 0 ≤ v0n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : ℕ) (An : ℝ), 0 ≤ An → An ≤ C * k ! * (ρ⁻¹) ^ k →
      coeffBound σ C ρ δ v0n An k ≤ K * k ! * ((k : ℝ) + 1) ^ 2 * (ρ⁻¹) ^ k := by
  set κ := kernelUp σ
  set D := δ ^ (-(2 * σ)) / (2 * σ)
  have hκ : 0 < κ := kernelUp_pos hσ0 hσ1
  have hD : 0 ≤ D := by have := Real.rpow_nonneg hδ0.le (-(2 * σ)); positivity
  have hkl := kernelLow_pos σ
  set K0 := κ * (v0n ^ 2 * (ρ⁻¹) ^ 2 + 1) + 4 * D with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨C * Real.sqrt (1 + (kernelLow σ)⁻¹ * K0), by positivity, fun k An hA0 hA => ?_⟩
  set a := C * k ! * (ρ⁻¹) ^ k with ha
  have ha0 : 0 ≤ a := by positivity
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hL : C * (k + 1)! * (ρ⁻¹) ^ (k + 1) = a * ((k + 1) * ρ⁻¹) := by
    rw [ha, Nat.factorial_succ, pow_succ]; push_cast; ring
  -- Q_k ≤ a² (k+1)³ K0
  have hQ : coeffQ σ C ρ δ v0n An k ≤ a ^ 2 * ((k : ℝ) + 1) ^ 3 * K0 := by
    unfold coeffQ
    rw [hL]
    have hA2 : An ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hA0 hA 2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e1 : ((k : ℝ) + 1) * κ * ((a * ((k + 1) * ρ⁻¹)) ^ 2 * v0n ^ 2 + k * An ^ 2) ≤
        ((k : ℝ) + 1) * κ * ((a * ((k + 1) * ρ⁻¹)) ^ 2 * v0n ^ 2 + (k + 1) ^ 2 * a ^ 2) := by
      gcongr
      all_goals nlinarith
    have e2 : 4 * An ^ 2 * D ≤ 4 * a ^ 2 * D := by gcongr
    have e3 : ((k : ℝ) + 1) * κ * ((a * ((k + 1) * ρ⁻¹)) ^ 2 * v0n ^ 2 + (k + 1) ^ 2 * a ^ 2) +
        4 * a ^ 2 * D ≤ a ^ 2 * ((k : ℝ) + 1) ^ 3 * K0 := by
      rw [hK0]
      have hk3 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 3 := one_le_pow₀ hk1
      have : 4 * a ^ 2 * D ≤ a ^ 2 * ((k : ℝ) + 1) ^ 3 * (4 * D) := by
        have := mul_le_mul_of_nonneg_left hk3 (by positivity : (0 : ℝ) ≤ 4 * a ^ 2 * D)
        nlinarith
      nlinarith [this]
    linarith
  have hM2 : An ^ 2 + (kernelLow σ)⁻¹ * coeffQ σ C ρ δ v0n An k ≤
      (a * ((k : ℝ) + 1) ^ 2) ^ 2 * (1 + (kernelLow σ)⁻¹ * K0) := by
    have hA2 : An ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hA0 hA 2
    have hk4 : ((k : ℝ) + 1) ^ 3 ≤ ((k : ℝ) + 1) ^ 4 := pow_le_pow_right₀ hk1 (by norm_num)
    have hk4' : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := one_le_pow₀ hk1
    have hinv : 0 ≤ (kernelLow σ)⁻¹ := inv_nonneg.2 hkl.le
    have h1 : (kernelLow σ)⁻¹ * coeffQ σ C ρ δ v0n An k ≤
        (kernelLow σ)⁻¹ * (a ^ 2 * ((k : ℝ) + 1) ^ 4 * K0) := by
      gcongr
      refine hQ.trans ?_
      gcongr
    have h2 : An ^ 2 ≤ a ^ 2 * ((k : ℝ) + 1) ^ 4 := by
      calc An ^ 2 ≤ a ^ 2 := hA2
        _ ≤ a ^ 2 * ((k : ℝ) + 1) ^ 4 := le_mul_of_one_le_right (sq_nonneg _) hk4'
    calc An ^ 2 + (kernelLow σ)⁻¹ * coeffQ σ C ρ δ v0n An k
        ≤ a ^ 2 * ((k : ℝ) + 1) ^ 4 + (kernelLow σ)⁻¹ * (a ^ 2 * ((k : ℝ) + 1) ^ 4 * K0) :=
          add_le_add h2 h1
      _ = (a * ((k : ℝ) + 1) ^ 2) ^ 2 * (1 + (kernelLow σ)⁻¹ * K0) := by ring
  unfold coeffBound
  calc Real.sqrt (An ^ 2 + (kernelLow σ)⁻¹ * coeffQ σ C ρ δ v0n An k)
      ≤ Real.sqrt ((a * ((k : ℝ) + 1) ^ 2) ^ 2 * (1 + (kernelLow σ)⁻¹ * K0)) :=
        Real.sqrt_le_sqrt hM2
    _ = a * ((k : ℝ) + 1) ^ 2 * Real.sqrt (1 + (kernelLow σ)⁻¹ * K0) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ = C * Real.sqrt (1 + (kernelLow σ)⁻¹ * K0) * k ! * ((k : ℝ) + 1) ^ 2 * (ρ⁻¹) ^ k := by
        rw [ha]; ring

end NlsGge.ALLS.TransA
