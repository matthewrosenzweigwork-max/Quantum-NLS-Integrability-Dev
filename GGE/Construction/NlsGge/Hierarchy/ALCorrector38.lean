import NlsGge.Hierarchy.ALFreeFields38

/-!
# AL corrector (D:eq:corrector, v2 l.2252-2259)

The deterministic Fourier multiplier `(D_h u)^(k) = sqrt(a_{h,k}/a_k) û(k)`, `|k| ≤ N`, satisfies
`D_h U_h = P_N U` exactly under the coupling, and `D_h U_h - U_h → 0` almost surely in every
ordinary Sobolev space `H^s`.  (D:eq:ALremaining is excluded.)
-/

set_option autoImplicit false

noncomputable section
namespace NlsGge.AblowitzLadik

open NlsGge.Weights NlsGge.Measure NlsGge.Pilot NlsGge.HierarchyRiccati.Core MeasureTheory Filter
open scoped Topology ENNReal

/-- Multiplier of `D_h`: `sqrt(a_{h,k}/a_k)` for `|k| ≤ N`, `0` otherwise. -/
def alCorrMul38 (c : ℕ → ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  if |k| ≤ (N : ℤ) then Real.sqrt (alRateFree38 c N k / alRateCont38 c k) else 0

/-- Multiplier of `D_h⁻¹` on `P_N`-modes: `sqrt(a_k/a_{h,k})` for `|k| ≤ N`. -/
def alCorrInvMul38 (c : ℕ → ℝ) (N : ℕ) (k : ℤ) : ℝ :=
  if |k| ≤ (N : ℤ) then Real.sqrt (alRateCont38 c k / alRateFree38 c N k) else 0

/-- Fourier coefficients of `D_h u`. -/
def alCorrCoef38 (c : ℕ → ℝ) (N : ℕ) (u : ℤ → ℂ) (k : ℤ) : ℂ :=
  (alCorrMul38 c N k : ℂ) * u k

/-- Fourier coefficients of `D_h⁻¹ u`. -/
def alCorrInvCoef38 (c : ℕ → ℝ) (N : ℕ) (u : ℤ → ℂ) (k : ℤ) : ℂ :=
  (alCorrInvMul38 c N k : ℂ) * u k

/-- Fourier coefficients of `P_N U`. -/
def alPNUCoef38 (c : ℕ → ℝ) (N : ℕ) (g : ℤ → ℂ) (k : ℤ) : ℂ :=
  if |k| ≤ (N : ℤ) then alUCoef38 c g k else 0

/-- `D_h U_h` realized in `H^s`. -/
def alDhUhRealization38 (s : ℝ) (c : ℕ → ℝ) (N : ℕ) (g : ℤ → ℂ) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (alCorrCoef38 c N (alUhCoef38 c N g))

/-- `P_N U` realized in `H^s`. -/
def alPNURealization38 (s : ℝ) (c : ℕ → ℝ) (N : ℕ) (g : ℤ → ℂ) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (alPNUCoef38 c N g)

section Exact

variable {lower upper : ℝ} {c : ℕ → ℝ}

/-- `D_h U_h = P_N U` coefficientwise, given positive lattice rates on the modes `|k| ≤ N`. -/
theorem alCorr_Uh_coef38 (hA : AdmissibleWeight38 lower upper c) (N : ℕ)
    (hpos : ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c N k) (g : ℤ → ℂ) :
    alCorrCoef38 c N (alUhCoef38 c N g) = alPNUCoef38 c N g := by
  funext k
  have hacpos : 0 < alRateCont38 c k := (alRateComp_pos38 hA k).trans_le (alRateComp_le_cont38 hA k)
  by_cases hk : |k| ≤ (N : ℤ)
  · have hh := hpos k hk
    simp only [alCorrCoef38, alCorrMul38, alUhCoef38, alPNUCoef38, alUCoef38, hk, ↓reduceIte]
    rw [Real.sqrt_div hh.le]
    have h1 : (Real.sqrt (alRateFree38 c N k) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hh).ne'
    have h2 : (Real.sqrt (alRateCont38 c k) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hacpos).ne'
    push_cast
    field_simp
  · simp [alCorrCoef38, alCorrMul38, alUhCoef38, alPNUCoef38, hk]

/-- `D_h⁻¹ P_N U = U_h` coefficientwise (so `F_h(U) = f_h(D_h⁻¹ P_N U)` evaluates `f_h` at `U_h`). -/
theorem alCorrInv_PNU_coef38 (hA : AdmissibleWeight38 lower upper c) (N : ℕ)
    (hpos : ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c N k) (g : ℤ → ℂ) :
    alCorrInvCoef38 c N (alPNUCoef38 c N g) = alUhCoef38 c N g := by
  funext k
  have hacpos : 0 < alRateCont38 c k := (alRateComp_pos38 hA k).trans_le (alRateComp_le_cont38 hA k)
  by_cases hk : |k| ≤ (N : ℤ)
  · have hh := hpos k hk
    simp only [alCorrInvCoef38, alCorrInvMul38, alUhCoef38, alPNUCoef38, alUCoef38, hk, ↓reduceIte]
    rw [Real.sqrt_div hacpos.le]
    have h1 : (Real.sqrt (alRateFree38 c N k) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hh).ne'
    have h2 : (Real.sqrt (alRateCont38 c k) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hacpos).ne'
    push_cast
    field_simp
  · simp [alCorrInvCoef38, alCorrInvMul38, alUhCoef38, alPNUCoef38, hk]

/-- The lattice rates are positive on all modes `|k| ≤ N` for large `N`. -/
theorem alRateFree_pos_eventually38 (hA : AdmissibleWeight38 lower upper c) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alRateFree38 c N k := by
  filter_upwards [alRateFree_ge38 hA] with N hN k hk
  exact lt_of_lt_of_le (half_pos (alRateComp_pos38 hA k)) (hN k hk)

/-- The identity `D_h U_h = P_N U` in `H^s`, for all large `N` (for every `g`, `s`). -/
theorem alDhUh_eq_PNU38 (hA : AdmissibleWeight38 lower upper c) (s : ℝ) (g : ℤ → ℂ) :
    ∀ᶠ N : ℕ in atTop, alDhUhRealization38 s c N g = alPNURealization38 s c N g := by
  filter_upwards [alRateFree_pos_eventually38 hA] with N hN
  unfold alDhUhRealization38 alPNURealization38
  rw [alCorr_Uh_coef38 hA N hN g]

end Exact

section Convergence

variable {lower upper : ℝ} {c : ℕ → ℝ}

theorem alU_summable38 (hA : AdmissibleWeight38 lower upper c) (s : ℝ) (g : ℤ → ℂ)
    (hg : Summable (fun k : ℤ => sobolevModeWeight s k * ‖g k‖ ^ 2 / alRateComp38 c k)) :
    Summable (fun k : ℤ => sobolevModeWeight s k * ‖alUCoef38 c g k‖ ^ 2) := by
  have hwpos : ∀ k, 0 < sobolevModeWeight s k :=
    (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight s n)).out
  have hacpos : ∀ k, 0 < alRateCont38 c k :=
    fun k => (alRateComp_pos38 hA k).trans_le (alRateComp_le_cont38 hA k)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hwpos k).le (sq_nonneg _)) (fun k => ?_) hg
  unfold alUCoef38
  rw [coef_norm_sq38 _ _ (hacpos k).le, ← mul_div_assoc]
  exact div_le_div_of_nonneg_left (by have := hwpos k; positivity) (alRateComp_pos38 hA k)
    (alRateComp_le_cont38 hA k)

/-- Deterministic: `P_N U → U` in `H^s` when `U ∈ H^s`. -/
theorem alPNU_tendsto38 (hA : AdmissibleWeight38 lower upper c) (s : ℝ) (g : ℤ → ℂ)
    (hg : Summable (fun k : ℤ => sobolevModeWeight s k * ‖g k‖ ^ 2 / alRateComp38 c k)) :
    Tendsto (fun N : ℕ => alPNURealization38 s c N g) atTop (𝓝 (alURealization38 s c g)) := by
  set w := sobolevModeWeight s with hwdef
  have hwpos : ∀ k, 0 < w k := (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight s n)).out
  have hsumU := alU_summable38 hA s g hg
  have hsumP : ∀ N, Summable (fun k => w k * ‖alPNUCoef38 c N g k‖ ^ 2) := by
    intro N
    apply summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N)
    intro k hk
    have : ¬ |k| ≤ (N : ℤ) := by
      intro h; apply hk; rw [Finset.mem_Icc]; exact abs_le.mp h
    simp [alPNUCoef38, this]
  set F : ℕ → ℤ → ℝ := fun N k => w k * ‖alPNUCoef38 c N g k - alUCoef38 c g k‖ ^ 2 with hF
  have hdom : ∀ N k, ‖F N k‖ ≤ w k * ‖alUCoef38 c g k‖ ^ 2 := by
    intro N k
    rw [Real.norm_of_nonneg (mul_nonneg (hwpos k).le (sq_nonneg _))]
    by_cases hk : |k| ≤ (N : ℤ)
    · simp only [alPNUCoef38, hk, ↓reduceIte, sub_self, norm_zero]
      simpa using mul_nonneg (hwpos k).le (sq_nonneg ‖alUCoef38 c g k‖)
    · simp [alPNUCoef38, hk]
  have hpt : ∀ k, Tendsto (fun N => F N k) atTop (𝓝 0) := by
    intro k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop k.natAbs] with N hN
    have hk : |k| ≤ (N : ℤ) := by
      rw [Int.abs_eq_natAbs]; exact_mod_cast hN
    simp [alPNUCoef38, hk, hF]
  have hT : Tendsto (fun N => ∑' k, F N k) atTop (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := F) (g := fun _ => (0 : ℝ))
      hsumU hpt (Eventually.of_forall hdom)
    simpa using this
  rw [tendsto_iff_dist_tendsto_zero]
  have hd : ∀ N, dist (alPNURealization38 s c N g) (alURealization38 s c g) =
      Real.sqrt (∑' k, F N k) := by
    intro N
    rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _)]
    unfold alPNURealization38 alURealization38
    rw [seqRealization_dist_sq38 w _ _ (hsumP N) hsumU]
  simp_rw [hd]
  simpa using hT.sqrt

/-- D:eq:corrector, deterministic form: if `U ∈ H^s` then `D_h U_h - U_h → 0` in `H^s`. -/
theorem alCorr_tendsto38 (hA : AdmissibleWeight38 lower upper c) (s : ℝ) (g : ℤ → ℂ)
    (hg : Summable (fun k : ℤ => sobolevModeWeight s k * ‖g k‖ ^ 2 / alRateComp38 c k)) :
    Tendsto (fun N : ℕ => alDhUhRealization38 s c N g - alUhRealization38 s c N g) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => alDhUhRealization38 s c N g) atTop
      (𝓝 (alURealization38 s c g)) :=
    (alPNU_tendsto38 hA s g hg).congr' ((alDhUh_eq_PNU38 hA s g).mono fun N h => h.symm)
  have h2 := alFree_sobolev_tendsto38 hA s g hg
  simpa using h1.sub h2

/-- D:eq:corrector: under the coupling by independent standard complex Gaussians `g_k`,
(i) `D_h U_h = P_N U` exactly (coefficientwise, for all large `N`, simultaneously for all `g`);
(ii) almost surely, for every ordinary Sobolev space `H^s`, `D_h U_h - U_h → 0` in `H^s`. -/
theorem alCorrector38 (hA : AdmissibleWeight38 lower upper c) :
    (∀ g : ℤ → ℂ, ∀ᶠ N : ℕ in atTop,
      alCorrCoef38 c N (alUhCoef38 c N g) = alPNUCoef38 c N g) ∧
    (∀ᵐ g ∂alFreeLaw38, ∀ s : ℝ,
      Tendsto (fun N : ℕ => alDhUhRealization38 s c N g - alUhRealization38 s c N g)
        atTop (𝓝 0)) := by
  refine ⟨fun g => ?_, ?_⟩
  · filter_upwards [alRateFree_pos_eventually38 hA] with N hN
    exact alCorr_Uh_coef38 hA N hN g
  · have hall : ∀ᵐ g ∂alFreeLaw38, ∀ r : ℕ,
        Summable (fun k : ℤ => (1 + (k : ℝ) ^ 2) ^ r / alRateComp38 c k * ‖g k‖ ^ 2) :=
      ae_all_iff.2 (fun r => ae_summable_comp38 hA r)
    filter_upwards [hall] with g hg s
    apply alCorr_tendsto38 hA s g
    have hr := hg ⌈s⌉₊
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hr
    · have := alRateComp_pos38 hA k
      have : 0 < sobolevModeWeight s k :=
        (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight s n)).out k
      positivity
    · have hW := alRateComp_pos38 hA k
      have := sobolevModeWeight_le_pow38 s ⌈s⌉₊ (Nat.le_ceil s) k
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this (sq_nonneg _)) hW.le

end Convergence

end NlsGge.AblowitzLadik
