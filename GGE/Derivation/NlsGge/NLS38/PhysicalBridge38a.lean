import NlsGge.NLS38.ClassicalSolution38
import NlsGge.NLS38.Functionals38

/-! # GWP piece A10b (part a): Parseval on `ℓ¹`, `Q₀`, `Q₂` of v2 l.60-62

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A10b (review note N3).  Public entry point is
`NlsGge.NLS38.PhysicalBridge38`; this file holds the Fourier pairing on `ℓ¹` and the three functional
identities

* `mass_eq_integral`  : `Q₀(u) = ∫ |u|²`,
* `quart_eq_integral` : `∫ |u|⁴ = ‖u*u‖²_{ℓ²}`,
* `ham_eq_Q2`         : `K + ∫|u|⁴ = ∫ (|u'|² + |u|⁴)` (v2 `Q₂`).

Method: the Parseval identity is proved directly on `ℓ¹` from `serU_mul`, `serU_conj`:
`|serU f|² = serU (f * f̃)` and `∫₀¹ serU g = g 0`, so no `Lp` bookkeeping is needed.
Every `tsum` identity is preceded by an `IsL1` hypothesis (AGENTS.md).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Filter Topology
open scoped ComplexConjugate

/-! ## The exponentials -/

theorem continuous_eT (n : ℤ) : Continuous (eT n) := by
  unfold eT; fun_prop

theorem eT_zero_arg (n : ℤ) : eT n 0 = 1 := by simp [eT]

theorem eT_zero_left (θ : ℝ) : eT 0 θ = 1 := by simp [eT]

theorem eT_one_arg (n : ℤ) : eT n 1 = 1 := by
  have := eT_periodic n 0
  simpa [eT_zero_arg] using this

theorem integral_eT (n : ℤ) : ∫ θ in (0 : ℝ)..1, eT n θ = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    simp [eT_zero_left]
  · have hc : (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, hpi, Complex.I_ne_zero]
    have hd : ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => eT n y / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))) (eT n θ) θ := by
      intro θ _
      have := (hasDerivAt_eT n θ).div_const (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))
      simpa [mul_div_assoc, div_self hc] using this
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_eT n).intervalIntegrable _ _)]
    simp [eT_zero_arg, eT_one_arg, hn]

/-! ## Fourier pairing on `ℓ¹` -/

theorem hasSum_integral_serU_mul {f : ℤ → ℂ} (hf : IsL1 f) {ψ : ℝ → ℂ} (hψ : Continuous ψ) :
    HasSum (fun n => f n * ∫ θ in (0 : ℝ)..1, eT n θ * ψ θ)
      (∫ θ in (0 : ℝ)..1, serU f θ * ψ θ) := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hψ.continuousOn
  have hs : ∀ θ, HasSum (fun n => f n * (eT n θ * ψ θ)) (serU f θ * ψ θ) := fun θ => by
    have := (summable_serU_term hf θ).hasSum.mul_right (ψ θ)
    rw [serU_def]
    simpa [mul_assoc] using this
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
    (F := fun n θ => f n * (eT n θ * ψ θ)) (f := fun θ => serU f θ * ψ θ)
    (fun n _ => ‖f n‖ * C)
    (fun n => (by have : Continuous fun θ => f n * (eT n θ * ψ θ) := by
                    have := continuous_eT n; fun_prop
                  exact this.aestronglyMeasurable))
    (fun n => Filter.Eventually.of_forall fun θ hθ => by
      rw [norm_mul, norm_mul, norm_eT, one_mul]
      exact mul_le_mul_of_nonneg_left (hC θ (by
        rw [Set.uIcc_of_le zero_le_one]; rw [Set.uIoc_of_le zero_le_one] at hθ
        exact ⟨hθ.1.le, hθ.2⟩)) (norm_nonneg _))
    (Filter.Eventually.of_forall fun θ _ => (hf.mul_right C))
    (by simp)
    (Filter.Eventually.of_forall fun θ _ => hs θ)
  have e : (fun n => ∫ θ in (0 : ℝ)..1, f n * (eT n θ * ψ θ)) =
      fun n => f n * ∫ θ in (0 : ℝ)..1, eT n θ * ψ θ :=
    funext fun n => intervalIntegral.integral_const_mul _ _
  rw [e] at key
  exact key

/-- The `m`-th Fourier coefficient of `serU f`, `f ∈ ℓ¹`: `f m = ∫₀¹ serU f θ e^{-2πimθ} dθ`. -/
theorem integral_serU_mul_eT_neg {f : ℤ → ℂ} (hf : IsL1 f) (m : ℤ) :
    ∫ θ in (0 : ℝ)..1, serU f θ * eT (-m) θ = f m := by
  have h := hasSum_integral_serU_mul hf (continuous_eT (-m))
  have e : ∀ n : ℤ, ∫ θ in (0 : ℝ)..1, eT n θ * eT (-m) θ = if n = m then 1 else 0 := by
    intro n
    have : ∀ θ, eT n θ * eT (-m) θ = eT (n + -m) θ := fun θ => (eT_add _ _ θ).symm
    simp_rw [this]
    rw [integral_eT]
    simp [sub_eq_zero, ← sub_eq_add_neg]
  rw [← h.tsum_eq]
  simp_rw [e]
  exact (tsum_eq_single m (fun n hn => by simp [hn])).trans (by simp)

theorem integral_serU {f : ℤ → ℂ} (hf : IsL1 f) : ∫ θ in (0 : ℝ)..1, serU f θ = f 0 := by
  have := integral_serU_mul_eT_neg hf 0
  simpa [eT_zero_left] using this

/-- Parseval on `ℓ¹`: `∫₀¹ |serU f|² = ∑ |fₙ|²`. -/
theorem integral_norm_sq_serU {f : ℤ → ℂ} (hf : IsL1 f) :
    ∫ θ in (0 : ℝ)..1, ‖serU f θ‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 := by
  have hc : IsL1 (cstar f) := (isL1_cstar_iff f).2 hf
  have hfc := (isL1_conv hf hc).1
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have e : ∀ θ : ℝ, (((‖serU f θ‖ ^ 2 : ℝ)) : ℂ) = serU (conv f (cstar f)) θ := by
    intro θ
    rw [← serU_mul hf hc, ← serU_conj, Complex.mul_conj']
    push_cast; ring
  simp_rw [e]
  rw [integral_serU hfc, Complex.ofReal_tsum]
  unfold conv
  refine tsum_congr fun a => ?_
  simp only [cstar, zero_sub, neg_neg, Complex.ofReal_pow]
  rw [Complex.mul_conj']

/-- `Q₀`: `mass u = ∫ |u|²` (Parseval, `h¹ ⊂ ℓ¹`). -/
theorem mass_eq_integral (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    mass x = ∫ θ in (0 : ℝ)..1, ‖serU x θ‖ ^ 2 :=
  (integral_norm_sq_serU (isL1_of_hn_one x hx).1).symm

theorem integral_norm_pow_four_serU {f : ℤ → ℂ} (hf : IsL1 f) :
    ∫ θ in (0 : ℝ)..1, ‖serU f θ‖ ^ 4 = ∑' n, ‖conv f f n‖ ^ 2 := by
  have h := integral_norm_sq_serU (isL1_conv hf hf).1
  rw [← h]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← serU_mul hf hf, norm_mul]
  ring

/-- `∫ |u|⁴ = quart u` (`serU_mul` + Parseval). -/
theorem quart_eq_integral (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    quart x = ∫ θ in (0 : ℝ)..1, ‖serU x θ‖ ^ 4 :=
  (integral_norm_pow_four_serU (isL1_of_hn_one x hx).1).symm

theorem isL1_dx_of_h2 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((2 : ℕ) : ℝ)) : IsL1 (dx x) :=
  (isL1_of_hn_one (dx x) (dx_mem 1 (by simpa using hx))).1

/-- v2 `Q₂ = ∫ (|u'|² + |u|⁴)` (l.60-62): `ham u = K(u) + ∫|u|⁴`, for `u ∈ h²`. -/
theorem ham_eq_Q2 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((2 : ℕ) : ℝ)) {Ux : ℝ → ℂ}
    (hUx : ∀ θ, HasDerivAt (serU x) (Ux θ) θ) :
    ham x = ∫ θ in (0 : ℝ)..1, (‖Ux θ‖ ^ 2 + ‖serU x θ‖ ^ 4) := by
  have hx1 : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) := mem_h1_of_mem_nat 2 (by norm_num) hx
  have hL := (isL1_of_hn_one x hx1).1
  have hd := isL1_dx_of_h2 hx
  have hU : ∀ θ, Ux θ = serU (dx x) θ := fun θ =>
    (hUx θ).unique (hasDerivAt_serU hL hd θ)
  have hc1 : Continuous fun θ => ‖Ux θ‖ ^ 2 := by
    have : Ux = serU (dx x) := funext hU
    rw [this]; have := continuous_serU hd; fun_prop
  have hc2 : Continuous fun θ => ‖serU x θ‖ ^ 4 := by
    have := continuous_serU hL; fun_prop
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  have k1 : kin x = ∫ θ in (0 : ℝ)..1, ‖Ux θ‖ ^ 2 := by
    simp_rw [hU]
    rw [integral_norm_sq_serU hd]
    unfold kin
    refine tsum_congr fun n => ?_
    rw [norm_dx, disp]
    have : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
    calc (2 * Real.pi * (n : ℝ)) ^ 2 * ‖x n‖ ^ 2 = (2 * Real.pi) ^ 2 * ((n : ℝ) ^ 2) * ‖x n‖ ^ 2 := by ring
      _ = _ := by rw [← this]; ring
  rw [ham_def, k1, quart_eq_integral x hx1]

end NlsGge.NLS38
