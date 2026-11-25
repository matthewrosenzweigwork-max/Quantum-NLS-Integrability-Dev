import Mathlib
import QuantumNLS.PeriodReconstruction
import QuantumNLS.CauchyLimitCriterion
import QuantumNLS.RootMeasureComplex
import QuantumNLS.RootMeasureConcentration

/-!
# PROP-009 `lem:B4-finite-probes` (`spectral_calculus.tex:139`): detection by finitely many bounded transfers

**Routing (no EXT-025 contract).** The source proof uses vague compactness of bounded measures and its mass-preserving weak upgrade
(contract `FIN-EXT025-GP-10`).  Here it is replaced, as for `R-09E1EAE9`, by the deterministic Cauchy criterion
`CauchyLimitCriterion.tendsto_of_cauchy` (mathlib's Prokhorov theorem for TIGHT sequences, tightness from the tail inequality and no
loss of mass, identification by `CauchyUniqueness.cauchy_ext_dense`: convergence of Cauchy transforms on a dense set of one horizontal line
and at the points `iY_j`, `Y_j → ∞`).  The "finitely many probes" statement is proved by the source's contradiction argument:
a countable family `zp` of probe points (a dense subset of the line `Im z = η₀` and the points `i(η₀ + j)`, all in `HighHalf`) and
violators for the first `k` probes with tolerance `1/(k+1)`.  The inputs consumed read-only are PROP-004 `label_block_uniform`
(block identification and root separation on a weak neighbourhood of `μ`) and PROP-006 `log_reconstruction` (the `O(N⁻²)` remainder along a
weakly convergent sequence); the quantitative probe step is `RootMeasureComplex.product_error` and `fz_lower` (Steps 1-2 of `thm:root-measure`,
the source's `eq:B4-high-transfer-expansion`, `eq:B4-high-inverse-bound`).

Statement (`finite_probes`): for the actual indexed scalar measure `S` with regular cutpoints `x₋ < x₊` and the PROP-006 label brackets,
there are `δ > 0`, finitely many probe points `z_j` in the high upper half-plane, `ε > 0`, `N₀` and `C` such that for every `N ≥ N₀` and
every on-shell Bethe configuration `B` with `max_j |s_N(z_j) − s(z_j)| < ε`:
* the corrected label block is identified exactly with the `δ`-separated cuts (`BlockConclusion`),
* all roots have distance `≥ min δ h` from the fixed contour `Γ = ∂([x₋,x₊]×[−h,h])`,
* `‖remf (z)‖ ≤ C N⁻²` on `Γ` (the reconstruction remainder, `eq:B3-log-reconstruction`), with one constant `C`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace QuantumNLS.Prop009FiniteProbes

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.RootMeasureComplex (fz HighHalf sProd GN product_error fz_lower)

/-! ### Elementary lemmas -/

theorem cauchy_emp {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    QuantumNLS.CauchyUniqueness.cauchyTransform (emp q) z = GN N q z := by
  unfold QuantumNLS.CauchyUniqueness.cauchyTransform GN
  rw [integral_emp_complex]
  push_cast; rfl

theorem mul_div_div_aux (a b c d : ℂ) : a * (b / c) / d = a * b / (c * d) := by
  rw [← mul_div_assoc, div_div]

theorem sNf_eq_sProd {L κ : ℝ} {N : ℕ} (q : Fin N → ℝ) (z : ℂ) :
    sNf L (κ / N) q z = QuantumNLS.RootMeasureComplex.sProd L κ N q z := by
  unfold sNf ANf ef QuantumNLS.RootMeasureComplex.sProd
  congr 1
  · refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    rw [mul_div_div_aux]
  · rw [show Complex.exp (I * L * z) = Complex.exp (I * z * L) by congr 1; ring]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    push_cast
    rw [mul_neg, neg_div, mul_div_div_aux, ← sub_eq_add_neg]

theorem sf_eq_fz (L κ : ℝ) (G : ℂ → ℂ) (z : ℂ) : sf L κ G z = fz L κ z (G z) := by
  unfold sf Af ef fz
  rw [div_eq_mul_inv, ← Complex.exp_neg, show I * (L : ℂ) * z = I * z * L by ring]

theorem norm_cauchy_le_im (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {z : ℂ} (hz : 0 < z.im) :
    ‖QuantumNLS.CauchyUniqueness.cauchyTransform ρ z‖ ≤ (z.im)⁻¹ := by
  unfold QuantumNLS.CauchyUniqueness.cauchyTransform
  have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun t : ℝ => ((z - (t : ℂ))⁻¹ : ℂ))
    (C := (z.im)⁻¹) (Eventually.of_forall fun t => QuantumNLS.CauchyLimitCriterion.norm_kernel_le hz t)
  rwa [probReal_univ, mul_one] at this

/-- The probe step: for `z` in the high half-plane, closeness of the transfer eigenvalue to the scalar symbol forces closeness of the
empirical Cauchy transform to `G_μ` (`eq:B4-high-transfer-expansion` + `eq:B4-high-inverse-bound`). -/
theorem GN_close {L κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : HighHalf L κ z) {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ‖GN N q z - EmpiricalRapidity.cauchyTransform ρ z‖ ≤
      2 / κ * (‖sNf L (κ / N) q z - sf L κ (EmpiricalRapidity.cauchyTransform ρ) z‖ + 3 * (κ / z.im) ^ 2 / N) := by
  have hη : 0 < z.im := by linarith [hz.1]
  have h1 : ‖GN N q z‖ ≤ (z.im)⁻¹ := QuantumNLS.RootMeasureConcentration.norm_GN_le q hη
  have h2 : ‖EmpiricalRapidity.cauchyTransform ρ z‖ ≤ (z.im)⁻¹ := norm_cauchy_le_im ρ hη
  have h3 := fz_lower (L := L) hκ hz h1 h2
  have h4 := product_error (L := L) hκ hz hN q
  have h5 : ‖fz L κ z (GN N q z) - fz L κ z (EmpiricalRapidity.cauchyTransform ρ z)‖ ≤
      ‖sNf L (κ / N) q z - sf L κ (EmpiricalRapidity.cauchyTransform ρ) z‖ + 3 * (κ / z.im) ^ 2 / N := by
    have e1 : fz L κ z (GN N q z) - fz L κ z (EmpiricalRapidity.cauchyTransform ρ z) =
        (fz L κ z (GN N q z) - sProd L κ N q z) +
          (sNf L (κ / N) q z - sf L κ (EmpiricalRapidity.cauchyTransform ρ) z) := by
      rw [sNf_eq_sProd, sf_eq_fz]; ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_sub_rev (fz L κ z (GN N q z))]
    linarith
  have : κ / 2 * ‖GN N q z - EmpiricalRapidity.cauchyTransform ρ z‖ ≤ _ := h3.trans h5
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  nlinarith

/-- No loss of mass for a probability measure along `Y_j = η₀ + j`. -/
theorem mass_tendsto (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {η₀ : ℝ} (hη : 0 < η₀) :
    Tendsto (fun j : ℕ => 1 + (η₀ + j) *
      (EmpiricalRapidity.cauchyTransform ρ (Complex.I * ((η₀ + j : ℝ) : ℂ))).im) atTop (𝓝 0) := by
  have hY : ∀ j : ℕ, 0 < η₀ + j := fun j => by positivity
  have key : ∀ j : ℕ, 1 + (η₀ + j) *
      (EmpiricalRapidity.cauchyTransform ρ (Complex.I * ((η₀ + j : ℝ) : ℂ))).im =
      ∫ s : ℝ, s ^ 2 / ((η₀ + j) ^ 2 + s ^ 2) ∂ρ := by
    intro j
    have him := QuantumNLS.CauchyUniqueness.im_cauchy ρ (hY j) 0
    have e : ((0 : ℝ) : ℂ) + ((η₀ + j : ℝ) : ℂ) * Complex.I = Complex.I * ((η₀ + j : ℝ) : ℂ) := by
      push_cast; ring
    rw [e] at him
    have hc : EmpiricalRapidity.cauchyTransform ρ (Complex.I * ((η₀ + j : ℝ) : ℂ)) =
        QuantumNLS.CauchyUniqueness.cauchyTransform ρ (Complex.I * ((η₀ + j : ℝ) : ℂ)) := rfl
    rw [hc, him]
    unfold QuantumNLS.CauchyUniqueness.poisson QuantumNLS.CauchyUniqueness.pk
    have hint : Integrable (fun s : ℝ => (η₀ + j) / ((η₀ + j) ^ 2 + (0 - s) ^ 2)) ρ := by
      refine (integrable_const (η₀ + j)⁻¹).mono' ?_ (Eventually.of_forall fun s => ?_)
      · exact (continuous_const.div (by fun_prop) (fun s => by positivity)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
        have := hY j
        nlinarith [sq_nonneg (0 - s), mul_inv_cancel₀ this.ne']
    have : ∀ s : ℝ, 1 - (η₀ + j) * ((η₀ + j) / ((η₀ + j) ^ 2 + (0 - s) ^ 2)) =
        s ^ 2 / ((η₀ + j) ^ 2 + s ^ 2) := by
      intro s
      have : (0 : ℝ) < (η₀ + j) ^ 2 + s ^ 2 := by positivity
      field_simp
      ring
    calc 1 + (η₀ + j) * (-∫ s : ℝ, (η₀ + j) / ((η₀ + j) ^ 2 + (0 - s) ^ 2) ∂ρ)
        = ∫ s : ℝ, (1 - (η₀ + j) * ((η₀ + j) / ((η₀ + j) ^ 2 + (0 - s) ^ 2))) ∂ρ := by
          rw [integral_sub (integrable_const _) (hint.const_mul _), integral_const_mul]
          simp; ring
      _ = _ := by simp_rw [this]
  simp_rw [key]
  have hF : ∀ j : ℕ, AEStronglyMeasurable (fun s : ℝ => s ^ 2 / ((η₀ + j) ^ 2 + s ^ 2)) ρ := fun j =>
    ((continuous_pow 2).div (by fun_prop) (fun s => by have := hY j; positivity)).aestronglyMeasurable
  have hb : ∀ j : ℕ, ∀ᵐ s ∂ρ, ‖s ^ 2 / ((η₀ + j) ^ 2 + s ^ 2)‖ ≤ 1 := fun j => Eventually.of_forall fun s => by
    have := hY j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by positivity)]
    nlinarith [sq_nonneg (η₀ + j)]
  have hlim : ∀ᵐ s ∂ρ, Tendsto (fun j : ℕ => s ^ 2 / ((η₀ + j) ^ 2 + s ^ 2)) atTop (𝓝 0) :=
    Eventually.of_forall fun s => by
      have h1 : Tendsto (fun j : ℕ => (η₀ + j) ^ 2 + s ^ 2) atTop atTop := by
        refine tendsto_atTop_add_const_right _ _ ?_
        exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
      exact h1.const_div_atTop (s ^ 2)
  have := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hF (integrable_const _) hb hlim
  simpa using this

/-! ### The probe family and the main statement -/

/-- Height of the probe line: large enough for `HighHalf`. -/
def eta0' (L κ : ℝ) : ℝ := max (4 * κ) (Real.log 16 / L)

theorem eta0'_pos {L κ : ℝ} (hκ : 0 < κ) : 0 < eta0' L κ :=
  lt_of_lt_of_le (by positivity) (le_max_left _ _)

theorem highHalf_of {L κ : ℝ} (hL : 0 < L) {y : ℝ} (hy : eta0' L κ ≤ y) :
    ∀ {w : ℂ}, w.im = y → HighHalf L κ w := by
  intro w hw
  refine ⟨by rw [hw]; exact (le_max_left _ _).trans hy, ?_⟩
  rw [hw]
  have : Real.log 16 / L ≤ y := (le_max_right _ _).trans hy
  rwa [div_le_iff₀ hL, mul_comm] at this

/-- Probe points: the dense subset `q_k + iη₀` of the line `Im z = η₀` (even indices) and `i(η₀ + j)` (odd indices). -/
def zp (L κ : ℝ) (q : ℕ → ℝ) (i : ℕ) : ℂ :=
  if i % 2 = 0 then (q (i / 2) : ℂ) + (eta0' L κ : ℂ) * Complex.I
  else Complex.I * ((eta0' L κ + (i / 2 : ℕ) : ℝ) : ℂ)

theorem zp_even (L κ : ℝ) (q : ℕ → ℝ) (k : ℕ) :
    zp L κ q (2 * k) = (q k : ℂ) + (eta0' L κ : ℂ) * Complex.I := by
  have h1 : (2 * k) % 2 = 0 := by omega
  have h2 : (2 * k) / 2 = k := by omega
  simp [zp, h1, h2]

theorem zp_odd (L κ : ℝ) (q : ℕ → ℝ) (j : ℕ) :
    zp L κ q (2 * j + 1) = Complex.I * ((eta0' L κ + (j : ℕ) : ℝ) : ℂ) := by
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [zp, h1, h2]

theorem zp_high {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (q : ℕ → ℝ) (i : ℕ) : HighHalf L κ (zp L κ q i) := by
  unfold zp
  split_ifs
  · exact highHalf_of hL le_rfl (by simp)
  · refine highHalf_of hL (y := eta0' L κ + (i / 2 : ℕ)) (by have : (0 : ℝ) ≤ ((i / 2 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith) ?_
    simp

/-- The conclusion of PROP-009 for one configuration. -/
def ProbeConcl {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) (n : ℤ) (xm xp h δ C : ℝ) {N : ℕ}
    (B : OnShellBethe L κ N) : Prop :=
  BlockConclusion B n xm xp δ ∧ (∀ w ∈ Gam xm xp h, ∀ j, min δ h ≤ ‖w - ((B.q j : ℝ) : ℂ)‖) ∧
    ∀ w ∈ Gam xm xp h,
      ‖remf κ L (fun _ => N) (fun _ => B.q) (EmpiricalRapidity.cauchyTransform S.μ) (0, w)‖ ≤
        C * ((N : ℝ)⁻¹) ^ 2

/-- **PROP-009 `lem:B4-finite-probes`.** -/
theorem finite_probes {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {n : ℤ} {xm xp h : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ δ > 0, ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, HighHalf L κ (z j)) ∧ ∃ ε > 0, ∃ N₀ : ℕ, ∃ C : ℝ,
      ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
        (∀ j, ‖sNf L (κ / N) B.q (z j) - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (z j)‖ < ε) →
        ProbeConcl S n xm xp h δ C B := by
  have hL := S.hL
  have hκ := S.hκ
  haveI : IsProbabilityMeasure S.μ := S.isProb
  set μ : ProbabilityMeasure ℝ := ⟨S.μ, S.isProb⟩ with hμdef
  have hμ : (μ : Measure ℝ) = S.μ := rfl
  obtain ⟨δ, hδ, U, hU, N₁, hN₁⟩ := label_block_uniform S hμ hxm hxp hlt h1 h2 h3 h4
  refine ⟨δ, hδ, ?_⟩
  by_contra hcon
  set qd : ℕ → ℝ := TopologicalSpace.denseSeq ℝ with hqd
  have hzp := zp_high hL hκ qd
  have key : ∀ k : ℕ, ∃ (N : ℕ) (_ : 0 < N) (_ : k + 1 ≤ N) (B : OnShellBethe L κ N),
      (∀ j : Fin k, ‖sNf L (κ / N) B.q (zp L κ qd j) - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (zp L κ qd j)‖ < 1 / ((k : ℝ) + 1)) ∧
      ¬ ProbeConcl S n xm xp h δ (k : ℝ) B := by
    intro k
    by_contra hk
    apply hcon
    refine ⟨k, fun j => zp L κ qd j, fun j => hzp j, 1 / ((k : ℝ) + 1), by positivity, k + 1, k, ?_⟩
    intro N hN hNge B hB
    by_contra hC
    exact hk ⟨N, hN, hNge, B, hB, hC⟩
  choose N hNpos hNge B hB hnot using key
  have hNtop : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun k => by have := hNge k; simp only [id]; omega) tendsto_id
  -- convergence of the empirical Cauchy transforms at every probe point
  have hconvG : ∀ i : ℕ, Tendsto (fun k => GN (N k) (B k).q (zp L κ qd i)) atTop (𝓝 (EmpiricalRapidity.cauchyTransform S.μ (zp L κ qd i))) := by
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hx : 0 ≤ 3 * (κ / (zp L κ qd i).im) ^ 2 := by positivity
    have hlim : Tendsto (fun k : ℕ => 2 / κ * (1 / ((k : ℝ) + 1) + 3 * (κ / (zp L κ qd i).im) ^ 2 / (N k : ℝ)))
        atTop (𝓝 (2 / κ * (0 + 0))) := by
      refine Tendsto.const_mul _ (Tendsto.add ?_ ?_)
      · exact tendsto_one_div_add_atTop_nhds_zero_nat
      · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hNtop)
    refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) ?_ (by simpa using hlim)
    filter_upwards [eventually_gt_atTop i] with k hk
    have h5 := GN_close (L := L) hκ (hzp i) (hNpos k) (B k).q S.μ
    have h6 := (hB k ⟨i, hk⟩).le
    refine h5.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h7 : ‖sNf L (κ / (N k : ℝ)) (B k).q (zp L κ qd i) -
        sf L κ (EmpiricalRapidity.cauchyTransform S.μ) (zp L κ qd i)‖ ≤ 1 / ((k : ℝ) + 1) := h6
    rw [one_div] at h7
    linarith
  have hρ : ∀ k, ((rootP (B k) (hNpos k) : ProbabilityMeasure ℝ) : Measure ℝ) = emp (B k).q := fun k => rfl
  have hcauchy : ∀ k z, QuantumNLS.CauchyUniqueness.cauchyTransform
      ((rootP (B k) (hNpos k) : ProbabilityMeasure ℝ) : Measure ℝ) z = GN (N k) (B k).q z := by
    intro k z; rw [hρ]; exact cauchy_emp _ _
  have hη : 0 < eta0' L κ := eta0'_pos hκ
  have hconv : Tendsto (fun k => rootP (B k) (hNpos k)) atTop (𝓝 μ) := by
    refine QuantumNLS.CauchyLimitCriterion.tendsto_of_cauchy (η₀ := eta0' L κ) (q := qd)
      (g := QuantumNLS.CauchyUniqueness.cauchyTransform S.μ) (Y := fun j : ℕ => eta0' L κ + j) hη
      (TopologicalSpace.denseRange_denseSeq ℝ) (fun k => rootP (B k) (hNpos k))
      (fun j => by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) μ (fun k => rfl) ?_ ?_ ?_
    · exact mass_tendsto S.μ hη
    · intro j
      have := hconvG (2 * j + 1)
      rw [zp_odd] at this
      simp_rw [hcauchy]
      exact this
    · intro k0
      have := hconvG (2 * k0)
      rw [zp_even] at this
      simp_rw [hcauchy]
      exact this
  -- the sequence theorems
  have hblock : ∀ᶠ k in atTop, BlockConclusion (B k) n xm xp δ := by
    filter_upwards [hconv.eventually (mem_of_superset hU subset_rfl),
      hNtop.eventually (eventually_ge_atTop N₁)] with k hk1 hk2
    exact hN₁ (N k) (hNpos k) hk2 (B k) hk1
  obtain ⟨C₁, hC₁⟩ := log_reconstruction S (μ := μ) hμ hconv hNtop hxm hxp hlt hh h1 h2 h3 h4
  obtain ⟨k, hk1, hk2, hk3⟩ := (hblock.and (hC₁.and (eventually_ge_atTop ⌈C₁⌉₊))).exists
  apply hnot k
  refine ⟨hk1, fun w hw j => Gam_dist hh (hk1 j).2.1 (hk1 j).2.2 hw, fun w hw => ?_⟩
  have hC : C₁ ≤ (k : ℝ) := (Nat.le_ceil C₁).trans (by exact_mod_cast hk3)
  exact (hk2 w hw).trans (mul_le_mul_of_nonneg_right hC (sq_nonneg _))

end QuantumNLS.Prop009FiniteProbes

#print axioms QuantumNLS.Prop009FiniteProbes.GN_close
#print axioms QuantumNLS.Prop009FiniteProbes.mass_tendsto
#print axioms QuantumNLS.Prop009FiniteProbes.finite_probes
