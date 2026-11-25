import Mathlib
import QuantumNLS.RootDiscriminantBound

/-!
# R-7E0532E7: continuity of `z ↦ M(L,z)` and of `t ↦ Δ_u(t)` (Gronwall)

For continuous `u`, `κ ≥ 0`, `L ≥ 0`, `R ≥ 0` there is `C` with
`‖M(L,z) - M(L,z')‖ ≤ C ‖z - z'‖` for all complex `‖z‖, ‖z'‖ ≤ R` (`lipschitz_transfer`).  Hence `z ↦ M(L,z)`, `z ↦ Δ_u(z)`
and the real discriminant `t ↦ Δ_u(t)` are continuous (`continuous_discriminant`, `continuous_discReal`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open ComplexConjugate MeasureTheory Filter Topology Set
open scoped Matrix NNReal
open QuantumNLS.SpatialTransfer QuantumNLS.LinearFundamental QuantumNLS.RootDiscriminant
  QuantumNLS.RootDiscriminantBound

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.RootDiscriminantContinuity

variable (κ : ℝ) (u : ℝ → ℂ)

theorem norm_balCoef_le (z : ℂ) (x : ℝ) : ‖balCoef κ u z x‖ ≤ ‖z‖ / 2 + Real.sqrt κ * ‖u x‖ := by
  have hs' : |Real.sqrt κ| = Real.sqrt κ := abs_of_nonneg (Real.sqrt_nonneg κ)
  refine norm_le_of_row_sums _ (by positivity) (fun i => ?_)
  fin_cases i <;> simp [balCoef, coef, hs'] <;> linarith [norm_nonneg z, norm_nonneg (u x)]

theorem norm_balCoef_sub (z z' : ℂ) (x : ℝ) : ‖balCoef κ u z x - balCoef κ u z' x‖ ≤ ‖z - z'‖ / 2 := by
  have e : balCoef κ u z x - balCoef κ u z' x =
      !![-(Complex.I * (z - z')) / 2, 0; 0, Complex.I * (z - z') / 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [balCoef, coef] <;> ring
  rw [e]
  refine norm_le_of_row_sums _ (by positivity) (fun i => ?_)
  fin_cases i <;> simp


/-- Gronwall for `Mat2`-valued `C¹` functions on `[0, L]`. -/
theorem gronwall_mat2 {f f' : ℝ → Mat2} {δ K ε L : ℝ} (hd : ∀ x, HasDerivAt f (f' x) x)
    (h0 : ‖f 0‖ ≤ δ) (hb : ∀ x ∈ Ico 0 L, ‖f' x‖ ≤ K * ‖f x‖ + ε) :
    ∀ x ∈ Icc 0 L, ‖f x‖ ≤ gronwallBound δ K ε (x - 0) :=
  norm_le_gronwallBound_of_norm_deriv_right_le
    (continuous_iff_continuousAt.2 (fun x => (hd x).continuousAt)).continuousOn
    (fun x _ => (hd x).hasDerivWithinAt) h0 hb

/-- **`z ↦ M(L,z)` is continuous** (Gronwall; continuous `u`, `κ ≥ 0`). -/
theorem continuousAt_transfer {u : ℝ → ℂ} (hu : Continuous u) {L : ℝ} (hL : 0 ≤ L) (z0 : ℂ) :
    ContinuousAt (fun z : ℂ => spatialTransfer κ u z L) z0 := by
  obtain ⟨Ku, hKu⟩ : ∃ Ku, ∀ x ∈ Icc (0 : ℝ) L, ‖u x‖ ≤ Ku :=
    (isCompact_Icc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn hu.continuousOn
  set R : ℝ := ‖z0‖ + 1 with hR
  set K : ℝ := max 1 (R / 2 + Real.sqrt κ * Ku) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hAK : ∀ z : ℂ, ‖z‖ ≤ R → ∀ x ∈ Icc (0 : ℝ) L, ‖balCoef κ u z x‖ ≤ K := by
    intro z hz x hx
    refine (norm_balCoef_le κ u z x).trans ?_
    refine le_trans ?_ (le_max_right _ _)
    have := mul_le_mul_of_nonneg_left (hKu x hx) (Real.sqrt_nonneg κ)
    linarith
  have hMb : ∀ z : ℂ, ‖z‖ ≤ R → ∀ x ∈ Icc (0 : ℝ) L, ‖spatialTransfer κ u z x‖ ≤ Real.exp (K * L) := by
    intro z hz x hx
    have hM := spatialTransfer_spec' κ hu z
    have := gronwall_mat2 (δ := 1) (K := K) (ε := 0) (L := L) (f := spatialTransfer κ u z)
      (f' := fun y => balCoef κ u z y * spatialTransfer κ u z y) hM.2
      (by rw [hM.1]; exact norm_one_mat2_le)
      (fun y hy => by
        calc ‖balCoef κ u z y * spatialTransfer κ u z y‖
            ≤ ‖balCoef κ u z y‖ * ‖spatialTransfer κ u z y‖ := norm_mul_le _ _
          _ ≤ K * ‖spatialTransfer κ u z y‖ :=
            mul_le_mul_of_nonneg_right (hAK z hz y ⟨hy.1, hy.2.le⟩) (norm_nonneg _)
          _ = K * ‖spatialTransfer κ u z y‖ + 0 := by ring) x hx
    rw [gronwallBound_ε0, sub_zero, one_mul] at this
    exact this.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx.2 (by linarith)))
  set G : ℂ → ℝ := fun z => gronwallBound 0 K (‖z - z0‖ / 2 * Real.exp (K * L)) L with hG
  have hGc : Continuous G := by
    have h1 : Continuous fun z : ℂ => ‖z - z0‖ / 2 * Real.exp (K * L) := by fun_prop
    exact (gronwallBound_continuous_ε 0 K L).comp h1
  have hG0 : G z0 = 0 := by
    simp only [hG, sub_self, norm_zero, zero_div, zero_mul]
    simpa using gronwallBound_ε0_δ0 K L
  have hbound : ∀ᶠ z in 𝓝 z0, ‖spatialTransfer κ u z L - spatialTransfer κ u z0 L‖ ≤ G z := by
    filter_upwards [Metric.ball_mem_nhds z0 one_pos] with z hzb
    have hz : ‖z - z0‖ < 1 := by simpa [dist_eq_norm] using hzb
    have hzR : ‖z‖ ≤ R := by
      have := norm_le_norm_add_norm_sub' z z0
      linarith [norm_sub_rev z z0]
    have hMz := spatialTransfer_spec' κ hu z
    have hMz0 := spatialTransfer_spec' κ hu z0
    have hz0R : ‖z0‖ ≤ R := by rw [hR]; linarith
    have hD : ∀ x, HasDerivAt (fun y => spatialTransfer κ u z y - spatialTransfer κ u z0 y)
        (balCoef κ u z x * spatialTransfer κ u z x - balCoef κ u z0 x * spatialTransfer κ u z0 x) x :=
      fun x => (hMz.2 x).sub (hMz0.2 x)
    have := gronwall_mat2 (δ := 0) (K := K) (ε := ‖z - z0‖ / 2 * Real.exp (K * L)) (L := L)
      (f := fun y => spatialTransfer κ u z y - spatialTransfer κ u z0 y) hD
      (by simp [hMz.1, hMz0.1]) (fun x hx => by
        have hxI : x ∈ Icc (0 : ℝ) L := ⟨hx.1, hx.2.le⟩
        have e : balCoef κ u z x * spatialTransfer κ u z x - balCoef κ u z0 x * spatialTransfer κ u z0 x =
            balCoef κ u z x * (spatialTransfer κ u z x - spatialTransfer κ u z0 x) +
              (balCoef κ u z x - balCoef κ u z0 x) * spatialTransfer κ u z0 x := by
          rw [mul_sub, sub_mul]; abel
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hAK z hzR x hxI) (norm_nonneg _))
        · refine (norm_mul_le _ _).trans ?_
          exact mul_le_mul (norm_balCoef_sub κ u z z0 x) (hMb z0 hz0R x hxI) (norm_nonneg _) (by positivity)) L
        ⟨hL, le_rfl⟩
    simpa [hG] using this
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  simpa [hG0] using hGc.tendsto z0

theorem continuous_discriminant (L : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (hL : 0 ≤ L) :
    Continuous (discriminant L κ u) := by
  refine continuous_iff_continuousAt.2 fun z0 => ?_
  have h := continuousAt_transfer κ hu hL z0
  have htr : Continuous (Matrix.trace : Mat2 → ℂ) := by
    have : (Matrix.trace : Mat2 → ℂ) = fun m => m 0 0 + m 1 1 := funext Matrix.trace_fin_two
    rw [this]
    exact (continuous_id.matrix_elem 0 0).add (continuous_id.matrix_elem 1 1)
  exact htr.continuousAt.comp h

theorem continuous_discReal (L : ℝ) {u : ℝ → ℂ} (hu : Continuous u) (hL : 0 ≤ L) :
    Continuous (discReal L κ u) := by
  unfold discReal
  exact Complex.continuous_re.comp ((continuous_discriminant κ L hu hL).comp Complex.continuous_ofReal)

#print axioms continuousAt_transfer
#print axioms continuous_discReal

end QuantumNLS.RootDiscriminantContinuity
