import Mathlib
import QuantumNLS.L1Stability
import QuantumNLS.L2SpatialTransfer
import QuantumNLS.RootDiscriminantBound

/-!
# R-0C33082D (`prop:D05-total-variation`): joint continuity of the discriminant in `(κ, u) ∈ ℝ × L²(𝕋_L)`

Source: `D05.tex`, proof of `prop:D05-total-variation`: "`‖√κ_j u_j - √κ u‖₁ ≤ √L(√κ_j ‖u_j - u‖₂ + |√κ_j - √κ| ‖u‖₂)`", "`A_j → A` in `L¹`", Gronwall, hence `Δ_{κ_j,u_j}(t) → Δ_{κ,u}(t)`.

* `integral_profile_le`: `∫₀ᴸ |u(s)| ds ≤ √L ‖u‖₂` for the pulled-back profile of `w ∈ L²(𝕋_L)` (Hölder).
* `norm_balCoef_sub_le`: `‖A_{κ,v}(x) - A_{κ',v'}(x)‖ ≤ |√κ v(x) - √κ' v'(x)|` (same `z`).
* `continuous_discriminant_param`: `(κ,u) ↦ Δ_{κ,u}(z)` is jointly continuous on `ℝ × L²` (every `z ∈ ℂ`), via `L1Stability.norm_transfer_sub_le`
  (the Gronwall estimate `‖F_j - F‖ ≤ e^{‖A_j‖₁+‖A‖₁}‖A_j - A‖₁`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set ComplexConjugate
open scoped Matrix Interval ENNReal

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace QuantumNLS.DiscParamContinuity

open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.L1Stability
open QuantumNLS.L2SpatialTransfer (profile intervalIntegrable_profile intervalIntegrable_coef discriminant spatialTransfer)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootDiscriminantBound (row_sum_le_norm norm_le_of_row_sums)

local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : ENormedAddMonoid Mat2 :=
  NormedAddGroup.toENormedAddMonoid

variable {L : ℝ} [Fact (0 < L)]

/-! ### `L²(𝕋_L) → L¹[0,L]` for the pulled-back profile -/

theorem profile_sub_ae (u u0 : L2T L) :
    (fun s : ℝ => profile (u - u0) s) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)]
      fun s => profile u s - profile u0 s := by
  have hmp := AddCircle.measurePreserving_mk L 0
  have h := hmp.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_sub u u0)
  simpa [Function.comp_def, profile, zero_add] using h

theorem integral_profile_le (w : L2T L) :
    ∫ s in (0 : ℝ)..L, ‖profile w s‖ ≤ Real.sqrt L * ‖w‖ := by
  have hL : 0 < L := Fact.out
  rw [intervalIntegral.integral_of_le hL.le]
  have hw : AEStronglyMeasurable (w : AddCircle L → ℂ) volume := Lp.aestronglyMeasurable w
  have hmp := AddCircle.measurePreserving_mk L 0
  simp only [zero_add] at hmp
  have e : ∫ s in Ioc (0 : ℝ) L, ‖profile w s‖ = ∫ x : AddCircle L, ‖(w : AddCircle L → ℂ) x‖ := by
    have h1 := integral_map (μ := volume.restrict (Ioc (0 : ℝ) L)) (φ := ((↑) : ℝ → AddCircle L))
      (f := fun x : AddCircle L => ‖(w : AddCircle L → ℂ) x‖) hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hw.norm)
    rw [hmp.map_eq] at h1
    exact h1.symm
  rw [e, integral_norm_eq_lintegral_enorm hw]
  have h2 : ∫⁻ x : AddCircle L, ‖(w : AddCircle L → ℂ) x‖ₑ = eLpNorm w 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm hw]
  rw [h2]
  have h3 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := (volume : Measure (AddCircle L)))
    (f := (w : AddCircle L → ℂ)) (p := 1) (q := 2) (by norm_num) hw
  have hvol : (volume : Measure (AddCircle L)) Set.univ = ENNReal.ofReal L :=
    QuantumNLS.PhysicalTensor.torus_mass L
  rw [hvol] at h3
  have h4 : (eLpNorm w 2 volume * ENNReal.ofReal L ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (Lp.eLpNorm_lt_top w).ne ?_
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have h5 := ENNReal.toReal_mono h4 h3
  refine le_trans h5 ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hL.le]
  have : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  rw [this, ← Real.sqrt_eq_rpow, mul_comm]
  have : (eLpNorm w 2 volume).toReal = ‖w‖ := by rw [Lp.norm_def]
  rw [this]

/-! ### The coefficient difference -/

theorem norm_balCoef_sub_le (κ κ' : ℝ) (v v' : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    ‖balCoef κ v z x - balCoef κ' v' z x‖ ≤
      ‖(Real.sqrt κ : ℂ) * v x - (Real.sqrt κ' : ℂ) * v' x‖ := by
  refine norm_le_of_row_sums _ (norm_nonneg _) fun i => ?_
  fin_cases i
  · simp [balCoef, coef]
    rw [← Complex.norm_conj (_ * _ - _ * _)]
    simp [map_sub, map_mul]
  · simp [balCoef, coef]

/-! ### Joint continuity -/

theorem continuous_discriminant_param (z : ℂ) :
    Continuous (fun p : ℝ × L2T L => discriminant p.1 p.2 z) := by
  have hL : 0 < L := Fact.out
  rw [continuous_iff_continuousAt]
  rintro ⟨κ0, u0⟩
  set A : ℝ × L2T L → ℝ → Mat2 := fun p => balCoef p.1 (profile p.2) z with hAdef
  have hA : ∀ p, IntervalIntegrable (A p) volume 0 L := fun p =>
    intervalIntegrable_coef (intervalIntegrable_profile p.2) _ _ z
  set a : ℝ × L2T L → ℝ := fun p => ∫ s in (0 : ℝ)..L, ‖A p s - A (κ0, u0) s‖ with hadef
  set b0 : ℝ := ∫ s in (0 : ℝ)..L, ‖A (κ0, u0) s‖ with hb0
  set I0 : ℝ := ∫ s in (0 : ℝ)..L, ‖profile u0 s‖ with hI0
  have hnorm_int : ∀ p, IntervalIntegrable (fun s => ‖A p s - A (κ0, u0) s‖) volume 0 L := fun p =>
    ((hA p).sub (hA (κ0, u0))).norm
  have ha0 : ∀ p, 0 ≤ a p := fun p => intervalIntegral.integral_nonneg hL.le fun s _ => norm_nonneg _
  -- the bound U(p) for a(p)
  set U : ℝ × L2T L → ℝ := fun p =>
    Real.sqrt p.1 * (Real.sqrt L * ‖p.2 - u0‖) + |Real.sqrt p.1 - Real.sqrt κ0| * I0 with hU
  have hu_int : ∀ p : ℝ × L2T L, IntervalIntegrable (fun s => ‖profile p.2 s - profile u0 s‖) volume 0 L :=
    fun p => ((intervalIntegrable_profile p.2).sub (intervalIntegrable_profile u0)).norm
  have hprof : ∀ p : ℝ × L2T L,
      ∫ s in (0 : ℝ)..L, ‖profile p.2 s - profile u0 s‖ ≤ Real.sqrt L * ‖p.2 - u0‖ := by
    intro p
    have h1 : ∫ s in (0 : ℝ)..L, ‖profile p.2 s - profile u0 s‖ =
        ∫ s in (0 : ℝ)..L, ‖profile (p.2 - u0) s‖ := by
      rw [intervalIntegral.integral_of_le hL.le, intervalIntegral.integral_of_le hL.le]
      refine integral_congr_ae ?_
      filter_upwards [profile_sub_ae p.2 u0] with s hs
      rw [hs]
    rw [h1]
    exact integral_profile_le _
  have ha_le : ∀ p, a p ≤ U p := by
    intro p
    have hpt : ∀ s, ‖A p s - A (κ0, u0) s‖ ≤
        Real.sqrt p.1 * ‖profile p.2 s - profile u0 s‖ + |Real.sqrt p.1 - Real.sqrt κ0| * ‖profile u0 s‖ := by
      intro s
      refine le_trans (norm_balCoef_sub_le p.1 κ0 (profile p.2) (profile u0) z s) ?_
      have e : (Real.sqrt p.1 : ℂ) * profile p.2 s - (Real.sqrt κ0 : ℂ) * profile u0 s =
          (Real.sqrt p.1 : ℂ) * (profile p.2 s - profile u0 s) +
            ((Real.sqrt p.1 : ℂ) - (Real.sqrt κ0 : ℂ)) * profile u0 s := by ring
      rw [e]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      have : ‖(Real.sqrt p.1 : ℂ) - (Real.sqrt κ0 : ℂ)‖ = |Real.sqrt p.1 - Real.sqrt κ0| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [this]
    have hint2 : IntervalIntegrable (fun s => Real.sqrt p.1 * ‖profile p.2 s - profile u0 s‖ +
        |Real.sqrt p.1 - Real.sqrt κ0| * ‖profile u0 s‖) volume 0 L :=
      ((hu_int p).const_mul _).add (((intervalIntegrable_profile u0).norm).const_mul _)
    have h1 := intervalIntegral.integral_mono_on hL.le (hnorm_int p) hint2 (fun s _ => hpt s)
    refine le_trans h1 ?_
    rw [intervalIntegral.integral_add ((hu_int p).const_mul _) (((intervalIntegrable_profile u0).norm).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have := hprof p
    have hs : 0 ≤ Real.sqrt p.1 := Real.sqrt_nonneg _
    simp only [hU, hI0]
    nlinarith [mul_le_mul_of_nonneg_left this hs]
  have hUcont : ContinuousAt U (κ0, u0) := by
    have : Continuous U := by
      simp only [hU]
      fun_prop
    exact this.continuousAt
  have hU0 : U (κ0, u0) = 0 := by simp [hU]
  have haT : Tendsto a (𝓝 (κ0, u0)) (𝓝 0) := by
    have hUT : Tendsto U (𝓝 (κ0, u0)) (𝓝 0) := by
      have := hUcont.tendsto
      rwa [hU0] at this
    exact squeeze_zero ha0 ha_le hUT
  -- the bound for the discriminant difference
  set K1 : ℝ := ‖(1 : Mat2)‖ with hK1
  set R : ℝ → ℝ := fun x => 2 * (x * (K1 * Real.exp (b0 + x)) * Real.exp b0) with hR
  have hRT : Tendsto (fun p => R (a p)) (𝓝 (κ0, u0)) (𝓝 0) := by
    have hRc : Continuous R := by simp only [hR]; fun_prop
    have h0 : R 0 = 0 := by simp [hR]
    have := (hRc.tendsto 0).comp haT
    rwa [h0] at this
  have hbound : ∀ p, ‖discriminant p.1 p.2 z - discriminant κ0 u0 z‖ ≤ R (a p) := by
    intro p
    have hLmem : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
    have hdiff := norm_transfer_sub_le hL.le (hA p) (hA (κ0, u0)) hLmem
    have hb : ∫ s in (0 : ℝ)..L, ‖A p s‖ ≤ b0 + a p := by
      have hpt : ∀ s, ‖A p s‖ ≤ ‖A (κ0, u0) s‖ + ‖A p s - A (κ0, u0) s‖ := by
        intro s
        have := norm_add_le (A (κ0, u0) s) (A p s - A (κ0, u0) s)
        simpa [add_sub_cancel, add_comm] using this
      have h1 := intervalIntegral.integral_mono_on hL.le (hA p).norm
        ((hA (κ0, u0)).norm.add (hnorm_int p)) (fun s _ => hpt s)
      refine le_trans h1 ?_
      rw [intervalIntegral.integral_add (hA (κ0, u0)).norm (hnorm_int p)]
    have hexp : Real.exp (∫ s in (0 : ℝ)..L, ‖A p s‖) ≤ Real.exp (b0 + a p) := Real.exp_le_exp.2 hb
    have hK0 : 0 ≤ K1 := norm_nonneg _
    have htr : ‖discriminant p.1 p.2 z - discriminant κ0 u0 z‖ ≤
        2 * ‖spatialTransfer p.1 p.2 z L - spatialTransfer κ0 u0 z L‖ := by
      unfold QuantumNLS.L2SpatialTransfer.discriminant
      rw [← Matrix.trace_sub, Matrix.trace_fin_two]
      refine le_trans (norm_add_le _ _) ?_
      have h0 := row_sum_le_norm (spatialTransfer p.1 p.2 z L - spatialTransfer κ0 u0 z L) 0
      have h1 := row_sum_le_norm (spatialTransfer p.1 p.2 z L - spatialTransfer κ0 u0 z L) 1
      have n0 := norm_nonneg ((spatialTransfer p.1 p.2 z L - spatialTransfer κ0 u0 z L) 0 1)
      have n1 := norm_nonneg ((spatialTransfer p.1 p.2 z L - spatialTransfer κ0 u0 z L) 1 0)
      linarith
    refine le_trans htr ?_
    simp only [hR]
    have hdiff' : ‖spatialTransfer p.1 p.2 z L - spatialTransfer κ0 u0 z L‖ ≤
        a p * (K1 * Real.exp (b0 + a p)) * Real.exp b0 := by
      refine le_trans hdiff ?_
      have e0 : 0 ≤ Real.exp b0 := (Real.exp_pos _).le
      have : a p * (K1 * Real.exp (∫ s in (0 : ℝ)..L, ‖A p s‖)) ≤ a p * (K1 * Real.exp (b0 + a p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hK0) (ha0 p)
      exact mul_le_mul_of_nonneg_right this e0
    linarith
  have hT : Tendsto (fun p : ℝ × L2T L => ‖discriminant p.1 p.2 z - discriminant κ0 u0 z‖)
      (𝓝 (κ0, u0)) (𝓝 0) :=
    squeeze_zero (fun p => norm_nonneg _) hbound hRT
  exact (tendsto_iff_norm_sub_tendsto_zero.2 hT)

end QuantumNLS.DiscParamContinuity

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.DiscParamContinuity.integral_profile_le
#print axioms QuantumNLS.DiscParamContinuity.norm_balCoef_sub_le
#print axioms QuantumNLS.DiscParamContinuity.continuous_discriminant_param
