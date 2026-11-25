import Mathlib
import QuantumNLS.RB01TraceGauge
import QuantumNLS.PhysicalUpperTraceIdentity

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-10: the trace Lipschitz bound (source eq. GB01-trace-Lipschitz,
`collective_actions.tex:333-343`) and Cauchy bounds in `z`, for the actual DEF-014 discriminant
`L2SpatialTransfer.discriminant κ u z` on the physical carrier `L²(𝕋_L)` (real slice, as in RB01-3..8).

* `abs_trace_le`: `|tr M| ≤ 2‖M‖`.
* `integral_profile_sub_le`: `∫₀ᴸ |u − ũ| ≤ √L ‖u − ũ‖₂` ("`‖u‖₁ ≤ √L‖u‖₂` is sufficient").
* `norm_gauge_sub_le`: Dyson difference bound for `W_u − W_ũ` (RootInteractionL1.norm_transfer_Bc_sub_le).
* **`disc_lipschitz`** (eq. GB01-trace-Lipschitz): for all `C₀, R ≥ 0` there is `C` with
  `|Δ_u(z) − Δ_ũ(z)| ≤ C ‖u − ũ‖` for `‖u‖, ‖ũ‖ ≤ R`, every `Re z ∈ ℝ` and `|Im z| ≤ C₀`.
* `disc_zero`: `Δ_0(z) = 2cos(zL/2)`; **`disc_bound`**: `|Δ_u(z)| ≤ B` uniformly for `‖u‖ ≤ R`, `|Im z| ≤ C₀`.
* **`deriv_disc_lipschitz`**, **`deriv_disc_bound`** (Cauchy estimates on the smaller strip, radius one):
  `|∂_zΔ_u(z) − ∂_zΔ_ũ(z)| ≤ C ‖u − ũ‖` and `|∂_zΔ_u(z)| ≤ B` for `|Im z| ≤ C₀`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.LinearFundamental
  QuantumNLS.RootInteractionL1 QuantumNLS.RB01TraceGauge
open QuantumNLS.RootDiscriminantBound (P1 P2 norm_le_of_row_sums row_sum_le_norm norm_one_mat2_le)

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

local instance instPseudoMetrizableMat2RB01TL : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance instENormedAddMonoidMat2RB01TL : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RB01TraceLip

variable {L : ℝ} [Fact (0 < L)]

theorem abs_trace_le (M : Mat2) : ‖Matrix.trace M‖ ≤ 2 * ‖M‖ := by
  rw [Matrix.trace_fin_two]
  have h0 := row_sum_le_norm M 0
  have h1 := row_sum_le_norm M 1
  have := norm_add_le (M 0 0) (M 1 1)
  linarith [norm_nonneg (M 0 1), norm_nonneg (M 1 0)]

theorem integral_profile_sub_le (u v : PhysicalTensor.L2T L) :
    ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile u s - L2SpatialTransfer.profile v s‖ ≤
      Real.sqrt L * ‖u - v‖ := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have he : ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile u s - L2SpatialTransfer.profile v s‖ =
      ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile (u - v) s‖ := by
    apply intervalIntegral.integral_congr_ae
    have h := (ae_restrict_iff' measurableSet_Ioc).mp (DiscParamContinuity.profile_sub_ae u v)
    filter_upwards [h] with s hs hs'
    rw [uIoc_of_le hL] at hs'
    rw [hs hs']
  rw [he]
  exact DiscParamContinuity.integral_profile_le (u - v)

/-- The interaction coefficient's `L¹` mass, uniformly on the strip and the ball. -/
def mass (κ C₀ R : ℝ) (L : ℝ) : ℝ := Real.sqrt κ * Real.exp (C₀ * L) * (Real.sqrt L * R)

theorem integral_gaugeCoef_le_mass (κ : ℝ) {C₀ R : ℝ} (u : PhysicalTensor.L2T L) (hu : ‖u‖ ≤ R)
    {z : ℂ} (hz : |z.im| ≤ C₀) :
    ∫ s in (0 : ℝ)..L, ‖Bc κ (L2SpatialTransfer.profile u) z s‖ ≤ mass κ C₀ R L := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  refine (integral_norm_gaugeCoef_le κ u z).trans ?_
  unfold mass
  have h1 : Real.exp (|z.im| * L) ≤ Real.exp (C₀ * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hz hL)
  have h2 : Real.sqrt L * ‖u‖ ≤ Real.sqrt L * R := mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _)
  gcongr

theorem norm_gauge_sub_le (κ : ℝ) {C₀ R : ℝ} (u v : PhysicalTensor.L2T L) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    {z : ℂ} (hz : |z.im| ≤ C₀) :
    ‖gauge κ u z L - gauge κ v z L‖ ≤
      Real.sqrt κ * Real.exp (C₀ * L) * Real.sqrt L * (Real.exp (mass κ C₀ R L) * Real.exp (mass κ C₀ R L)) *
        ‖u - v‖ := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hiu := L2SpatialTransfer.intervalIntegrable_profile u
  have hiv := L2SpatialTransfer.intervalIntegrable_profile v
  have h := norm_transfer_sub_le_of hL (intervalIntegrable_Bc hiu κ z) (intervalIntegrable_Bc hiv κ z)
    (integral_gaugeCoef_le_mass κ u hu hz) (integral_gaugeCoef_le_mass κ v hv hz)
    (le_refl _) (x := L) ⟨hL, le_rfl⟩
  refine h.trans ?_
  have hd := integral_norm_Bc_sub_le hL hiu hiv κ z
  have hp := integral_profile_sub_le u v
  have h1 : Real.exp (|z.im| * L) ≤ Real.exp (C₀ * L) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hz hL)
  have hE : 0 ≤ Real.exp (mass κ C₀ R L) * Real.exp (mass κ C₀ R L) := by positivity
  have hI : 0 ≤ ∫ s in (0 : ℝ)..L, ‖L2SpatialTransfer.profile u s - L2SpatialTransfer.profile v s‖ :=
    intervalIntegral.integral_nonneg hL (fun _ _ => norm_nonneg _)
  calc (∫ s in (0 : ℝ)..L, ‖Bc κ (L2SpatialTransfer.profile u) z s - Bc κ (L2SpatialTransfer.profile v) z s‖) *
        (Real.exp (mass κ C₀ R L) * Real.exp (mass κ C₀ R L))
      ≤ (Real.sqrt κ * Real.exp (C₀ * L) * (Real.sqrt L * ‖u - v‖)) *
        (Real.exp (mass κ C₀ R L) * Real.exp (mass κ C₀ R L)) := by
        refine mul_le_mul_of_nonneg_right (hd.trans ?_) hE
        gcongr
    _ = _ := by ring

/-- The constant of eq. GB01-trace-Lipschitz. -/
def lipConst (κ C₀ R L : ℝ) : ℝ :=
  2 * Real.exp (C₀ * L / 2) *
    (Real.sqrt κ * Real.exp (C₀ * L) * Real.sqrt L * (Real.exp (mass κ C₀ R L) * Real.exp (mass κ C₀ R L)))

theorem lipConst_nonneg (κ C₀ R L : ℝ) : 0 ≤ lipConst κ C₀ R L := by
  unfold lipConst; positivity

theorem disc_sub_eq (κ : ℝ) (u v : PhysicalTensor.L2T L) (z : ℂ) :
    L2SpatialTransfer.discriminant κ u z - L2SpatialTransfer.discriminant κ v z =
      Matrix.trace (freeE z L * (gauge κ u z L - gauge κ v z L)) := by
  rw [discriminant_eq_gauge, discriminant_eq_gauge, mul_sub, Matrix.trace_sub]

/-- **eq. GB01-trace-Lipschitz**, uniformly in `Re z`. -/
theorem disc_lipschitz (κ : ℝ) {C₀ R : ℝ} (u v : PhysicalTensor.L2T L) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    {z : ℂ} (hz : |z.im| ≤ C₀) :
    ‖L2SpatialTransfer.discriminant κ u z - L2SpatialTransfer.discriminant κ v z‖ ≤
      lipConst κ C₀ R L * ‖u - v‖ := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  rw [disc_sub_eq]
  refine (abs_trace_le _).trans ?_
  have hE : ‖freeE z L‖ ≤ Real.exp (C₀ * L / 2) := by
    refine (norm_freeE_le z (L := L) ⟨hL, le_rfl⟩).trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_right hz hL
    linarith
  have hW := norm_gauge_sub_le κ u v hu hv hz
  calc 2 * ‖freeE z L * (gauge κ u z L - gauge κ v z L)‖
      ≤ 2 * (‖freeE z L‖ * ‖gauge κ u z L - gauge κ v z L‖) := by gcongr; exact norm_mul_le _ _
    _ ≤ 2 * (Real.exp (C₀ * L / 2) *
        (Real.sqrt κ * Real.exp (C₀ * L) * Real.sqrt L * (Real.exp (mass κ C₀ R L) * Real.exp (mass κ C₀ R L)) *
          ‖u - v‖)) := by gcongr
    _ = lipConst κ C₀ R L * ‖u - v‖ := by unfold lipConst; ring

theorem profile_zero_ae :
    (fun s : ℝ => L2SpatialTransfer.profile (0 : PhysicalTensor.L2T L) s) =ᵐ[volume.restrict (Icc (0 : ℝ) L)]
      fun _ => 0 := by
  have h := L2SpatialTransfer.profile_ae_of_representative (0 : PhysicalTensor.L2T L)
    (v := fun _ => 0) (Lp.coeFn_zero ℂ 2 volume).symm
  exact h.symm

theorem gauge_zero (κ : ℝ) (z : ℂ) : gauge κ (0 : PhysicalTensor.L2T L) z L = 1 := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hae : Bc κ (L2SpatialTransfer.profile (0 : PhysicalTensor.L2T L)) z =ᵐ[volume.restrict (Icc (0 : ℝ) L)]
      fun _ => (0 : Mat2) := by
    filter_upwards [profile_zero_ae] with s hs
    ext i j; fin_cases i <;> fin_cases j <;> simp [Bc, hs]
  unfold RB01TraceGauge.gauge
  rw [transfer_eq_of_ae hL hae ⟨hL, le_rfl⟩]
  exact transfer_zero hL ⟨hL, le_rfl⟩

/-- The free trace: `Δ_0(z) = 2cos(zL/2)`. -/
theorem disc_zero (κ : ℝ) (z : ℂ) :
    L2SpatialTransfer.discriminant κ (0 : PhysicalTensor.L2T L) z = 2 * Complex.cos (z * L / 2) := by
  rw [discriminant_eq_gauge_entries, gauge_zero, Complex.two_cos]
  simp only [Matrix.one_apply_eq, mul_one, E1c, E2c, a1c]
  rw [add_comm]
  congr 1 <;> congr 1 <;> ring

theorem norm_two_cos_le {C₀ : ℝ} {z : ℂ} (hz : |z.im| ≤ C₀) :
    ‖2 * Complex.cos (z * L / 2)‖ ≤ 2 * Real.exp (C₀ * L / 2) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  rw [← disc_zero (L := L) 0 z, discriminant_eq_gauge, gauge_zero, mul_one]
  have hE : ‖freeE z L‖ ≤ Real.exp (C₀ * L / 2) := by
    refine (norm_freeE_le z (L := L) ⟨hL, le_rfl⟩).trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_right hz hL
    linarith
  exact (abs_trace_le _).trans (by linarith)

/-- Uniform bound on the strip and the ball. -/
def discBound (κ C₀ R L : ℝ) : ℝ := 2 * Real.exp (C₀ * L / 2) + lipConst κ C₀ R L * R

theorem disc_bound (κ : ℝ) {C₀ R : ℝ} (u : PhysicalTensor.L2T L) (hu : ‖u‖ ≤ R) {z : ℂ} (hz : |z.im| ≤ C₀) :
    ‖L2SpatialTransfer.discriminant κ u z‖ ≤ discBound κ C₀ R L := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hu
  have h := disc_lipschitz κ u 0 hu (by simpa using hR) hz
  rw [sub_zero] at h
  have h2 := norm_two_cos_le (L := L) hz
  rw [← disc_zero (L := L) κ z] at h2
  have h3 : ‖L2SpatialTransfer.discriminant κ u z‖ ≤
      ‖L2SpatialTransfer.discriminant κ u z - L2SpatialTransfer.discriminant κ (0 : PhysicalTensor.L2T L) z‖ +
        ‖L2SpatialTransfer.discriminant κ (0 : PhysicalTensor.L2T L) z‖ := by
    have := norm_add_le (L2SpatialTransfer.discriminant κ u z - L2SpatialTransfer.discriminant κ (0 : PhysicalTensor.L2T L) z)
      (L2SpatialTransfer.discriminant κ (0 : PhysicalTensor.L2T L) z)
    simpa using this
  unfold discBound
  have h4 : lipConst κ C₀ R L * ‖u‖ ≤ lipConst κ C₀ R L * R :=
    mul_le_mul_of_nonneg_left hu (lipConst_nonneg _ _ _ _)
  linarith

theorem im_le_of_mem_sphere {z w : ℂ} {C₀ : ℝ} (hz : |z.im| ≤ C₀) (hw : w ∈ sphere z 1) : |w.im| ≤ C₀ + 1 := by
  have h1 : |w.im - z.im| ≤ 1 := by
    have := Complex.abs_im_le_norm (w - z)
    rw [mem_sphere, dist_eq_norm] at hw
    simpa [hw] using this
  have := abs_sub_abs_le_abs_sub w.im z.im
  linarith

/-- **Cauchy estimate**: `z`-derivatives are Lipschitz in the field on the strip `|Im z| ≤ C₀`. -/
theorem deriv_disc_lipschitz (κ : ℝ) {C₀ R : ℝ} (u v : PhysicalTensor.L2T L) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R)
    {z : ℂ} (hz : |z.im| ≤ C₀) :
    ‖deriv (L2SpatialTransfer.discriminant κ u) z - deriv (L2SpatialTransfer.discriminant κ v) z‖ ≤
      lipConst κ (C₀ + 1) R L * ‖u - v‖ := by
  have hdu := PhysicalUpperTraceIdentity.entire_discriminant (L := L) κ u
  have hdv := PhysicalUpperTraceIdentity.entire_discriminant (L := L) κ v
  have hd : Differentiable ℂ (fun w => L2SpatialTransfer.discriminant κ u w - L2SpatialTransfer.discriminant κ v w) :=
    hdu.sub hdv
  have he : deriv (fun w => L2SpatialTransfer.discriminant κ u w - L2SpatialTransfer.discriminant κ v w) z =
      deriv (L2SpatialTransfer.discriminant κ u) z - deriv (L2SpatialTransfer.discriminant κ v) z :=
    deriv_sub (hdu z) (hdv z)
  rw [← he]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) one_pos hd.diffContOnCl
    (fun w hw => disc_lipschitz κ u v hu hv (im_le_of_mem_sphere hz hw))
  simpa using h

theorem deriv_disc_bound (κ : ℝ) {C₀ R : ℝ} (u : PhysicalTensor.L2T L) (hu : ‖u‖ ≤ R)
    {z : ℂ} (hz : |z.im| ≤ C₀) :
    ‖deriv (L2SpatialTransfer.discriminant κ u) z‖ ≤ discBound κ (C₀ + 1) R L := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) one_pos
    (PhysicalUpperTraceIdentity.entire_discriminant (L := L) κ u).diffContOnCl
    (fun w hw => disc_bound κ u hu (im_le_of_mem_sphere hz hw))
  simpa using h

end QuantumNLS.RB01TraceLip

#print axioms QuantumNLS.RB01TraceLip.abs_trace_le
#print axioms QuantumNLS.RB01TraceLip.integral_profile_sub_le
#print axioms QuantumNLS.RB01TraceLip.norm_gauge_sub_le
#print axioms QuantumNLS.RB01TraceLip.disc_lipschitz
#print axioms QuantumNLS.RB01TraceLip.gauge_zero
#print axioms QuantumNLS.RB01TraceLip.disc_zero
#print axioms QuantumNLS.RB01TraceLip.disc_bound
#print axioms QuantumNLS.RB01TraceLip.deriv_disc_lipschitz
#print axioms QuantumNLS.RB01TraceLip.deriv_disc_bound
