import Mathlib
import QuantumNLS.Local007MassB
import QuantumNLS.Local007Gauge
import QuantumNLS.RootMassFree
import QuantumNLS.RootIndexedMasses

/-! LOCAL-007 stage M3: for small `v`, the index-`0` mass is the mass of the free cell `(-π/L, π/L)`.

Uses the accepted cell-cut lemma `RootMassFree.cut_equiv` (any cut with phase strictly between the integer
labels selects the same mass as the separator), the real Cauchy-integral form of the boundary phase
`DEF014Phase.phase_eq_integral`, and the gauge `Local007Gauge.disc_shift` to reduce the band condition at
every cell boundary to closeness of `boost(-j) v` to the free trace. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
namespace QuantumNLS.Local007MassC
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Zeros (Dl)
open QuantumNLS.RootMassBoostSymbol (boost)
variable {L κ : ℝ} [Fact (0 < L)]

theorem abs_re_eq_norm {z : ℂ} (hz : z.im = 0) : |z.re| = ‖z‖ := by
  have h : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using hz)
  conv_rhs => rw [h]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `|cos y| ≤ cos(3/32)` for `y ∈ [3/32, π - 3/32]`. -/
theorem abs_cos_le {y : ℝ} (h1 : 3 / 32 ≤ y) (h2 : y ≤ Real.pi - 3 / 32) : |Real.cos y| ≤ Real.cos (3 / 32) := by
  have hc : 0 ≤ Real.cos (3 / 32) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_gt_three]⟩
  rcases le_total y (Real.pi / 2) with hy | hy
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three]) h1
    have h0 : 0 ≤ Real.cos y := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hy⟩
    rw [abs_of_nonneg h0]; exact h
  · have e : Real.cos y = -Real.cos (Real.pi - y) := by rw [Real.cos_pi_sub]; ring
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith [Real.pi_gt_three])
      (show 3 / 32 ≤ Real.pi - y by linarith)
    have h0 : 0 ≤ Real.cos (Real.pi - y) := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
    rw [e, abs_neg, abs_of_nonneg h0]; exact h

theorem kernel_le (x δ : ℝ) (hδ : 0 < δ) (t : ℝ) : |QuantumNLS.DEF014Phase.kernel x δ hδ t| ≤ δ⁻¹ := by
  change |(x - t) / max (δ ^ 2) ((x - t) ^ 2)| ≤ δ⁻¹
  have hm : 0 < max (δ ^ 2) ((x - t) ^ 2) := lt_max_of_lt_left (by positivity)
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  rcases le_total |x - t| δ with h | h
  · have : max (δ ^ 2) ((x - t) ^ 2) = δ ^ 2 :=
      max_eq_left (by nlinarith [sq_abs (x - t), abs_nonneg (x - t)])
    rw [this]
    have : δ⁻¹ * δ ^ 2 = δ := by field_simp
    linarith
  · have : max (δ ^ 2) ((x - t) ^ 2) = (x - t) ^ 2 :=
      max_eq_right (by nlinarith [sq_abs (x - t), abs_nonneg (x - t)])
    rw [this, ← sq_abs (x - t)]
    have h2 : δ⁻¹ * |x - t| ^ 2 = |x - t| * (|x - t| / δ) := by field_simp
    rw [h2]
    have : 1 ≤ |x - t| / δ := by rw [le_div_iff₀ hδ]; linarith
    nlinarith [abs_nonneg (x - t)]

theorem theta_cell (hκ : 0 < κ) (v : L2T L) (j : ℤ)
    (hcl : ∀ z : ℂ, ‖z‖ ≤ 2 * Real.pi / L →
      ‖Dl κ (boost (-j) v) z - 2 * Complex.cos ((L : ℂ) * z / 2)‖ ≤ 1 / 400)
    (hsmall : κ * L * ‖v‖ ^ 2 < 1) :
    (j : ℝ) * Real.pi < QuantumNLS.RootIndexedPhase.theta hκ v (QuantumNLS.RootMassFree.cell (L := L) j) ∧
      QuantumNLS.RootIndexedPhase.theta hκ v (QuantumNLS.RootMassFree.cell (L := L) j) < ((j : ℝ) + 1) * Real.pi := by
  have hL : 0 < L := Fact.out
  set d : ℝ := 1 / (16 * L) with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hLd : L * d = 1 / 16 := by rw [hd]; field_simp
  set δ : ℝ := Real.pi / L - 3 * d with hδ
  have hδL : 29 / 10 / L ≤ δ := by
    rw [hδ, hd]
    have : Real.pi / L - 3 * (1 / (16 * L)) = (Real.pi - 3 / 16) / L := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith [Real.pi_gt_d2]) hL.le
  have hδ0 : 0 < δ := lt_of_lt_of_le (by positivity) hδL
  have hcellj : QuantumNLS.RootMassFree.cell (L := L) j = (2 * (j : ℝ) + 1) * Real.pi / L := by
    unfold QuantumNLS.RootMassFree.cell
    simp only [QuantumNLS.MonotoneIndexedMasses.level, QuantumNLS.IndexedMasses.level]
    field_simp
  have hb : ∀ t : ℝ, |t - QuantumNLS.RootMassFree.cell (L := L) j| < δ →
      |(QuantumNLS.L2SpatialTransfer.discriminant κ v (t : ℂ)).re| < 2 := by
    intro t ht
    set w : ℝ := t - QuantumNLS.Local007Gauge.pm L j with hw
    have hpm : QuantumNLS.Local007Gauge.pm L j = 2 * Real.pi * j / L := rfl
    have hw1 : |w - Real.pi / L| < δ := by
      have : w - Real.pi / L = t - QuantumNLS.RootMassFree.cell (L := L) j := by
        rw [hw, hpm, hcellj]; field_simp; ring
      rwa [this]
    have hw2 := abs_lt.1 hw1
    have hy1 : 3 / 32 ≤ L * w / 2 := by
      have : 3 * d < w := by linarith [hw2.1]
      nlinarith [hLd, mul_pos hL hd0]
    have hy2 : L * w / 2 ≤ Real.pi - 3 / 32 := by
      have : w < 2 * Real.pi / L - 3 * d := by
        have := hw2.2
        calc w < Real.pi / L + δ := by linarith
          _ = 2 * Real.pi / L - 3 * d := by rw [hδ]; ring
      have h3 : L * w < 2 * Real.pi - 3 * (L * d) := by
        have h4 := mul_lt_mul_of_pos_left this hL
        have e : L * (2 * Real.pi / L - 3 * d) = 2 * Real.pi - 3 * (L * d) := by field_simp
        rw [e] at h4
        linarith
      rw [show 3 * (L * d) = 3 / 16 by rw [hLd]; ring] at h3
      linarith
    have hwn : ‖(w : ℂ)‖ ≤ 2 * Real.pi / L := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith)]
      have : w < 2 * Real.pi / L - 3 * d := by
        have := hw2.2
        calc w < Real.pi / L + δ := by linarith
          _ = 2 * Real.pi / L - 3 * d := by rw [hδ]; ring
      linarith [hd0]
    have hcw := hcl (w : ℂ) hwn
    have hshift := QuantumNLS.Local007Gauge.disc_shift hκ.le j v (w : ℂ)
    have htw : (t : ℂ) = ((QuantumNLS.Local007Gauge.pm L j : ℝ) : ℂ) + (w : ℂ) := by rw [hw]; push_cast; ring
    have hnorm : ‖QuantumNLS.L2SpatialTransfer.discriminant κ v (t : ℂ)‖ =
        ‖QuantumNLS.L2SpatialTransfer.discriminant κ (boost (-j) v) (w : ℂ)‖ := by
      rw [htw, hshift, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
    rw [abs_re_eq_norm (QuantumNLS.L2DiscriminantRegularity.discriminant_real κ v t), hnorm]
    have h2c : ‖2 * Complex.cos ((L : ℂ) * (w : ℂ) / 2)‖ ≤ 2 * Real.cos (3 / 32) := by
      have e : (L : ℂ) * (w : ℂ) / 2 = ((L * w / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, ← Complex.ofReal_cos, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
      have := abs_cos_le hy1 hy2
      linarith
    have := QuantumNLS.Local007MassB.cos_three_thirtytwo
    have h3 := norm_le_norm_add_norm_sub' (QuantumNLS.L2SpatialTransfer.discriminant κ (boost (-j) v) (w : ℂ))
      (2 * Complex.cos ((L : ℂ) * (w : ℂ) / 2))
    linarith
  -- the phase
  let p : QuantumNLS.DEF014Phase.Param L := (⟨κ, hκ⟩, v)
  have hph := QuantumNLS.DEF014Phase.phase_eq_integral p hδ0 hb
  have hth : QuantumNLS.RootIndexedPhase.theta hκ v (QuantumNLS.RootMassFree.cell (L := L) j) =
      L * QuantumNLS.RootMassFree.cell (L := L) j / 2 -
        κ * ∫ t, QuantumNLS.DEF014Phase.kernel (QuantumNLS.RootMassFree.cell (L := L) j) δ hδ0 t
          ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v) := hph
  have hlev : L * QuantumNLS.RootMassFree.cell (L := L) j / 2 = ((j : ℝ) + 1 / 2) * Real.pi := by
    rw [QuantumNLS.RootMassFree.cell_phase]; rfl
  have hint : |∫ t, QuantumNLS.DEF014Phase.kernel (QuantumNLS.RootMassFree.cell (L := L) j) δ hδ0 t
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)| ≤ δ⁻¹ * ‖v‖ ^ 2 := by
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := QuantumNLS.PhysicalQuantumMeasure.measure hκ v)
      (f := fun t => QuantumNLS.DEF014Phase.kernel (QuantumNLS.RootMassFree.cell (L := L) j) δ hδ0 t) (C := δ⁻¹)
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs]; exact kernel_le _ _ _ t)
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have : (QuantumNLS.PhysicalQuantumMeasure.measure hκ v).real Set.univ = ‖v‖ ^ 2 :=
      QuantumNLS.PhysicalQuantumMeasure.full_mass hκ v
    rw [this]
  have hδinv : δ⁻¹ ≤ L / (29 / 10) := by
    rw [inv_le_comm₀ hδ0 (by positivity)]
    calc (L / (29 / 10))⁻¹ = 29 / 10 / L := by field_simp
      _ ≤ δ := hδL
  have hbound : κ * |∫ t, QuantumNLS.DEF014Phase.kernel (QuantumNLS.RootMassFree.cell (L := L) j) δ hδ0 t
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)| < 1 / 2 := by
    calc _ ≤ κ * (δ⁻¹ * ‖v‖ ^ 2) := by gcongr
      _ ≤ κ * (L / (29 / 10) * ‖v‖ ^ 2) := by gcongr
      _ = (κ * L * ‖v‖ ^ 2) / (29 / 10) := by ring
      _ < 1 / 2 := by rw [div_lt_iff₀ (by norm_num)]; linarith
  rw [hth, hlev]
  have h1 := abs_lt.1 (show |κ * ∫ t, QuantumNLS.DEF014Phase.kernel (QuantumNLS.RootMassFree.cell (L := L) j) δ hδ0 t
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ v)| < 1 / 2 by
    rw [abs_mul, abs_of_pos hκ]; exact hbound)
  constructor <;> nlinarith [Real.pi_gt_three, h1.1, h1.2]


theorem masses_zero (hκ : 0 < κ) (v : L2T L)
    (hclB : ∀ j : ℤ, ∀ z : ℂ, ‖z‖ ≤ 2 * Real.pi / L →
      ‖Dl κ (boost (-j) v) z - 2 * Complex.cos ((L : ℂ) * z / 2)‖ ≤ 1 / 400)
    (hsmall : κ * L * ‖v‖ ^ 2 < 1) :
    (QuantumNLS.RootIndexedMasses.masses hκ v).1 0 =
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ v (Ioo (-(Real.pi / L)) (Real.pi / L))).toReal := by
  have hL : 0 < L := Fact.out
  have hk0 := theta_cell hκ v (-1) (hclB (-1)) hsmall
  have hk1 := theta_cell hκ v 0 (hclB 0) hsmall
  have e0 : (0 : ℤ) - 1 = -1 := by norm_num
  have hcm1 : QuantumNLS.RootMassFree.cell (L := L) (-1) = -(Real.pi / L) := by
    unfold QuantumNLS.RootMassFree.cell
    simp only [QuantumNLS.MonotoneIndexedMasses.level, QuantumNLS.IndexedMasses.level]
    push_cast; field_simp; ring
  have hc0 : QuantumNLS.RootMassFree.cell (L := L) 0 = Real.pi / L := by
    unfold QuantumNLS.RootMassFree.cell
    simp only [QuantumNLS.MonotoneIndexedMasses.level, QuantumNLS.IndexedMasses.level]
    push_cast; field_simp; ring
  let k : QuantumNLS.RootMassFree.Coupling := ⟨κ, hκ⟩
  rw [← hcm1, ← hc0]
  change (QuantumNLS.PhysicalQuantumMeasure.measure hκ v (Ioo
    (QuantumNLS.RootIndexedPhase.separator hκ v (0 - 1)) (QuantumNLS.RootIndexedPhase.separator hκ v 0))).toReal = _
  rw [e0]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have c0 := QuantumNLS.RootMassFree.cut_equiv k v (-1) (QuantumNLS.RootMassFree.cell (L := L) (-1)) hk0.1 hk0.2
  have c1 := QuantumNLS.RootMassFree.cut_equiv k v 0 (QuantumNLS.RootMassFree.cell (L := L) 0)
    (by simpa using hk1.1) (by simpa using hk1.2)
  filter_upwards [c0, c1] with t ht0 ht1
  simp only [mem_Ioo, ht0.1, ht1.2]

end QuantumNLS.Local007MassC
#print axioms QuantumNLS.Local007MassC.masses_zero
