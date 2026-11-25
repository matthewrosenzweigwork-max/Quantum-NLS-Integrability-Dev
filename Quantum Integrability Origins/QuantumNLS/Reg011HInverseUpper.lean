import QuantumNLS.Reg011HInverseMid
import QuantumNLS.Reg011HFreeMoment
import QuantumNLS.Reg010LowFinal
import QuantumNLS.Reg010LowEmbeddingMap
import QuantumNLS.Reg010LowL4Space
import QuantumNLS.TerraMultiRound64BaseCoefficient
import QuantumNLS.TerraMultiRound59REG007
import QuantumNLS.TerraMultiRound59RCompatibility
import QuantumNLS.TerraMultiRound64FieldIdentity
import QuantumNLS.TerraMultiRound75Correction
import QuantumNLS.TerraMultiRound78UpperPrinted
import QuantumNLS.TerraMultiRound77FreeContinuity
import QuantumNLS.TerraMultiRound77ActionCriteria

/-! REG-011 upper inverse continuity (haiku_inventory, module Reg011HInverseUpper), orders
1 ≤ s ≤ 2. Inverse continuity V ∩ h^s → H^s, by cases:
* s = 1 (`inverse_one_tendsto`): the free second moment is the physical one minus R1 (frozen
  `TerraMultiRound64BaseCoefficient.first_moment_correction`), and R1 = κ‖E w‖⁴ with E the
  native L⁴ embedding of H^{1/3} (frozen `TerraMultiRound59REG007.R1field_quartic`,
  `TranslatedCorrelation.ae_eq_contRep`, `Reg010LowL4Space.fourth_integral`). The H^{1/3}
  inverse converges by `Reg011HInverseLow.inverse_low_tendsto`, so no H¹ input is assumed.
* 1 < s < 2 (`inverse_mid_upper_tendsto`): the printed upper identity
  (frozen `TerraMultiRound78UpperPrinted.physical_free_upper_printed`) with the H¹ continuity of
  the correction (frozen `TerraMultiRound75Correction.correction_continuous`) and the H¹ inverse
  of the same L² vector from the s = 1 case.
* s = 2 (`inverse_two_tendsto`): the finite field identity (frozen
  `TerraMultiRound64FieldIdentity.finite_field_identity`) with the H¹ continuity of
  `TerraMultiRound59RCompatibility.Rfield_continuous` at j = 2 and the H¹ inverse of the same L².
The REG-010 chain (Reg010LowFinal, Reg010LowPrinted, Reg010LowEmbeddingMap, Reg010LowL4Correction)
is frozen but PENDING REG-010 REVIEW; every result here is conditional on that review, and no
acceptance is claimed. Read-only imports only; no review record unfrozen module is imported. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.Fourier QuantumNLS.RootWeightedCellsR26
open QuantumNLS.Reg011SettingR48a
namespace QuantumNLS.Reg011HInverseUpper

variable {L κ : ℝ} [Fact (0 < L)] {V : Set Seq}

/-! ### Order transfers (value-preserving CLMs; same L² vector) -/

/-- H¹ → Hk L 1 = H02 L ((1:ℕ):ℝ). -/
def toHk1 : H02 L 1 →L[ℂ] QuantumNLS.TranslatedCorrelation.Hk L 1 :=
  H02.mono (show ((1:ℕ):ℝ) ≤ 1 by norm_num)

theorem toHk1_val (u : H02 L 1) : (toHk1 (L := L) u).val = u.val :=
  QuantumNLS.Reg010LowFinal.H02_lower_val _ _ (show ((1:ℕ):ℝ) ≤ 1 by norm_num) u

/-- H¹ → Hk L (2-1), the domain of the frozen `Rfield 2`. -/
def toHk21 : H02 L 1 →L[ℂ] QuantumNLS.TranslatedCorrelation.Hk L (2 - 1) :=
  H02.mono (show (((2 - 1 : ℕ)) : ℝ) ≤ 1 by norm_num)

theorem toHk21_val (u : H02 L 1) : (toHk21 (L := L) u).val = u.val :=
  QuantumNLS.Reg010LowFinal.H02_lower_val _ _ (show (((2 - 1 : ℕ)) : ℝ) ≤ 1 by norm_num) u

/-- H² → Hk L 2 = H02 L ((2:ℕ):ℝ). -/
def toHk2 : H02 L 2 →L[ℂ] QuantumNLS.TranslatedCorrelation.Hk L 2 :=
  H02.mono (show ((2:ℕ):ℝ) ≤ 2 by norm_num)

theorem toHk2_val (u : H02 L 2) : (toHk2 (L := L) u).val = u.val :=
  QuantumNLS.Reg010LowFinal.H02_lower_val _ _ (show ((2:ℕ):ℝ) ≤ 2 by norm_num) u

/-- Monotone restriction of the coordinates h^s → h^t (t ≤ s) preserves the ℓ² vector. -/
theorem toBase_mono_gen {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hst : t ≤ s) (x : h02 L s) :
    toBase (L := L) t ht (h02_mono L hst x) = toBase (L := L) s hs x := by
  apply lp.ext
  funext n
  rw [toBase_apply, toBase_apply]
  rfl

/-- The order-1 inverse of the coordinates of z has the same L² vector as the order-s inverse. -/
theorem inverse_mono_one_val (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : (1:ℝ) ≤ s) (hs2 : s ≤ 2) (z : h02 L s)
    (hz : toBase (L := L) s hs0 z ∈ V)
    (hz' : toBase (L := L) 1 zero_le_one (h02_mono L hs1 z) ∈ V) :
    (inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L hs1 z, hz'⟩ : Target (L := L) V 1 zero_le_one)).val =
    (inverse e hκ he s hs0 hs2 (⟨z, hz⟩ : Target (L := L) V s hs0)).val := by
  have h1 := inverse_val e hκ he 1 zero_le_one one_le_two
    (⟨h02_mono L hs1 z, hz'⟩ : Target (L := L) V 1 zero_le_one)
  have h2 := inverse_val e hκ he s hs0 hs2 (⟨z, hz⟩ : Target (L := L) V s hs0)
  rw [h1, h2]
  unfold baseInverse
  exact congrArg e.symm (Subtype.ext (toBase_mono_gen zero_le_one hs0 hs1 z))

/-! ### Scalar and integral conversions between `t^(2k)` (ℕ) and `|t|^(2s)` (ℝ) -/

theorem abs_rpow_one (t : ℝ) : |t| ^ (2 * (1:ℝ)) = t ^ (2 * 1) := by
  norm_num [Real.rpow_two, sq_abs]

theorem abs_rpow_two (t : ℝ) : |t| ^ (2 * (2:ℝ)) = t ^ (2 * 2) := by
  have h : (2:ℝ) * 2 = ((4:ℕ):ℝ) := by norm_num
  rw [h, Real.rpow_natCast]
  exact Even.pow_abs ⟨2, rfl⟩ t

theorem integral_one_eq (μ : Measure ℝ) :
    ∫ t : ℝ, t ^ (2 * 1) ∂μ = ∫ t : ℝ, |t| ^ (2 * (1:ℝ)) ∂μ := by
  simp only [abs_rpow_one]

theorem integral_two_eq (μ : Measure ℝ) :
    ∫ t : ℝ, t ^ (2 * 2) ∂μ = ∫ t : ℝ, |t| ^ (2 * (2:ℝ)) ∂μ := by
  simp only [abs_rpow_two]

/-- Free fourth moment as a Fourier sum (from the frozen `free_moment_eq_tsum`). -/
theorem free_rpow_two (u : L2T L) :
    ∫ t : ℝ, |t| ^ (2 * (2:ℝ)) ∂(QuantumNLS.FreeLimit.freeMeasure L u) =
      ∑' n : ℤ, (momentum L n) ^ (2 * 2) *
        ‖QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ^ 2 := by
  rw [QuantumNLS.Reg011HFreeMoment.free_moment_eq_tsum]
  apply tsum_congr
  intro n
  rw [abs_rpow_two, QuantumNLS.Fourier.fourierL2_apply]

/-! ### s = 1 -/

/-- R1 through the native L⁴ embedding: for u ∈ H¹ and w ∈ H^{1/3} with the same L² vector,
R1(u) = κ ‖E w‖⁴ where E = `embeddingH02 w` (frozen R1field_quartic + ae_eq_contRep). -/
theorem R1_eq_third (κ : ℝ) (w : H02 L (1/3)) (u : H02 L 1) (h : u.val = w.val) :
    QuantumNLS.TerraMultiRound59RCompatibility.R1field (L := L) κ (toHk1 (L := L) u) =
      κ * ‖QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 w‖ ^ 4 := by
  rw [QuantumNLS.TerraMultiRound59REG007.R1field_quartic L κ (toHk1 (L := L) u)]
  congr 1
  have hE := QuantumNLS.Reg010LowL4Space.fourth_integral
    (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 w)
  rw [← hE]
  apply integral_congr_ae
  have hvE : (toHk1 (L := L) u).val =
      QuantumNLS.Reg010LowL4Space.toL2 (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 w) := by
    rw [toHk1_val, h, QuantumNLS.Reg010LowEmbeddingMap.embeddingH02_toL2]
  filter_upwards [QuantumNLS.TranslatedCorrelation.ae_eq_contRep (le_refl (1:ℕ))
      (toHk1 (L := L) u),
    QuantumNLS.Reg010LowL4Space.toL2_ae (QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 w)]
    with y hy1 hy2
  rw [hvE] at hy1
  rw [← hy1, hy2]

/-- R1 converges along H^{1/3}-convergent representatives with equal L² vectors. -/
theorem R1_tendsto_of_third (κ : ℝ) (w : ℕ → H02 L 1) (w0 : H02 L 1)
    (third : ℕ → H02 L (1/3)) (third0 : H02 L (1/3))
    (hthird : Tendsto third atTop (𝓝 third0))
    (hw : ∀ j, (w j).val = (third j).val) (hw0 : w0.val = third0.val) :
    Tendsto (fun j => QuantumNLS.TerraMultiRound59RCompatibility.R1field (L := L) κ
        (toHk1 (L := L) (w j))) atTop
      (𝓝 (QuantumNLS.TerraMultiRound59RCompatibility.R1field (L := L) κ (toHk1 (L := L) w0))) := by
  have hcont : Continuous (fun x : H02 L (1/3) =>
      κ * ‖QuantumNLS.Reg010LowEmbeddingMap.embeddingH02 x‖ ^ 4) :=
    continuous_const.mul ((QuantumNLS.Reg010LowEmbeddingMap.embeddingH02.continuous.norm).pow 4)
  have hE := (hcont.tendsto third0).comp hthird
  rw [R1_eq_third κ third0 w0 hw0]
  exact hE.congr (fun j => (R1_eq_third κ (third j) (w j) (hw j)).symm)

/-- Abstract s = 1 step: free second moment = physical minus R1 (frozen first_moment_correction),
so the H¹ norm converges from L², the physical moment and R1 convergence. -/
theorem inverse_one_core (κ : ℝ) (hκ : 0 < κ) (w : ℕ → H02 L 1) (w0 : H02 L 1)
    (hL2 : Tendsto (fun j => (w j).val) atTop (𝓝 w0.val))
    (hphys : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * (1:ℝ))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (w j).val)) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * (1:ℝ)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ w0.val))))
    (hR : Tendsto (fun j => QuantumNLS.TerraMultiRound59RCompatibility.R1field (L := L) κ
        (toHk1 (L := L) (w j))) atTop
      (𝓝 (QuantumNLS.TerraMultiRound59RCompatibility.R1field (L := L) κ (toHk1 (L := L) w0)))) :
    Tendsto w atTop (𝓝 w0) := by
  have key : ∀ u : H02 L 1,
      ∫ t : ℝ, |t| ^ (2 * (1:ℝ)) ∂(QuantumNLS.FreeLimit.freeMeasure L u.val) =
        (∫ t : ℝ, |t| ^ (2 * (1:ℝ)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
          QuantumNLS.TerraMultiRound59RCompatibility.R1field (L := L) κ (toHk1 (L := L) u) := by
    intro u
    have h := QuantumNLS.TerraMultiRound64BaseCoefficient.first_moment_correction hκ u.val
      (toHk1 (L := L) u) (toHk1_val u)
    rw [integral_one_eq, integral_one_eq] at h
    linarith
  have hpt := hphys.sub hR
  rw [← key w0] at hpt
  have hfree : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * (1:ℝ))
        ∂(QuantumNLS.FreeLimit.freeMeasure L (w j).val)) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * (1:ℝ)) ∂(QuantumNLS.FreeLimit.freeMeasure L w0.val))) :=
    hpt.congr (fun j => (key (w j)).symm)
  have hn := QuantumNLS.Reg011HInverseMid.norm_sq_tendsto_of_free (L := L) zero_le_one w w0 hL2 hfree
  exact QuantumNLS.Reg011HSobolevConvergence.H02_tendsto_of_L2_and_norm w w0 hL2 hn

/-- **s = 1 inverse continuity.** z_j → z0 in h^1 with z_j ∈ V give inverse images converging in
H¹. REG-010 pending review (the L⁴ and H^{1/3} inputs are frozen REG-010 chain). -/
theorem inverse_one_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (z : ℕ → h02 L 1) (z0 : h02 L 1) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) 1 zero_le_one (z j) ∈ V)
    (hV0 : toBase (L := L) 1 zero_le_one z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he 1 zero_le_one one_le_two
        (⟨z j, hzV j⟩ : Target (L := L) V 1 zero_le_one)) atTop
      (𝓝 (inverse e hκ he 1 zero_le_one one_le_two (⟨z0, hV0⟩ : Target (L := L) V 1 zero_le_one))) := by
  have h0 : (0:ℝ) ≤ 1 := zero_le_one
  have h13 : (1/3 : ℝ) ≤ 1 := by norm_num
  have h3p : (0:ℝ) < 1/3 := by norm_num
  have h3s : (1/3 : ℝ) < 1/2 := by norm_num
  have h3two : (1/3 : ℝ) ≤ 2 := by norm_num
  have hz3 : Tendsto (fun j => h02_mono L h13 (z j)) atTop (𝓝 (h02_mono L h13 z0)) :=
    ((h02_mono L h13).continuous.tendsto z0).comp hz
  have hzV3 : ∀ j, toBase (L := L) (1/3) h3p.le (h02_mono L h13 (z j)) ∈ V := fun j => by
    rw [toBase_mono_gen h3p.le h0 h13 (z j)]
    exact hzV j
  have hV03 : toBase (L := L) (1/3) h3p.le (h02_mono L h13 z0) ∈ V := by
    rw [toBase_mono_gen h3p.le h0 h13 z0]
    exact hV0
  have hw3 := QuantumNLS.Reg011HInverseLow.inverse_low_tendsto hκ e he (1/3) h3p h3s h3two
    (fun j => h02_mono L h13 (z j)) (h02_mono L h13 z0) hz3 hzV3 hV03
  have hwv : ∀ j, (inverse e hκ he (1/3) h3p.le h3two
      (⟨h02_mono L h13 (z j), hzV3 j⟩ : Target (L := L) V (1/3) h3p.le)).val =
      (inverse e hκ he 1 h0 one_le_two (⟨z j, hzV j⟩ : Target (L := L) V 1 h0)).val :=
    fun j => QuantumNLS.Reg011HInverseMid.inverse_mono_val hκ e he 1 h0 h13 one_le_two (z j)
      (hzV j) (hzV3 j)
  have hwv0 : (inverse e hκ he (1/3) h3p.le h3two
      (⟨h02_mono L h13 z0, hV03⟩ : Target (L := L) V (1/3) h3p.le)).val =
      (inverse e hκ he 1 h0 one_le_two (⟨z0, hV0⟩ : Target (L := L) V 1 h0)).val :=
    QuantumNLS.Reg011HInverseMid.inverse_mono_val hκ e he 1 h0 h13 one_le_two z0 hV0 hV03
  have hL2 : Tendsto (fun j => (inverse e hκ he 1 h0 one_le_two
      (⟨z j, hzV j⟩ : Target (L := L) V 1 h0)).val) atTop
      (𝓝 (inverse e hκ he 1 h0 one_le_two (⟨z0, hV0⟩ : Target (L := L) V 1 h0)).val) := by
    have hl := inverse_val e hκ he 1 h0 one_le_two (⟨z0, hV0⟩ : Target (L := L) V 1 h0)
    rw [hl]
    exact (QuantumNLS.Reg011HReverseMoment.inverse_tendsto e 1 h0 z z0 hz hzV hV0).congr
      (fun j => (inverse_val e hκ he 1 h0 one_le_two
        (⟨z j, hzV j⟩ : Target (L := L) V 1 h0)).symm)
  have hphys : Tendsto (fun j => ∫ t : ℝ, |t| ^ (2 * (1:ℝ))
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he 1 h0 one_le_two
        (⟨z j, hzV j⟩ : Target (L := L) V 1 h0)).val)) atTop
      (𝓝 (∫ t : ℝ, |t| ^ (2 * (1:ℝ))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he 1 h0 one_le_two
          (⟨z0, hV0⟩ : Target (L := L) V 1 h0)).val))) := by
    rw [inverse_val e hκ he 1 h0 one_le_two (⟨z0, hV0⟩ : Target (L := L) V 1 h0)]
    exact (QuantumNLS.Reg011HReverseMoment.moment_tendsto hκ e he 1 zero_lt_one one_le_two
      z z0 hz hzV hV0).congr (fun j => by
        rw [inverse_val e hκ he 1 h0 one_le_two (⟨z j, hzV j⟩ : Target (L := L) V 1 h0)])
  have hR := R1_tendsto_of_third κ
    (fun j => inverse e hκ he 1 h0 one_le_two (⟨z j, hzV j⟩ : Target (L := L) V 1 h0))
    (inverse e hκ he 1 h0 one_le_two (⟨z0, hV0⟩ : Target (L := L) V 1 h0))
    (fun j => inverse e hκ he (1/3) h3p.le h3two
      (⟨h02_mono L h13 (z j), hzV3 j⟩ : Target (L := L) V (1/3) h3p.le))
    (inverse e hκ he (1/3) h3p.le h3two
      (⟨h02_mono L h13 z0, hV03⟩ : Target (L := L) V (1/3) h3p.le))
    hw3 (fun j => (hwv j).symm) hwv0.symm
  exact inverse_one_core κ hκ _ _ hL2 hphys hR

/-! ### 1 < s < 2 -/

/-- Printed upper identity, transferred to the H¹ representative with the same L² vector. -/
theorem upper_identity (hκ : 0 < κ) (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (v : H02 L 1) (u : H02 L s) (h : v.val = u.val)
    (hμ : Integrable (fun x : ℝ => |x| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val))
    (hν : Integrable (fun x : ℝ => |x| ^ (2 * s)) (QuantumNLS.FreeLimit.freeMeasure L u.val)) :
    (∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
      (∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L u.val)) =
      (2 * Real.sin (Real.pi * (s - 1)) / Real.pi) *
        QuantumNLS.TerraMultiRound75Correction.correction κ hκ s (toHk1 (L := L) v) := by
  have h2 := QuantumNLS.TerraMultiRound78UpperPrinted.physical_free_upper_printed κ hκ
    (toHk1 (L := L) v) s hs1 hs2
    (by rw [toHk1_val, h]; exact hμ) (by rw [toHk1_val, h]; exact hν)
  rw [toHk1_val, h] at h2
  linarith

/-- Abstract 1 < s < 2 step: the H¹ representatives t_j of the same L² vectors as u_j. -/
theorem inverse_mid_upper_core (κ : ℝ) (hκ : 0 < κ) (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2)
    (u : ℕ → H02 L s) (u0 : H02 L s) (t : ℕ → H02 L 1) (t0 : H02 L 1)
    (ht : Tendsto t atTop (𝓝 t0)) (htu : ∀ j, (t j).val = (u j).val) (ht0 : t0.val = u0.val)
    (hL2 : Tendsto (fun j => (u j).val) atTop (𝓝 u0.val))
    (hphys : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2 * s)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j).val)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u0.val))))
    (hμ : ∀ j, Integrable (fun x : ℝ => |x| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j).val))
    (hν : ∀ j, Integrable (fun x : ℝ => |x| ^ (2 * s)) (QuantumNLS.FreeLimit.freeMeasure L (u j).val))
    (hμ0 : Integrable (fun x : ℝ => |x| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ u0.val))
    (hν0 : Integrable (fun x : ℝ => |x| ^ (2 * s)) (QuantumNLS.FreeLimit.freeMeasure L u0.val)) :
    Tendsto u atTop (𝓝 u0) := by
  have hs0 : (0:ℝ) ≤ s := by linarith
  have hc : Tendsto (fun j => QuantumNLS.TerraMultiRound75Correction.correction κ hκ s
      (toHk1 (L := L) (t j))) atTop
      (𝓝 (QuantumNLS.TerraMultiRound75Correction.correction κ hκ s (toHk1 (L := L) t0))) :=
    ((QuantumNLS.TerraMultiRound75Correction.correction_continuous (L := L) κ hκ s hs1 hs2).tendsto
      _).comp (((toHk1 (L := L)).continuous.tendsto t0).comp ht)
  have hcm := hc.const_mul (2 * Real.sin (Real.pi * (s - 1)) / Real.pi)
  have hpt := hphys.sub hcm
  have key0 := upper_identity hκ s hs1 hs2 t0 u0 ht0 hμ0 hν0
  have hfree : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2 * s)
        ∂(QuantumNLS.FreeLimit.freeMeasure L (u j).val)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L u0.val))) := by
    have hlim : (∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u0.val)) -
        (2 * Real.sin (Real.pi * (s - 1)) / Real.pi) *
          QuantumNLS.TerraMultiRound75Correction.correction κ hκ s (toHk1 (L := L) t0) =
        ∫ x : ℝ, |x| ^ (2 * s) ∂(QuantumNLS.FreeLimit.freeMeasure L u0.val) := by
      linarith [key0]
    rw [← hlim]
    refine hpt.congr (fun j => ?_)
    have hj := upper_identity hκ s hs1 hs2 (t j) (u j) (htu j) (hμ j) (hν j)
    linarith
  have hn := QuantumNLS.Reg011HInverseMid.norm_sq_tendsto_of_free hs0 u u0 hL2 hfree
  exact QuantumNLS.Reg011HSobolevConvergence.H02_tendsto_of_L2_and_norm u u0 hL2 hn

/-- **1 < s < 2 inverse continuity.** -/
theorem inverse_mid_upper_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : 1 < s) (hs2 : s < 2)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs0 (z j) ∈ V) (hV0 : toBase (L := L) s hs0 z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he s hs0 hs2.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0))
      atTop (𝓝 (inverse e hκ he s hs0 hs2.le (⟨z0, hV0⟩ : Target (L := L) V s hs0))) := by
  have h0 : (0:ℝ) ≤ 1 := zero_le_one
  have h12 : (1:ℝ) ≤ s := hs1.le
  have hy : Tendsto (fun j => h02_mono L h12 (z j)) atTop (𝓝 (h02_mono L h12 z0)) :=
    ((h02_mono L h12).continuous.tendsto z0).comp hz
  have hyV : ∀ j, toBase (L := L) 1 zero_le_one (h02_mono L h12 (z j)) ∈ V := fun j => by
    rw [toBase_mono_gen zero_le_one hs0 h12 (z j)]
    exact hzV j
  have hyV0 : toBase (L := L) 1 zero_le_one (h02_mono L h12 z0) ∈ V := by
    rw [toBase_mono_gen zero_le_one hs0 h12 z0]
    exact hV0
  have ht := inverse_one_tendsto hκ e he (fun j => h02_mono L h12 (z j)) (h02_mono L h12 z0)
    hy hyV hyV0
  have htu : ∀ j, (inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 (z j), hyV j⟩ : Target (L := L) V 1 zero_le_one)).val =
      (inverse e hκ he s hs0 hs2.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val :=
    fun j => inverse_mono_one_val hκ e he s hs0 h12 hs2.le (z j) (hzV j) (hyV j)
  have ht0 : (inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 z0, hyV0⟩ : Target (L := L) V 1 zero_le_one)).val =
      (inverse e hκ he s hs0 hs2.le (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val :=
    inverse_mono_one_val hκ e he s hs0 h12 hs2.le z0 hV0 hyV0
  have hu := QuantumNLS.Reg011HReverseMoment.inverse_tendsto e s hs0 z z0 hz hzV hV0
  have hL2 : Tendsto (fun j => (inverse e hκ he s hs0 hs2.le
      (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val) atTop
      (𝓝 (inverse e hκ he s hs0 hs2.le (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val) := by
    have hl := inverse_val e hκ he s hs0 hs2.le (⟨z0, hV0⟩ : Target (L := L) V s hs0)
    rw [hl]
    exact hu.congr (fun j => (inverse_val e hκ he s hs0 hs2.le
      (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).symm)
  have hphys : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2 * s)
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0 hs2.le
        (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2 * s)
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0 hs2.le
          (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val))) := by
    rw [inverse_val e hκ he s hs0 hs2.le (⟨z0, hV0⟩ : Target (L := L) V s hs0)]
    exact (QuantumNLS.Reg011HReverseMoment.moment_tendsto hκ e he s
      (by linarith : (0:ℝ) < s) hs2.le z z0 hz hzV hV0).congr (fun j => by
        rw [inverse_val e hκ he s hs0 hs2.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0)])
  have hsp : (0:ℝ) < s := by linarith
  have hμ : ∀ j, Integrable (fun x : ℝ => |x| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0 hs2.le
        (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val) := by
    intro j
    rw [inverse_val e hκ he s hs0 hs2.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0)]
    exact (QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ _ s
      hsp).mpr (QuantumNLS.Reg011HReverseMoment.masses_summable hκ e he s hs0 (z j) (hzV j))
  have hμ0 : Integrable (fun x : ℝ => |x| ^ (2 * s))
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he s hs0 hs2.le
        (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val) := by
    rw [inverse_val e hκ he s hs0 hs2.le (⟨z0, hV0⟩ : Target (L := L) V s hs0)]
    exact (QuantumNLS.TerraMultiRound77ActionCriteria.physical_power_iff_indexed_actions hκ _ s
      hsp).mpr (QuantumNLS.Reg011HReverseMoment.masses_summable hκ e he s hs0 z0 hV0)
  have hν : ∀ j, Integrable (fun x : ℝ => |x| ^ (2 * s))
      (QuantumNLS.FreeLimit.freeMeasure L (inverse e hκ he s hs0 hs2.le
        (⟨z j, hzV j⟩ : Target (L := L) V s hs0)).val) :=
    fun j => QuantumNLS.TerraMultiRound77FreeContinuity.free_power_integrable (L := L) s hs0 _
  have hν0 : Integrable (fun x : ℝ => |x| ^ (2 * s))
      (QuantumNLS.FreeLimit.freeMeasure L (inverse e hκ he s hs0 hs2.le
        (⟨z0, hV0⟩ : Target (L := L) V s hs0)).val) :=
    QuantumNLS.TerraMultiRound77FreeContinuity.free_power_integrable (L := L) s hs0 _
  exact inverse_mid_upper_core κ hκ s hs1 hs2
    (fun j => inverse e hκ he s hs0 hs2.le (⟨z j, hzV j⟩ : Target (L := L) V s hs0))
    (inverse e hκ he s hs0 hs2.le (⟨z0, hV0⟩ : Target (L := L) V s hs0))
    (fun j => inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 (z j), hyV j⟩ : Target (L := L) V 1 zero_le_one))
    (inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 z0, hyV0⟩ : Target (L := L) V 1 zero_le_one))
    ht htu ht0 hL2 hphys hμ hν hμ0 hν0

/-! ### s = 2 -/

/-- Printed finite field identity at order 2, transferred to H¹ (frozen finite_field_identity). -/
theorem two_identity (hκ : 0 < κ) (u : H02 L 2) (v : H02 L 1) (h : v.val = u.val) :
    ∫ x : ℝ, |x| ^ (2 * (2:ℝ)) ∂(QuantumNLS.FreeLimit.freeMeasure L u.val) =
      (∫ x : ℝ, |x| ^ (2 * (2:ℝ)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u.val)) -
        QuantumNLS.TerraMultiRound59RCompatibility.Rfield (L := L) 2 le_rfl κ
          (toHk21 (L := L) v) := by
  have hid := QuantumNLS.TerraMultiRound64FieldIdentity.finite_field_identity (L := L) κ hκ 2
    le_rfl (toHk21 (L := L) v) (by
      have h2 := QuantumNLS.TerraMultiRound64FieldIdentity.representative_hsq 2
        (toHk2 (L := L) u)
      rw [toHk2_val] at h2
      rw [toHk21_val, h]
      exact h2)
  rw [toHk21_val, h] at hid
  rw [free_rpow_two, ← integral_two_eq, hid]
  ring

/-- Abstract s = 2 step. -/
theorem inverse_two_core (κ : ℝ) (hκ : 0 < κ) (u : ℕ → H02 L 2) (u0 : H02 L 2)
    (t : ℕ → H02 L 1) (t0 : H02 L 1)
    (ht : Tendsto t atTop (𝓝 t0)) (htu : ∀ j, (t j).val = (u j).val) (ht0 : t0.val = u0.val)
    (hL2 : Tendsto (fun j => (u j).val) atTop (𝓝 u0.val))
    (hphys : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2 * (2:ℝ))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (u j).val)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2 * (2:ℝ))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u0.val)))) :
    Tendsto u atTop (𝓝 u0) := by
  have hR : Tendsto (fun j => QuantumNLS.TerraMultiRound59RCompatibility.Rfield (L := L) 2 le_rfl κ
      (toHk21 (L := L) (t j))) atTop
      (𝓝 (QuantumNLS.TerraMultiRound59RCompatibility.Rfield (L := L) 2 le_rfl κ
        (toHk21 (L := L) t0))) :=
    ((QuantumNLS.TerraMultiRound59RCompatibility.Rfield_continuous (L := L) 2 le_rfl κ).tendsto
      _).comp (((toHk21 (L := L)).continuous.tendsto t0).comp ht)
  have hpt := hphys.sub hR
  have hlim : (∫ x : ℝ, |x| ^ (2 * (2:ℝ)) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u0.val)) -
      QuantumNLS.TerraMultiRound59RCompatibility.Rfield (L := L) 2 le_rfl κ
        (toHk21 (L := L) t0) =
      ∫ x : ℝ, |x| ^ (2 * (2:ℝ)) ∂(QuantumNLS.FreeLimit.freeMeasure L u0.val) := by
    have hid0 := two_identity hκ u0 t0 ht0
    linarith
  have hfree : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2 * (2:ℝ))
        ∂(QuantumNLS.FreeLimit.freeMeasure L (u j).val)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2 * (2:ℝ)) ∂(QuantumNLS.FreeLimit.freeMeasure L u0.val))) := by
    rw [← hlim]
    refine hpt.congr (fun j => ?_)
    have hj := two_identity hκ (u j) (t j) (htu j)
    linarith
  have hn := QuantumNLS.Reg011HInverseMid.norm_sq_tendsto_of_free (by norm_num : (0:ℝ) ≤ 2) u u0
    hL2 hfree
  exact QuantumNLS.Reg011HSobolevConvergence.H02_tendsto_of_L2_and_norm u u0 hL2 hn

/-- **s = 2 inverse continuity.** -/
theorem inverse_two_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (z : ℕ → h02 L 2) (z0 : h02 L 2) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) 2 zero_le_two (z j) ∈ V)
    (hV0 : toBase (L := L) 2 zero_le_two z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he 2 zero_le_two le_rfl (⟨z j, hzV j⟩ : Target (L := L) V 2 zero_le_two))
      atTop (𝓝 (inverse e hκ he 2 zero_le_two le_rfl (⟨z0, hV0⟩ : Target (L := L) V 2 zero_le_two))) := by
  have h0 : (0:ℝ) ≤ 1 := zero_le_one
  have h12 : (1:ℝ) ≤ 2 := one_le_two
  have hy : Tendsto (fun j => h02_mono L h12 (z j)) atTop (𝓝 (h02_mono L h12 z0)) :=
    ((h02_mono L h12).continuous.tendsto z0).comp hz
  have hyV : ∀ j, toBase (L := L) 1 zero_le_one (h02_mono L h12 (z j)) ∈ V := fun j => by
    rw [toBase_mono_gen zero_le_one zero_le_two h12 (z j)]
    exact hzV j
  have hyV0 : toBase (L := L) 1 zero_le_one (h02_mono L h12 z0) ∈ V := by
    rw [toBase_mono_gen zero_le_one zero_le_two h12 z0]
    exact hV0
  have ht := inverse_one_tendsto hκ e he (fun j => h02_mono L h12 (z j)) (h02_mono L h12 z0)
    hy hyV hyV0
  have htu : ∀ j, (inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 (z j), hyV j⟩ : Target (L := L) V 1 zero_le_one)).val =
      (inverse e hκ he 2 zero_le_two le_rfl (⟨z j, hzV j⟩ : Target (L := L) V 2 zero_le_two)).val :=
    fun j => inverse_mono_one_val hκ e he 2 zero_le_two h12 le_rfl (z j) (hzV j) (hyV j)
  have ht0 : (inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 z0, hyV0⟩ : Target (L := L) V 1 zero_le_one)).val =
      (inverse e hκ he 2 zero_le_two le_rfl (⟨z0, hV0⟩ : Target (L := L) V 2 zero_le_two)).val :=
    inverse_mono_one_val hκ e he 2 zero_le_two h12 le_rfl z0 hV0 hyV0
  have hu := QuantumNLS.Reg011HReverseMoment.inverse_tendsto e 2 zero_le_two z z0 hz hzV hV0
  have hL2 : Tendsto (fun j => (inverse e hκ he 2 zero_le_two le_rfl
      (⟨z j, hzV j⟩ : Target (L := L) V 2 zero_le_two)).val) atTop
      (𝓝 (inverse e hκ he 2 zero_le_two le_rfl (⟨z0, hV0⟩ : Target (L := L) V 2 zero_le_two)).val) := by
    have hl := inverse_val e hκ he 2 zero_le_two le_rfl
      (⟨z0, hV0⟩ : Target (L := L) V 2 zero_le_two)
    rw [hl]
    exact hu.congr (fun j => (inverse_val e hκ he 2 zero_le_two le_rfl
      (⟨z j, hzV j⟩ : Target (L := L) V 2 zero_le_two)).symm)
  have hphys : Tendsto (fun j => ∫ x : ℝ, |x| ^ (2 * (2:ℝ))
      ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he 2 zero_le_two le_rfl
        (⟨z j, hzV j⟩ : Target (L := L) V 2 zero_le_two)).val)) atTop
      (𝓝 (∫ x : ℝ, |x| ^ (2 * (2:ℝ))
        ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ (inverse e hκ he 2 zero_le_two le_rfl
          (⟨z0, hV0⟩ : Target (L := L) V 2 zero_le_two)).val))) := by
    rw [inverse_val e hκ he 2 zero_le_two le_rfl (⟨z0, hV0⟩ : Target (L := L) V 2 zero_le_two)]
    exact (QuantumNLS.Reg011HReverseMoment.moment_tendsto hκ e he 2 (by norm_num) le_rfl z z0 hz
      hzV hV0).congr (fun j => by
        rw [inverse_val e hκ he 2 zero_le_two le_rfl (⟨z j, hzV j⟩ : Target (L := L) V 2 zero_le_two)])
  exact inverse_two_core κ hκ
    (fun j => inverse e hκ he 2 zero_le_two le_rfl (⟨z j, hzV j⟩ : Target (L := L) V 2 zero_le_two))
    (inverse e hκ he 2 zero_le_two le_rfl (⟨z0, hV0⟩ : Target (L := L) V 2 zero_le_two))
    (fun j => inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 (z j), hyV j⟩ : Target (L := L) V 1 zero_le_one))
    (inverse e hκ he 1 zero_le_one one_le_two
      (⟨h02_mono L h12 z0, hyV0⟩ : Target (L := L) V 1 zero_le_one))
    ht htu ht0 hL2 hphys

/-! ### Combined upper inverse continuity, 1 ≤ s ≤ 2 -/

/-- **REG-011 upper inverse continuity, 1 ≤ s ≤ 2.** REG-010 pending review. -/
theorem inverse_upper_tendsto (hκ : 0 < κ) (e : L2T L ≃ₜ V) (he : ExactModuli e hκ)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : 1 ≤ s) (hs2 : s ≤ 2)
    (z : ℕ → h02 L s) (z0 : h02 L s) (hz : Tendsto z atTop (𝓝 z0))
    (hzV : ∀ j, toBase (L := L) s hs0 (z j) ∈ V) (hV0 : toBase (L := L) s hs0 z0 ∈ V) :
    Tendsto (fun j => inverse e hκ he s hs0 hs2 (⟨z j, hzV j⟩ : Target (L := L) V s hs0))
      atTop (𝓝 (inverse e hκ he s hs0 hs2 (⟨z0, hV0⟩ : Target (L := L) V s hs0))) := by
  rcases hs1.eq_or_lt with h1 | h1
  · subst h1
    exact inverse_one_tendsto hκ e he z z0 hz hzV hV0
  · rcases hs2.eq_or_lt with h2 | h2
    · subst h2
      exact inverse_two_tendsto hκ e he z z0 hz hzV hV0
    · exact inverse_mid_upper_tendsto hκ e he s hs0 h1 h2 z z0 hz hzV hV0

#print axioms abs_rpow_two
#print axioms R1_eq_third
#print axioms inverse_one_core
#print axioms inverse_one_tendsto
#print axioms upper_identity
#print axioms inverse_mid_upper_core
#print axioms inverse_mid_upper_tendsto
#print axioms two_identity
#print axioms inverse_two_core
#print axioms inverse_two_tendsto
#print axioms inverse_upper_tendsto
end QuantumNLS.Reg011HInverseUpper
