import NlsGge.Birkhoff.F11Claim38c
import NlsGge.Birkhoff.S03Measure38c
import NlsGge.Birkhoff.W10Localized38g

/-! # NEW-F11 (`F:cor:charge`), file 4: continuity, nonnegativity and measurability of the local charge (NEW-F11.05)

Source: `paper/v2.tex` l.1817 ("The charge `Q_{2j}` is continuous on `H^j` and nonnegative").
`B`-free.

`Q_{2j}` is the realized charge functional of the project: `chargeSobolev38 m j` on `H^{m-1}` (the continuous
extension of the local charge `∫ (-1)^{j+1} u p_{2j+1}`, F03/F04) and `chargeFn38 m j` on `L²` (cleaned off `H^{m-1}`).

* `chargeSobolev38_nonneg` : `Q_{2j} ≥ 0` on `H^{m-1}` (`2 ≤ m`, `j ≤ m-1`; by density of Fourier truncations and
  `localCharge38_plane_nonneg`);
* `continuous_charge_Hj38` : for `j ≥ 1`, `Q_{2j} = chargeSobolev38 (j+1) j` is continuous and nonnegative on `H^j`;
* `measurable_chargeFn38` : `chargeFn38 m j` is a (Borel) measurable function on `L²`;
* `continuous_chargeFn_physOfCarrier38` : `y ↦ chargeFn38 m j (𝓕⁻¹ y)` is continuous on the Birkhoff carrier `h^{m-1}`
  (the reflected Fourier sign `reflect38` is an isometry of `h^{m-1}`), which is the form of the test functions of
  NEW-F09 (`F ∘ physOfCarrier38 r`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.HierarchyRiccati Filter Topology
open scoped ENNReal Real ContDiff

/-- **`Q_{2j} ≥ 0` on `H^{m-1}`.** -/
theorem chargeSobolev38_nonneg (m j : ℕ) (hm : 2 ≤ m) (hj : j ≤ m - 1)
    (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) : 0 ≤ chargeSobolev38 m j y := by
  have hc := continuous_chargeSobolev38 m j hj
  refine ge_of_tendsto (hc.continuousAt.tendsto.comp (tendsto_truncSobolev38 _ y))
    (Filter.Eventually.of_forall fun N => ?_)
  simp only [Function.comp]
  rw [chargeSobolev38_trunc m j hm (by omega) N y]
  exact localCharge38_plane_nonneg N _ j

theorem chargeFn38_nonneg (m j : ℕ) (hm : 2 ≤ m) (hj : j ≤ m - 1) (u : PhysicalL2) :
    0 ≤ chargeFn38 m j u :=
  chargeSobolev38_nonneg m j hm hj _

/-- **NEW-F11.05.** For `j ≥ 1`, `Q_{2j}` is continuous and nonnegative on `H^j`. -/
theorem continuous_charge_Hj38 (j : ℕ) (hj : 1 ≤ j) :
    Continuous (chargeSobolev38 (j + 1) j) ∧
      ∀ y : SobolevHilbert (((j + 1 - 1 : ℕ)) : ℝ), 0 ≤ chargeSobolev38 (j + 1) j y :=
  ⟨continuous_chargeSobolev38 (j + 1) j (by omega),
    fun y => chargeSobolev38_nonneg (j + 1) j (by omega) (by omega) y⟩

theorem measurable_chargeFn38 (m j : ℕ) (hj : j ≤ m - 1) : Measurable (chargeFn38 m j) := by
  let _ : MeasurableSpace (SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevCarrier38 ((m - 1 : ℕ) : ℝ)) := ⟨rfl⟩
  let _ : MeasurableSpace (SobolevHilbert ((m - 1 : ℕ) : ℝ)) := borel _
  have : BorelSpace (SobolevHilbert ((m - 1 : ℕ) : ℝ)) := ⟨rfl⟩
  exact (continuous_chargeSobolev38 m j hj).measurable.comp
    ((continuous_ofCarrier38 _).measurable.comp (measurable_physC38 (m - 1)))

/-! ### The reflection `(Ry)_n = -y_{-n}` is an isometry of `h^r` -/

/-- The reflection `y ↦ (-y_{-n})_n` of the carrier `h^r`. -/
def reflCF11_38 (r : ℝ) : SobolevCarrier38 r → SobolevCarrier38 r :=
  carrierMap38 r r reflect38 (fun _ hx => reflect38_mem hx)

theorem carrierCoe38_reflCF11_38 (r : ℝ) (y : SobolevCarrier38 r) :
    carrierCoe38 r (reflCF11_38 r y) = reflect38 (carrierCoe38 r y) := rfl

theorem norm_reflCF11_38_sub (r : ℝ) (x y : SobolevCarrier38 r) :
    ‖reflCF11_38 r x - reflCF11_38 r y‖ = ‖x - y‖ := by
  have h1 := (carrier_hasSum_norm_sq38 r (reflCF11_38 r x - reflCF11_38 r y)).tsum_eq
  have h2 := (carrier_hasSum_norm_sq38 r (x - y)).tsum_eq
  have h3 : ∑' n : ℤ, sobolevModeWeight r n *
      ‖carrierCoe38 r (reflCF11_38 r x - reflCF11_38 r y) n‖ ^ 2 =
      ∑' n : ℤ, sobolevModeWeight r n * ‖carrierCoe38 r (x - y) n‖ ^ 2 := by
    rw [← tsum_comp_neg (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r (x - y) n‖ ^ 2)]
    refine tsum_congr (fun n => ?_)
    have e : carrierCoe38 r (reflCF11_38 r x - reflCF11_38 r y) n = -(carrierCoe38 r (x - y) (-n)) := by
      show -(carrierCoe38 r x (-n)) - -(carrierCoe38 r y (-n)) =
        -(carrierCoe38 r x (-n) - carrierCoe38 r y (-n))
      ring
    rw [e, norm_neg, sobolevModeWeight_neg]
  have h4 : ‖reflCF11_38 r x - reflCF11_38 r y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [← h1, ← h2, h3]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h4

theorem continuous_reflCF11_38 (r : ℝ) : Continuous (reflCF11_38 r) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => ?_)).continuous
  rw [dist_eq_norm, dist_eq_norm, norm_reflCF11_38_sub]
  simp

/-- `physC38 k (𝓕⁻¹ y) = R y`: the physical Fourier carrier of `𝓕⁻¹ y` is the reflection of `y`. -/
theorem physC38_physOfCarrier38 (k : ℕ) (y : SobolevCarrier38 (k : ℝ)) :
    physC38 k (physOfCarrier38 (k : ℝ) (Nat.cast_nonneg k) y) = reflCF11_38 (k : ℝ) y := by
  set u := physOfCarrier38 (k : ℝ) (Nat.cast_nonneg k) y with hu
  have hF : (fun n => physicalFourier u n) = reflect38 (carrierCoe38 (k : ℝ) y) := by
    funext n
    rw [physicalFourier_eq_neg_fourierSeq38, hu]
    unfold physOfCarrier38
    rw [fourierSeq38_physInv38]
    rfl
  have hmem : (fun n => physicalFourier u n) ∈ seqSobolev38 (k : ℝ) := by
    rw [hF]; exact reflect38_mem (carrierCoe38_mem _ y)
  rw [physC38_of_mem k u hmem]
  exact carrierExt38 (by rw [carrierCoe38_mk, carrierCoe38_reflCF11_38, hF])

/-- `y ↦ Q_{2j}(𝓕⁻¹ y)` is continuous on the Birkhoff carrier `h^{m-1}` (the form of NEW-F09's test functions). -/
theorem continuous_chargeFn_physOfCarrier38 (m j : ℕ) (hj : j ≤ m - 1) :
    Continuous (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
      chargeFn38 m j (physOfCarrier38 ((m - 1 : ℕ) : ℝ) (Nat.cast_nonneg _) y)) := by
  have : (fun y : SobolevCarrier38 ((m - 1 : ℕ) : ℝ) =>
      chargeFn38 m j (physOfCarrier38 ((m - 1 : ℕ) : ℝ) (Nat.cast_nonneg _) y)) =
      (chargeSobolev38 m j) ∘ (ofCarrier38 _) ∘ (reflCF11_38 ((m - 1 : ℕ) : ℝ)) :=
    funext fun y => by
      simp only [Function.comp, chargeFn38, physC38_physOfCarrier38]
  rw [this]
  exact (continuous_chargeSobolev38 m j hj).comp
    ((continuous_ofCarrier38 _).comp (continuous_reflCF11_38 _))

end NlsGge.Birkhoff
end
