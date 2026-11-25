import NlsGge.Spectral.ChargeJensenSobolev38
import NlsGge.Spectral.F04EnergyIdentity38

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-- Parseval for the actual finite Fourier truncation, at every finite derivative order. -/
theorem chargeQuad_trunc_derivative38 (r : ℝ) (j N : ℕ) (y : SobolevHilbert r) :
    chargeQuad38 r j (truncSobolev38 r N y) =
      ∫ t in (0 : ℝ)..1, ‖iteratedDeriv j (truncField38 r N y) t‖ ^ 2 := by
  rw [(smoothDerivative_parseval38 j (truncField38 r N y)
    (contDiff_truncField38 r N y) (periodic_truncField38 r N y)).2]
  unfold chargeQuad38
  refine tsum_congr fun n => ?_
  rw [truncSobolev38_link r N y n, two_pi_abs_pow_even38]

/-- The stronger finite-plane Jensen lower bound keeps the derivative quadratic term. -/
theorem chargeTwo_trunc_ge_quad_add_mass_sq38 (N : ℕ) (y : SobolevHilbert ((1 : ℕ) : ℝ)) :
    chargeQuad38 ((1 : ℕ) : ℝ) 1 (truncSobolev38 ((1 : ℕ) : ℝ) N y) +
      (chargeSobolev38 2 0 (truncSobolev38 ((1 : ℕ) : ℝ) N y)) ^ 2 ≤
        chargeSobolev38 2 1 (truncSobolev38 ((1 : ℕ) : ℝ) N y) := by
  let z : FourierPlane N := fun i => (show WeightedHilbert (sobolevModeWeight ((1 : ℕ) : ℝ)) from y) (modeIndex N i)
  rw [chargeQuad_trunc_derivative38 ((1 : ℕ) : ℝ) 1 N y,
    chargeSobolev38_trunc 2 0 (by norm_num) (by norm_num),
    chargeSobolev38_trunc 2 1 (by norm_num) (by norm_num)]
  change (∫ t in (0 : ℝ)..1, ‖iteratedDeriv 1 (planeReal N z) t‖ ^ 2) +
    (localCharge38 (planeReal N z) 0) ^ 2 ≤ localCharge38 (planeReal N z) 1
  simp only [iteratedDeriv_one, deriv_planeReal]
  have hd : IntervalIntegrable
      (fun x : ℝ => ‖planeReal N (derivativePlane N z) x‖ ^ 2) volume 0 1 :=
    ((continuous_planeReal38 N (derivativePlane N z)).norm.pow 2).intervalIntegrable _ _
  have hq : IntervalIntegrable
      (fun x : ℝ => ‖planeReal N z x‖ ^ 4) volume 0 1 :=
    ((continuous_planeReal38 N z).norm.pow 4).intervalIntegrable _ _
  rw [planeQ2_local38, intervalIntegral.integral_add hd hq]
  exact add_le_add le_rfl (planeMass_sq_le_quartic38 N z)

/-- Every actual H1 carrier satisfies the source `Q2 >= derivative energy + mass squared`. -/
theorem chargeTwo_ge_quad_add_mass_sq38 (y : SobolevHilbert ((1 : ℕ) : ℝ)) :
    chargeQuad38 ((1 : ℕ) : ℝ) 1 y + (chargeSobolev38 2 0 y) ^ 2 ≤ chargeSobolev38 2 1 y := by
  have hl : Continuous (fun x : SobolevHilbert ((1 : ℕ) : ℝ) =>
      chargeQuad38 ((1 : ℕ) : ℝ) 1 x + (chargeSobolev38 2 0 x) ^ 2) :=
    (continuous_chargeQuad38 1 1 le_rfl).add
      ((continuous_chargeSobolev38 2 0 (by norm_num)).pow 2)
  have hr := continuous_chargeSobolev38 2 1 (by norm_num)
  exact le_of_tendsto_of_tendsto'
    (hl.continuousAt.tendsto.comp (tendsto_truncSobolev38 ((1 : ℕ) : ℝ) y))
    (hr.continuousAt.tendsto.comp (tendsto_truncSobolev38 ((1 : ℕ) : ℝ) y))
    (fun N => chargeTwo_trunc_ge_quad_add_mass_sq38 N y)

end NlsGge.GK38.MolnarBounds38
