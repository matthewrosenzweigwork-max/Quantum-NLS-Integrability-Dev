import Mathlib
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.TauGamma
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.Lib.ParamProductsRoot
import NlsGge.ThirdConsultation.G4.G4018Support4
import NlsGge.ThirdConsultation.G4.G4018Support5
/- H215_PERTERM01 (proof development, AUTHOR; not self-reviewed). Pro round 9 section 10, step 3 (G4-018).
   One omitted factor of the disc estimate: for j != n, z in the open n-th disc, and sigma = tau_j + gamma_j A
   (the G2-074 equation, here as a hypothesis on A), the factor (sigma - z)/w_j - 1, with w_j the standard root,
   satisfies |.| <= |gamma_j A|/t + |gamma_j|^2/(4 t^2), where t = c^-1 |j-n| > 0 is the separation constant
   from IsolatingGeometry38. Uses only the separation lemmas and the root-deviation estimate. -/
set_option autoImplicit false

open Set Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.G4018Support

theorem perterm_bound (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (hspec : IsolatingSpectral38 φ C R) (n j : ℤ) (hj : j ≠ n)
    (z : ℂ) (hz : z ∈ ball (C n) (R n)) (σ A : ℂ) (hσ : σ = tauN φ j + gamma2 φ j * A) :
    ‖(σ - z) / stdRoot38 (tauN φ j) (gamma2 φ j) z - 1‖ ≤
      ‖gamma2 φ j * A‖ / (c⁻¹ * |((j - n : ℤ) : ℝ)|) +
        ‖gamma2 φ j‖ / (4 * (c⁻¹ * |((j - n : ℤ) : ℝ)|) ^ 2) := by
  have hc : 1 ≤ c := hgeom.2.2.1
  have hcpos : 0 < c := by linarith
  have hjne : ((j - n : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (sub_ne_zero.mpr hj)
  have ht : 0 < c⁻¹ * |((j - n : ℤ) : ℝ)| :=
    mul_pos (inv_pos.mpr hcpos) (abs_pos.mpr hjne)
  obtain ⟨hv, ha, hb⟩ := sep_lower_all φ hφ C R c N hgeom hspec j n hj z hz
  have hv0 : tauN φ j - z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    linarith
  have hτ : tauN φ j = (lamMinus φ j + lamPlus φ j) / 2 := by
    rw [tauN_value38 φ hφ j]
    ring
  have hg : gamma2 φ j = (lamPlus φ j - lamMinus φ j) ^ 2 := gamma2_value38 φ hφ j
  have hw : c⁻¹ * |((j - n : ℤ) : ℝ)| ≤ ‖stdRoot38 (tauN φ j) (gamma2 φ j) z‖ :=
    stdRoot_norm_lower (lamMinus φ j) (lamPlus φ j) (tauN φ j) (gamma2 φ j) z _ ht.le hτ hg hv0 ha hb
  have hwv := stdRoot_sub_tau_le (tauN φ j) (gamma2 φ j) z hv0
  have key := ratio_sub_one_le (tauN φ j - z) (gamma2 φ j * A) (gamma2 φ j)
    (stdRoot38 (tauN φ j) (gamma2 φ j) z) (c⁻¹ * |((j - n : ℤ) : ℝ)|) ht hv hw hwv
  have hsum : (tauN φ j - z) + gamma2 φ j * A = σ - z := by
    rw [hσ]
    ring
  rw [hsum] at key
  exact key

end NlsGge.G4018Support
