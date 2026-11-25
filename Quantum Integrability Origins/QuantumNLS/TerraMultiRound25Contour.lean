import QuantumNLS.TerraMultiRound24SwapContour
import QuantumNLS.Local002Analytic

/-! Discharge the contour side conditions using the LOCAL-002 resolvent construction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round25
open QuantumNLS.Local002 QuantumNLS.LocalSpectral.Round24

variable {L κ r : ℝ}

/-- The perturbed resolvent exists and is uniformly bounded on every prescribed contour. -/
theorem contour_resolvent (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) :
    ∀ z ∈ sphere (center L n) r, ∃ R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧
      ‖R‖ ≤ r⁻¹ * (1 - qpar κ L r u)⁻¹ := by
  intro z hz
  have hz' : ‖z - (pm L n : ℂ)‖ = r := by
    simpa [center, mem_sphere_iff_norm] using hz
  obtain ⟨_, R, _, hR, _, hbound, _⟩ := perturbed_resolvent hyp hr hr2 n hz' u hq
  exact ⟨R, hR, hbound⟩

/-- Uniform resolvent bounds imply the operator-valued contour integrability. -/
theorem contour_integrable (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) :
    CircleIntegrable (fun z => resolvent L κ (u : ℝ → ℂ) (parity n) z) (center L n) r := by
  have hpos : 0 < 1 - qpar κ L r u := by linarith
  exact (continuousOn_resolvent _ (M := r⁻¹ * (1 - qpar κ L r u)⁻¹)
    (by positivity) (contour_resolvent hyp hr hr2 n u hq)).circleIntegrable hr.le

/-- The Riesz projection and dressed contour integral commute with the
anti-linear swap for every potential in the Neumann ball. -/
theorem contour_swap (hyp : FreeResolventHyp L κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : qpar κ L r u < 1) (x : H2 L) :
    rieszProj L κ (u : ℝ → ℂ) (parity n) n r (swapOp L x) =
      swapOp L (rieszProj L κ (u : ℝ → ℂ) (parity n) n r x) ∧
    dressedIntegral L κ (u : ℝ → ℂ) n r (swapOp L x) =
      swapOp L (dressedIntegral L κ (u : ℝ → ℂ) n r x) := by
  have hR : ∀ z ∈ sphere (center L n) r,
      (∃ R, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R) ∧
      (∃ R, IsResolvent L κ (u : ℝ → ℂ) (parity n) (conj z) R) := by
    intro z hz
    have hzc : conj z ∈ sphere (center L n) r := by
      rw [mem_sphere_iff_norm] at hz ⊢
      change ‖conj z - (pm L n : ℂ)‖ = r
      change ‖z - (pm L n : ℂ)‖ = r at hz
      rw [← Complex.conj_ofReal (pm L n), ← map_sub, Complex.norm_conj]
      exact hz
    exact ⟨(contour_resolvent hyp hr hr2 n u hq z hz).imp (fun _ h => h.1),
      (contour_resolvent hyp hr hr2 n u hq (conj z) hzc).imp (fun _ h => h.1)⟩
  have hi := contour_integrable hyp hr hr2 n u hq
  exact ⟨riesz_swap L κ _ _ n r hr.le hR hi x,
    dressed_swap L κ _ n r hr.le hR hi x⟩

end QuantumNLS.LocalSpectral.Round25
#print axioms QuantumNLS.LocalSpectral.Round25.contour_resolvent
#print axioms QuantumNLS.LocalSpectral.Round25.contour_integrable
#print axioms QuantumNLS.LocalSpectral.Round25.contour_swap
