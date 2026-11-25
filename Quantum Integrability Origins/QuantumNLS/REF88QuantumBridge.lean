import Mathlib
import QuantumNLS.F07StepsR6
import QuantumNLS.BetheLabels

/-!
# REF88QuantumBridge: the finite coupling identity for occupation arrays (R-EF8C2837, item (iii), finite side)

Source: `physical_cubic.tex` printed lines 245-250 and 288-290: "the exact finite identity in Proposition
`prop:finite-coupling-response` gives `K ∂_K ℰ_N = 2 ℰ_N - 2L ∫ Q_N W_N`" and "Integrating the exact finite coupling
identity over a compact interval of `K > 0` gives `K ∂_K ℰ = 𝒯`".

* `arrRoots_eq_root`: the ordered Bethe roots of an occupation array `m ∈ M_N` (accepted DEF-006 `arrRoots`, R-4C8D7C9E)
  are the smooth root map `BetheSmooth.root` at the logarithmic labels (the form in which the accepted R-3C2D6BAB
  `F07EnergyR6.intensive_response` is stated).
* `finiteE_hasDerivAt`: the accepted finite coupling identity transported to arrays: `K ↦ N⁻¹ ∑ q_i(K/N)²` has derivative
  `K⁻¹ (2 ℰ_N - 2L N⁻¹ ∑ q_i (B⁻¹ q)_i)` at every `K > 0` (`B` the Gaudin map at contact `K/N`).
-/

set_option autoImplicit false
noncomputable section

open Filter Topology

namespace QuantumNLS.REF88QuantumBridge

open QuantumNLS.BetheLabels QuantumNLS.BetheSmooth QuantumNLS.BetheRoots

/-- The ordered Bethe roots of an occupation array are the smooth root map at the logarithmic labels. -/
theorem arrRoots_eq_root {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (m : MArr N) :
    arrRoots L c m = root L (fun j => 2 * Real.pi * (labelsEquivArr.symm m).I j) c := by
  have h1 := (rapidityEq_iff_arrRoots hL hc m (arrRoots L c m)).2 rfl
  rw [rapidityEq_iff_logMap] at h1
  exact eq_root hL hc h1

/-- **The finite coupling identity for occupation arrays** (accepted R-3C2D6BAB `F07EnergyR6.intensive_response`
transported to `arrRoots`): `K ∂_K [N⁻¹ ∑ q_i²] = 2 N⁻¹∑q_i² - 2 L N⁻¹ ∑ q_i (B⁻¹ q)_i` at contact `K/N`. -/
theorem finiteE_hasDerivAt {N : ℕ} (hN : 0 < N) {L K : ℝ} (hL : 0 < L) (hK : 0 < K) (m : MArr N) :
    HasDerivAt (fun K' : ℝ => (N : ℝ)⁻¹ * ∑ i, (arrRoots L (K' / N) m i) ^ 2)
      (K⁻¹ * (2 * ((N : ℝ)⁻¹ * ∑ i, (arrRoots L (K / N) m i) ^ 2) -
        2 * L * ((N : ℝ)⁻¹ * ∑ i, arrRoots L (K / N) m i *
          (gaudin L (K / N) (arrRoots L (K / N) m)).inverse (arrRoots L (K / N) m) i))) K := by
  set b : Fin N → ℝ := fun j => 2 * Real.pi * (labelsEquivArr.symm m).I j with hb
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hev : (fun K' : ℝ => (N : ℝ)⁻¹ * ∑ i, (arrRoots L (K' / N) m i) ^ 2) =ᶠ[𝓝 K]
      F07EnergyR6.intensiveEnergy L b := by
    filter_upwards [lt_mem_nhds hK] with K' hK'
    have hc : 0 < K' / N := div_pos hK' hNr
    rw [arrRoots_eq_root hL hc m]
    unfold F07EnergyR6.intensiveEnergy energy
    rfl
  have hparam : HasDerivAt (fun t : ℝ => t / N) (1 / N) K := by
    simpa using (hasDerivAt_id K).div_const (N : ℝ)
  have hc : 0 < K / N := div_pos hK hNr
  have hchain := (((energy_hasDerivAt hL hc b).differentiableAt.hasDerivAt).comp K hparam).const_mul
    ((N : ℝ)⁻¹)
  have hresp := F07EnergyR6.intensive_response hN hL hK b
  dsimp only at hresp
  have hdif : HasDerivAt (F07EnergyR6.intensiveEnergy L b) (deriv (F07EnergyR6.intensiveEnergy L b) K) K := by
    have : F07EnergyR6.intensiveEnergy L b = fun K' => (N : ℝ)⁻¹ * energy L b (K' / N) := rfl
    rw [this]
    exact (hchain.differentiableAt).hasDerivAt
  have hq : arrRoots L (K / N) m = root L b (K / N) := arrRoots_eq_root hL hc m
  have hval : deriv (F07EnergyR6.intensiveEnergy L b) K =
      K⁻¹ * (2 * ((N : ℝ)⁻¹ * ∑ i, (arrRoots L (K / N) m i) ^ 2) -
        2 * L * ((N : ℝ)⁻¹ * ∑ i, arrRoots L (K / N) m i *
          (gaudin L (K / N) (arrRoots L (K / N) m)).inverse (arrRoots L (K / N) m) i)) := by
    rw [eq_inv_mul_iff_mul_eq₀ hK.ne', hresp.1, hq]
    unfold F07EnergyR6.intensiveEnergy energy
    rfl
  rw [← hval]
  exact hdif.congr_of_eventuallyEq hev

end QuantumNLS.REF88QuantumBridge

#print axioms QuantumNLS.REF88QuantumBridge.arrRoots_eq_root
#print axioms QuantumNLS.REF88QuantumBridge.finiteE_hasDerivAt
