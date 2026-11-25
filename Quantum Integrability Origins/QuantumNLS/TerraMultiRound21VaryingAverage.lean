import QuantumNLS.KernelConvergence
import QuantumNLS.TerraMultiRound21OverlapContinuity
import QuantumNLS.TerraMultiRound19ScaledTerms

/-! The surviving fixed-overlap terms for norm-convergent varying inputs. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Filter Topology
open QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct
open QuantumNLS.TerraMultiRound18OverlapLimit QuantumNLS.TerraMultiRound21OverlapContinuity
namespace QuantumNLS.TerraMultiRound21VaryingAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem limit_of_difference_bound {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (x : E) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0))
    (hbound : ∀ n, ‖f n - x‖ ≤ u n) : Tendsto f atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall hbound) hu

theorem varying_average_limit {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q)
    (A : ℕ → BoundedSymmetricKernel H p) (B : ℕ → BoundedSymmetricKernel H q)
    (A₀ : BoundedSymmetricKernel H p) (B₀ : BoundedSymmetricKernel H q)
    (hA : Tendsto (fun N => ‖A N - A₀‖) atTop (𝓝 0))
    (hB : Tendsto (fun N => ‖B N - B₀‖) atTop (𝓝 0)) :
    Tendsto (fun N => averagedOverlapKernel hsp hsq (A N) (B N)) atTop
      (𝓝 (averagedOverlapKernel hsp hsq A₀ B₀)) := by
  have hb : Tendsto (fun N => ‖B N‖) atTop (𝓝 ‖B₀‖) :=
    QuantumNLS.KernelConvergence.norm_tendsto_of (E := BoundedSymmetricKernel H q) hB
  have hu : Tendsto (fun N => ‖A N - A₀‖ * ‖B N‖ + ‖A₀‖ * ‖B N - B₀‖)
      atTop (𝓝 0) := by
    simpa using (hA.mul hb).add (tendsto_const_nhds.mul hB)
  exact limit_of_difference_bound (E := BoundedSymmetricKernel H (unionSize p q s))
    _ _ _ hu (fun N => average_difference_bound hsp hsq (A N) A₀ (B N) B₀)

#print axioms varying_average_limit
end QuantumNLS.TerraMultiRound21VaryingAverage
