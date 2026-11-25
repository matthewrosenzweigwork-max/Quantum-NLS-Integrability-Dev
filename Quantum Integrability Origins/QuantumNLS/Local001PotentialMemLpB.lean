import QuantumNLS.Local001PotentialAlgebraB

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral

/-- The potential applied to an essentially bounded vector is square integrable. -/
theorem potentialFn_memLp {L : ℝ} (κ : ℝ) (hκ : 0 ≤ κ)
    (u : ScalarInterval L) (g : VectorInterval L) (M : ℝ)
    (hsup : ∀ᵐ (x : ℝ) ∂μI L, ‖g x‖ ≤ M) :
    MemLp (potentialResolventFn κ u g) 2 (μI L) := by
  have hpair : AEStronglyMeasurable (fun x : ℝ => (u x, g x)) (μI L) :=
    (Lp.aestronglyMeasurable u).prodMk (Lp.aestronglyMeasurable g)
  have hstrong : AEStronglyMeasurable (potentialResolventFn κ u g) (μI L) := by
    change AEStronglyMeasurable (fun x : ℝ => potentialPt κ (u x) (g x)) (μI L)
    exact Continuous.comp_aestronglyMeasurable
      (g := fun p : ℂ × E2 => potentialPt κ p.1 p.2)
      (f := fun x : ℝ => (u x, g x)) (continuous_potentialPt κ) hpair
  have hpoint : ∀ᵐ (x : ℝ) ∂μI L,
      ‖potentialResolventFn κ u g x‖ ≤ (2 * Real.sqrt κ * M) * ‖u x‖ := by
    filter_upwards [hsup] with x hx
    change ‖potentialPt κ (u x) (g x)‖ ≤ _
    rw [potentialPt_norm hκ]
    calc
      2 * Real.sqrt κ * ‖u x‖ * ‖g x‖ ≤ (2 * Real.sqrt κ * ‖u x‖) * M :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = (2 * Real.sqrt κ * M) * ‖u x‖ := by ring
  exact (Lp.memLp u).of_le_mul hstrong hpoint

#print axioms potentialFn_memLp

theorem potentialResolvent_memLp {L r : ℝ} [Fact (0 < L)]
    (κ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L) (n : ℤ) (hr : 0 < r)
    (hsmall : r < spacing L / 2) {z : ℂ} (hz : OnGamma L r n z)
    (u : ScalarInterval L) (f : VectorInterval L) :
    MemLp (potentialResolventFn κ u
      (LocalSpectral.resolvent L κ (fun _ => 0) (LocalSpectral.parity n) z f))
      2 (μI L) := by
  exact potentialFn_memLp κ hκ u _ (resolventConstant L r * ‖f‖)
    (sourceResolvent_ae_sup_bound hL κ n hr hsmall hz f)

#print axioms potentialResolvent_memLp
end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
