import QuantumNLS.TerraMultiRound46Recursion
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Cauchy product for an absolutely summable bilinear series. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound46Cauchy
open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- An absolutely convergent bilinear double series can be grouped by total degree. -/
theorem bilinear_cauchy (F : E →L[ℂ] E →L[ℂ] E) (f g : ℕ → E)
    (hf : Summable fun n => ‖f n‖) (hg : Summable fun n => ‖g n‖) :
    F (∑' i, f i) (∑' j, g j) =
      ∑' n, ∑ ij ∈ antidiagonal n, F (f ij.1) (g ij.2) := by
  have hp : Summable (fun p : ℕ × ℕ => F (f p.1) (g p.2)) := by
    apply Summable.of_norm_bounded ((hf.mul_of_nonneg hg
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left ‖F‖)
    intro p
    calc
      ‖F (f p.1) (g p.2)‖ ≤ ‖F (f p.1)‖ * ‖g p.2‖ := (F (f p.1)).le_opNorm _
      _ ≤ (‖F‖ * ‖f p.1‖) * ‖g p.2‖ := by gcongr; exact F.le_opNorm _
      _ = ‖F‖ * (‖f p.1‖ * ‖g p.2‖) := by ring
  have hi : ∀ i, Summable (fun j => F (f i) (g j)) :=
    fun i => (F (f i)).summable hg.of_norm
  have hs : Summable (fun p : Σ n : ℕ, antidiagonal n => F (f (p.2 : ℕ × ℕ).1) (g (p.2 : ℕ × ℕ).2)) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hp
  calc
    F (∑' i, f i) (∑' j, g j) = ∑' i, F (f i) (∑' j, g j) := by
      exact (F.flip (∑' j, g j)).map_tsum hf.of_norm
    _ = ∑' i, ∑' j, F (f i) (g j) := by
      apply tsum_congr
      intro i
      exact (F (f i)).map_tsum hg.of_norm
    _ = ∑' p : ℕ × ℕ, F (f p.1) (g p.2) := (hp.tsum_prod' hi).symm
    _ = ∑' p : Σ n : ℕ, antidiagonal n, F (f (p.2 : ℕ × ℕ).1) (g (p.2 : ℕ × ℕ).2) := by
      exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq _).symm
    _ = ∑' n, ∑ ij ∈ antidiagonal n, F (f ij.1) (g ij.2) := by
      rw [hs.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
      congr 1
      funext n
      conv_rhs => rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
      rfl

#print axioms bilinear_cauchy
end QuantumNLS.TerraMultiRound46Cauchy
