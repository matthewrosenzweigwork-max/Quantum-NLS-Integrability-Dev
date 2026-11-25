import NlsGge.Spectral.ComplexGeometricSeriesTailBound34V2
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations

/-- Odd coefficients vanish, and the even coefficients are genuinely
summable by comparison. The entire series and its tail are then identified. -/
theorem complexEvenSeriesGeometricTail_bound34
    (f : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A) (hA1 : A < 1)
    (hodd : ∀ k : ℕ, f (2*k+1) = 0)
    (hb : ∀ k : ℕ, ‖f (2*k)‖ ≤ A^k) :
    Summable f ∧ ‖(∑' k : ℕ, f k) - f 0‖ ≤ A/(1-A) := by
  have he := complexGeometricSeriesTail_bound34 (fun k => f (2*k)) A hA hA1 hb
  have ho : Summable (fun k : ℕ => f (2*k+1)) := by
    simpa only [hodd] using (summable_zero : Summable (fun k : ℕ => (0 : ℂ)))
  have hs : Summable f := he.1.even_add_odd ho
  have heq : (∑' k : ℕ, f k) = ∑' k : ℕ, f (2*k) := by
    simpa only [hodd, tsum_zero, add_zero] using (tsum_even_add_odd he.1 ho).symm
  refine ⟨hs, ?_⟩
  simpa only [heq, Nat.mul_zero] using he.2

end NlsGge.SpectralFoundations
end
