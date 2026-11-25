import NlsGge.Atomic.LIB.LIB023

set_option autoImplicit false
namespace NlsGge.Atomic.G5

theorem compact_of_hilbertSchmidt
    {ι H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H)
    (A : H →L[ℝ] H)
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)) :
    IsCompactOperator A := by
  exact NlsGge.Atomic.LIB023.hs_columns_compact b A hA

end NlsGge.Atomic.G5
