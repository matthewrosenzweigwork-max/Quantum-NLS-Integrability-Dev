import NlsGge.GK38.AbelianActualBoundedInverseTube
import NlsGge.GK38.AbelianFullCompactOperatorLimit

/-! The full actual signed compact operator limit discharges the only limit
premise in the common inverse-norm input tube. -/
set_option autoImplicit false
open Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p6FullGap_complex_uniform_inverse_bound_tube38 (u : PhysicalL2)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 (realSlice u) C R) :
    ∃ B : ℝ, ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq,
      0 < B ∧ IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧
      ∀ φ : PotPair, φ ∈ U → ∀ s : Lib.L2Seq, s ∈ V →
        ∀ n : ℤ, (p6PaddedJacobian38 n φ s).IsInvertible ∧
          ‖(p6PaddedJacobian38 n φ s).inverse‖ ≤ B := by
  apply p6FullGap_complex_uniform_inverse_bound_tube_of_signed_limit38 u C R hfam
  intro s hs ε hε
  obtain ⟨N,hN⟩ := p6ActualPadded_Qstar_compact_signed_operator_limit38 u C R hfam ε hε
  refine ⟨N,?_⟩
  intro n hn
  have hcast : (N : ℤ) ≤ (n.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using hn.le
  have hnat : N ≤ n.natAbs := by exact_mod_cast hcast
  exact hN n hnat s hs

end
end NlsGge.GK38
