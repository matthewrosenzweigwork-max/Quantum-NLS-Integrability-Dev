import NlsGge.GK38.AbelianOriginalFiniteCircleExcision
import NlsGge.GK38.AbelianFiniteSignedPeriodIsolation
import NlsGge.GK38.AbelianLargeCircleIntegralLimit

/-! SOURCE ONLY: exact missing actual numerator period. Genuine finite Cauchy
excision and actual large-circle limit discharge the contour/normalization
steps. Ordinary off-n zeros are later realized by actual Fn/Psi zeros, not a
missing-period oracle. Exact targets/English preceded proof.
UNCOMPILED/no native scope/no final family credit. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem p6Actual_missing_period_two_pi38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (n : ℤ) (s : Lib.L2Seq)
    (hoff : ∀ m : ℤ, m ≠ n → abelianPeriod38 m φ (p2FullNumerator38 n s)=0) :
    abelianPeriod38 n φ (p2FullNumerator38 n s)=2*(Real.pi : ℂ) := by
  obtain ⟨Lc,hcontour⟩ := p6Original_finite_circle_period_excision38 φ hφ C R hfam
    (p2FullNumerator38 n s) (p2FullNumerator_entire38 n s)
  obtain ⟨Nn,hNn⟩ := exists_nat_ge (|n| : ℤ)
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨Ll,hlimit⟩ := p6Actual_large_circle_full_quotient_integral_limit38 φ hφ s n ε hε
  let ν : ℕ := max Lc (max Ll Nn)
  have hcν : Lc ≤ ν := le_max_left _ _
  have hlν : Ll ≤ ν := le_trans (le_max_left _ _) (le_max_right _ _)
  have hnν : Nn ≤ ν := le_trans (le_max_right _ _) (le_max_right _ _)
  have hnlabel : |n| ≤ (ν : ℤ) := hNn.trans (by exact_mod_cast hnν)
  have hcircle := hcontour ν hcν
  have hlarge := hlimit ν hlν
  have hsingle := p6Finite_signed_period_single38
    (fun m : ℤ => abelianPeriod38 m φ (p2FullNumerator38 n s)) n ν hnlabel hoff
  have hb := hlarge.2
  rw [hcircle.2,hsingle] at hb
  simpa only [dist_eq_norm] using hb

end
end NlsGge.GK38
