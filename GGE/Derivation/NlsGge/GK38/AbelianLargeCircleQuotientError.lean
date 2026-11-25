import NlsGge.GK38.AbelianLargeCircleRootNonzero
import NlsGge.GK38.AbelianPeriods

/-! The actual full omitted-numerator/canonical-root ratio at infinity.
The weighted error has ONE cutoff before EVERY signed omitted label. -/
set_option autoImplicit false
open Filter Topology SummationFilter
namespace NlsGge.GK38
noncomputable section

theorem p6Root_product_quotient_error38 (P R S : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hS : S ≠ 0) (hRS : ‖S‖ ≤ ‖R‖)
    (hP : ‖P+S‖ ≤ δ*‖S‖) (hR : ‖R+2*Complex.I*S‖ ≤ δ*‖S‖) :
    ‖(-2)*P/R-Complex.I‖ ≤ 3*δ := by
  have hRn : R ≠ 0 := norm_pos_iff.mp ((norm_pos_iff.mpr hS).trans_le hRS)
  have he : (-2)*P/R-Complex.I=
      ((-2)*(P+S)-Complex.I*(R+2*Complex.I*S))/R := by
    field_simp [hRn]; ring_nf; simp [Complex.I_sq]
  have hnum : ‖(-2)*(P+S)-Complex.I*(R+2*Complex.I*S)‖ ≤ (3*δ)*‖S‖ := by
    calc
      _ ≤ ‖(-2)*(P+S)‖+‖Complex.I*(R+2*Complex.I*S)‖ := norm_sub_le _ _
      _ = 2*‖P+S‖+‖R+2*Complex.I*S‖ := by norm_num [norm_mul]
      _ ≤ 2*(δ*‖S‖)+δ*‖S‖ := by gcongr
      _ = _ := by ring
  rw [he,norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hRn)).2
  exact hnum.trans (mul_le_mul_of_nonneg_left hRS (by positivity))

theorem p6Actual_full_numerator_root_large_circle_weighted_error38
    (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq) :
    ∀ ε > 0, ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 → ∀ n : ℤ,
      ‖(Lib.sigmaOf s n-z)*(p2FullNumerator38 n s z/canonRoot38 φ z)-Complex.I‖ ≤ ε := by
  intro ε hε
  let δ : ℝ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NP,hNP⟩ := Lib.product_growth (Lib.sigmaOf s) (Lib.summable_dev_sigmaOf s) δ hδ
  obtain ⟨NR,hNR⟩ := p6Actual_canonical_root_large_circle_growth38 φ hφ δ hδ
  obtain ⟨NL,hNL⟩ := p6Actual_large_circle_root_lower_nonzero38 φ hφ
  refine ⟨max NP (max NR NL),fun ν hν z hz n => ?_⟩
  have hνP : NP ≤ ν := (le_max_left _ _).trans hν
  have hνR : NR ≤ ν := (le_max_left NR NL).trans ((le_max_right _ _).trans hν)
  have hνL : NL ≤ ν := (le_max_right NR NL).trans ((le_max_right _ _).trans hν)
  let P : ℂ := ∏'[symmetricIcc ℤ] m : ℤ, Lib.prodFactor (Lib.sigmaOf s) z m
  have hP : ‖P+Complex.sin z‖ ≤ δ*‖Complex.sin z‖ := hNP ν hνP z hz
  have hR : ‖canonRoot38 φ z+2*Complex.I*Complex.sin z‖ ≤ δ*‖Complex.sin z‖ :=
    hNR ν hνR z hz
  have hratio := p6Root_product_quotient_error38 P (canonRoot38 φ z) (Complex.sin z)
    δ hδ.le (p6LargeCircle_sin_ne_zero38 ν z hz) (hNL ν hνL z hz).1 hP hR
  have hmul : (Lib.sigmaOf s n-z)*p2FullNumerator38 n s z=(-2)*P := by
    dsimp only [P]
    rw [Lib.entProd_eq_mul_omitProd n s z]
    dsimp [p2FullNumerator38]
    ring
  have he : (Lib.sigmaOf s n-z)*(p2FullNumerator38 n s z/canonRoot38 φ z)=
      (-2)*P/canonRoot38 φ z := by rw [← mul_div_assoc,hmul]
  rw [he]
  exact hratio.trans (by dsimp [δ]; linarith)

end
end NlsGge.GK38
