import NlsGge.GK38.AbelianLargeCircleCorrectionProduct

/-! The canonical root has the literal sign fixed by its infinity-normalized
standard factors: -2*I*sin on the midpoint circles, with relative norm error.
This is the asymptotic step of book Proposition14.11, before contour excision. -/
set_option autoImplicit false
open Filter Topology SummationFilter
namespace NlsGge.GK38
noncomputable section

theorem p6Actual_tau_gamma_large_circle_inputs38 (φ : PotPair) (hφ : φ ∈ gkW) :
    Summable (fun m : ℤ => ‖tauN φ m-(m : ℂ)*(Real.pi : ℂ)‖^2) ∧
      Summable (fun m : ℤ => ‖gamma2 φ m‖^2) := by
  constructor
  · simpa only [← a5TauShift_value38 φ hφ] using
      (Lib.hasSum_sq_l2 (a5TauShift38 φ)).summable
  · simpa only [← a5GammaHilbert_value38 φ hφ] using
      (Lib.hasSum_sq_l2 (a5GammaHilbert38 φ)).summable

theorem p6Actual_canonical_root_large_circle_growth38 (φ : PotPair) (hφ : φ ∈ gkW) :
    ∀ ε > 0, ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 →
      ‖canonRoot38 φ z+2*Complex.I*Complex.sin z‖ ≤ ε*‖Complex.sin z‖ := by
  intro ε hε
  obtain ⟨hτ,hγ⟩ := p6Actual_tau_gamma_large_circle_inputs38 φ hφ
  let δ : ℝ := min 1 (ε/8)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε/8 := min_le_right _ _
  obtain ⟨Nτ,hNτ⟩ := Lib.product_growth (tauN φ) hτ δ hδ
  obtain ⟨NQ,hNQ⟩ := p6LargeCircle_root_correction_product38 (tauN φ) (gamma2 φ) hτ hγ δ hδ
  obtain ⟨NE,hNE⟩ := p6LargeCircle_root_correction_errors38 (tauN φ) (gamma2 φ) hτ hγ 1 zero_lt_one
  refine ⟨max Nτ (max NQ NE),fun ν hν z hz => ?_⟩
  have hντ : Nτ ≤ ν := (le_max_left _ _).trans hν
  have hνQ : NQ ≤ ν := (le_max_left NQ NE).trans ((le_max_right _ _).trans hν)
  have hνE : NE ≤ ν := (le_max_right NQ NE).trans ((le_max_right _ _).trans hν)
  let P : ℂ := ∏'[symmetricIcc ℤ] m : ℤ, (tauN φ m-z)/(Lib.piN m : ℂ)
  let Q : ℂ := p6FullRootCorrection38 (tauN φ) (gamma2 φ) z
  have hP : ‖P+Complex.sin z‖ ≤ δ*‖Complex.sin z‖ := hNτ ν hντ z hz
  have hQ : ‖Q-1‖ ≤ δ := (hNQ ν hνQ z hz).2
  have hQnorm : ‖Q‖ ≤ 1+δ := by
    have ht := norm_le_norm_sub_add Q (1 : ℂ)
    norm_num only [norm_one] at ht
    linarith
  have hfactor : canonRoot38 φ z=2*Complex.I*P*Q :=
    (p6Actual_canonical_root_full_correction38 φ hφ z (hNE ν hνE z hz).1).2
  have he : canonRoot38 φ z+2*Complex.I*Complex.sin z=
      (2*Complex.I)*((P+Complex.sin z)*Q-Complex.sin z*(Q-1)) := by
    rw [hfactor]
    ring
  have hconst : 2*(δ*(1+δ)+δ) ≤ ε := by
    have hs : δ*δ ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left hδ1 hδ.le]
    nlinarith
  calc
    _ = 2*‖(P+Complex.sin z)*Q-Complex.sin z*(Q-1)‖ := by
      rw [he,norm_mul]
      norm_num
    _ ≤ 2*(‖P+Complex.sin z‖*‖Q‖+‖Complex.sin z‖*‖Q-1‖) := by
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left
        (norm_sub_le ((P+Complex.sin z)*Q) (Complex.sin z*(Q-1))) (by norm_num : (0 : ℝ)≤2)
    _ ≤ 2*((δ*‖Complex.sin z‖)*(1+δ)+‖Complex.sin z‖*δ) := by gcongr
    _ = (2*(δ*(1+δ)+δ))*‖Complex.sin z‖ := by ring
    _ ≤ ε*‖Complex.sin z‖ := mul_le_mul_of_nonneg_right hconst (norm_nonneg _)

end
end NlsGge.GK38
