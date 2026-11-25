import NlsGge.Birkhoff.F10Claim38
open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Measure

/-! NEW-F10 corollary (review REVIEW_NEW_F10 finding N2): the L¹ convergence holds for every
Gaussian divergence `δ` satisfying `RamerDivergence38`, not only for the one produced by W07. -/

namespace NlsGge.Birkhoff

/-- `f_N → f_W` in `L¹(γ_W)` for every admissible Gaussian divergence `δ`. -/
theorem BirkhoffInput38.L1_F10_forall_delta38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) {s : ℝ} (hs : (1:ℝ)/2 < s) (hs' : s < 3/4)
    (δ : (ℤ → ℂ) → ℝ)
    (hδ : RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ) :
    Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x -
        fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ x|
        ∂(fullWeightedSequenceGaussian c s)) atTop (𝓝 0) := by
  obtain ⟨δ₀, hδ₀, -, -, -, h, -⟩ := B.L1_F10_38 O c hs hs'
  have hu := fW06_ae_unique_W07 c s B O hs (le_one_of_lt_three_quarters_W06_38 hs') δ₀ δ hδ₀ hδ
  refine h.congr fun N => integral_congr_ae ?_
  filter_upwards [hu] with x hx
  rw [hx]

end NlsGge.Birkhoff
