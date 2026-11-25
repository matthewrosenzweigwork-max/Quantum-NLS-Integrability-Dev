import NlsGge.Hierarchy.FullEnergyExistenceW01_38
import NlsGge.Measure.FourierGaussian

/-!
# Relative partition function `Z_N(W)` (v2 `F:eq:relativeZ`)

`Z_N(W) = 𝒵_{W,N} / ∏_{|n|≤N} (π/a_n)`, where
* `𝒵_{W,N} = ∫_{ℂ^{2N+1}} exp(-E_W(z)) d^2 z` is the full-energy plane integral
  (`fullEnergy38`, the complete charge series, ordinary product Lebesgue measure `planeVolume N`),
* `a_n = W(2πn) = fullWeightRate c n` (doubled spectral variable), for every `|n| ≤ N`
  including `n = 0` (`a_0 = β₀ = c₀`),
* the product runs over the `2N+1` modes `modeIndex N i = i - N`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Measure MeasureTheory

/-- The full-energy plane integral `𝒵_{W,N}`. -/
def fullPartition38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) : ℝ :=
  ∫ z, Real.exp (-fullEnergy38 c N z) ∂(planeVolume N)

/-- The free Gaussian normalizer `∏_{|n|≤N} π/a_n`, `a_n = W(2πn)`. -/
def freeNormalizer38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) : ℝ :=
  ∏ i : Fin (2 * N + 1), (Real.pi / fullWeightRate c.val (modeIndex N i))

/-- The relative partition function `Z_N(W) = 𝒵_{W,N} / ∏_{|n|≤N} (π/a_n)`. -/
def relativePartition38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) : ℝ :=
  fullPartition38 c N / freeNormalizer38 c N

theorem fullWeightRate_pos38 {lo up : ℝ} (c : BoundedCoefficients lo up) (n : ℤ) :
    0 < fullWeightRate c.val n :=
  fullWeightRate_pos lo up c.val c.property.1 (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2) n

theorem freeNormalizer38_pos {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    0 < freeNormalizer38 c N :=
  Finset.prod_pos fun _ _ => div_pos Real.pi_pos (fullWeightRate_pos38 c _)

theorem fullPartition38_pos {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    0 < fullPartition38 c N :=
  (partition38_pos_le c N).1

theorem relativePartition38_pos {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    0 < relativePartition38 c N :=
  div_pos (fullPartition38_pos c N) (freeNormalizer38_pos c N)

theorem relativePartition38_mul {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    relativePartition38 c N * freeNormalizer38 c N = fullPartition38 c N :=
  div_mul_cancel₀ _ (freeNormalizer38_pos c N).ne'

end NlsGge.HierarchyRiccati.Core

end
