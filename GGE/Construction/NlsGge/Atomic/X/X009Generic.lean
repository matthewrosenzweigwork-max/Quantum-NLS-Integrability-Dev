import Mathlib
import NlsGge.Birkhoff.L06Clause38
import NlsGge.Birkhoff.F05Identity38j
import NlsGge.Hierarchy.ALQ4Limit38

                                                                                                                      
                                                                                                                   
                                                                                                               
                                                                                                      
                                                                                                                                          
                                                                                                                                 
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations
namespace NlsGge.Atomic.X009

open MeasureTheory Filter Topology
open NlsGge.Birkhoff NlsGge.AblowitzLadik NlsGge.Sobolev38
open NlsGge.HierarchyRiccati.Core
open scoped BoundedContinuousFunction

theorem q4_law_comparison_and_conditional_identification
    {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
  (∀ s : ℝ, s < 3 / 2 → ∀ φ : SobolevHilbert s →ᵇ ℝ,
    Tendsto (fun N : ℕ => ∫ u, φ u
      ∂(nuBareS38 2 (alQ4Beta38 β₀ β₁ β₂) N s)) atTop
      (𝓝 (∫ u, φ u ∂(alQ4Rho38 s β₀ β₁ β₂))) ∧
    Tendsto (fun N : ℕ => ∫ u, φ u ∂(alQ4Mu38 s β₀ β₁ β₂ N)) atTop
      (𝓝 (∫ u, φ u ∂(alQ4Rho38 s β₀ β₁ β₂)))) ∧
  0 < alQ4Z2_38 β₀ β₁ β₂ ∧
  Tendsto (fun N : ℕ => ZcalBare38 2 (alQ4Beta38 β₀ β₁ β₂) N /
    ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (Real.pi / finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) n)) atTop
    (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) ∧
  Tendsto (alQ4Z38 β₀ β₁ β₂) atTop (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) ∧
  (∀ (B : BirkhoffInput38) (O : OneSmoothingInput38 B) (s : ℝ),
    (((gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map reflect38).map
      (seqRealization38 (sobolevModeWeight s)) =
      (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map
        (seqRealization38 (sobolevModeWeight s))) ∧
    (∀ u : Hm1 2, Vm38 2 (alQ4Beta38 β₀ β₁ β₂) u =
      alV2_38 β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u)) ∧
    ZM38 B 2 (alQ4Beta38 β₀ β₁ β₂) = alQ4Z2_38 β₀ β₁ β₂ ∧
    (muM38 B 2 (alQ4Beta38 β₀ β₁ β₂)).map
      (reSob38 ((2 - 1 : ℕ) : ℝ) s) = alQ4Rho38 s β₀ β₁ β₂) := by
  refine ⟨fun s hs φ => ⟨(L06_08a_free38 h0 h1 h2 hs φ).1,
      alQ4_weak_tendsto38 h0 h1.le h2 s hs φ⟩,
    alQ4Z2_pos38 h0 h1.le h2, (L06_08a_free38 h0 h1 h2 (s := 0) (by norm_num) 0).2,
    alQ4Z_tendsto38 h0 h1.le h2, fun B O s => L06_08b_38 B O h0 h1 h2 s⟩

end NlsGge.Atomic.X009
