import Mathlib
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2071Support1

set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open scoped BigOperators

namespace NlsGge.GKDefinitionDesign

theorem G2_074 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceW) :
    ∃ V : Set PotPair, IsOpen V ∧ φ₀ ∈ V ∧ V ⊆ sourceW ∧
      ∃ B : ℝ, 0 < B ∧ ∀ φ ∈ V, ∀ n : ℤ, ∃ A : P2Space38 n,
        (∀ m : P2Index38 n,
          normalizedRoot n m.1 φ =
            tauN φ m.1 + gamma2 φ m.1 * A m) ∧
        Summable (fun m : P2Index38 n => ‖A m‖^2) ∧
        (∑' m : P2Index38 n, ‖A m‖^2) ≤ B := by
  obtain ⟨V, hVo, hφV, hVW, B, hB, hA⟩ :=
    NlsGge.Atomic.ExistingPhysicalFamily.actualPhysicalLocalFamily_quadratic_mass φ₀ hφ₀
  refine ⟨V, hVo, hφV, hVW, B, hB, fun φ hφ n => ?_⟩
  obtain ⟨A, hfac, hs, hle⟩ := hA φ hφ n
  refine ⟨A, fun m => ?_, hs, hle⟩
  have h := hfac m
  unfold normalizedRoot
  rw [dif_pos m.2]
  exact h

end NlsGge.GKDefinitionDesign
