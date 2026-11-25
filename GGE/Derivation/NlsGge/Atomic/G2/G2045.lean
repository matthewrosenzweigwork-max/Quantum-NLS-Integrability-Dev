import Mathlib
import NlsGge.Atomic.G1.G1038
import NlsGge.Atomic.G1.G1038
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.Atomic.G2.G2045SupC1
import NlsGge.Atomic.G2.G2045SupC2
import NlsGge.Atomic.G2.G2045SupC3
import NlsGge.Atomic.G2.G2045SupC4
-- WRAPPER-IMPORTS-BEGIN
import NlsGge.Atomic.G2.G2043
import NlsGge.Atomic.G2.G2075
-- WRAPPER-IMPORTS-END

/- G2-045 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/G2/G2045.lean,
   namespace NlsGge.GKDefinitionDesign.  Head VERBATIM from Pro round 13 (gpt6pro_followup11) STATEMENTS/G2.md "## G2-045".
   Route (Grebert-Kappeler Thm 13.6): U is the union over u in H^(k-1) of the Sobolev balls about realSlice u furnished by
   G2045SupC4 (on which sourceW, absolute summability and the trace identity hold); openness is the triangle inequality for
   pairSobolevNorm; integrability from L2 x L2; the k = 3 clause from G1_038_part3 and (2I)^2 = -4. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

/-- `G2_045` with `sourceW` replaced by an abstract `W`; `hball` is the conclusion of `g2045c_ball_trace` for `W`. -/
theorem g2045c_main_core (k : ℕ) (hk : 2 ≤ k) (W : Set PotPair)
    (hball : ∀ u : PhysicalL2, physicalSobolev ((k - 1 : ℕ) : ℝ) u →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ ψ ∈ g2045bBall (k - 1) (realSlice u) ρ,
        ψ ∈ W ∧ Summable (fun n : ℤ => ‖higherAction k ψ n‖) ∧
        ∑' n : ℤ, higherAction k ψ n =
          -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k ψ) :
    ∃ U : Set PotPair,
      U ⊆ W ∧
      (∀ φ ∈ U, pairSobolev ((k-1 : ℕ) : ℝ) φ) ∧
      (∀ u : PhysicalL2, physicalSobolev ((k-1 : ℕ) : ℝ) u → realSlice u ∈ U) ∧
      (∀ φ ∈ U, ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : PotPair,
        pairSobolev ((k-1 : ℕ) : ℝ) ψ →
        pairSobolevNorm ((k-1 : ℕ) : ℝ) (ψ-φ) < δ → ψ ∈ U) ∧
      (∀ φ ∈ U,
        Integrable (fun x : PhysicalCircle => φ.1 x * wkbR φ k x) spatialMeasure ∧
        Summable (fun n : ℤ => ‖higherAction k φ n‖) ∧
        HasSum (fun n : ℤ => higherAction k φ n)
          (-(k : ℂ)/(2*Complex.I)^(k-1) * hierarchyHamiltonian k φ) ∧
        (k=3 →
          Integrable (fun x : PhysicalCircle =>
            weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2)
            spatialMeasure ∧
          (4/3 : ℂ) * (∑' n : ℤ, higherAction 3 φ n) =
            ∫ x : PhysicalCircle,
              weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2
              ∂spatialMeasure)) := by
  let P : PotPair → ℝ → Prop := fun c ρ => 0 < ρ ∧ ∀ ψ ∈ g2045bBall (k - 1) c ρ,
    ψ ∈ W ∧ Summable (fun n : ℤ => ‖higherAction k ψ n‖) ∧
      ∑' n : ℤ, higherAction k ψ n =
        -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k ψ
  let U : Set PotPair := {φ | ∃ (u : PhysicalL2) (ρ : ℝ), physicalSobolev ((k - 1 : ℕ) : ℝ) u ∧
    P (realSlice u) ρ ∧ φ ∈ g2045bBall (k - 1) (realSlice u) ρ}
  have hU1 : ∀ φ ∈ U, φ ∈ W ∧ pairSobolev ((k - 1 : ℕ) : ℝ) φ ∧
      Summable (fun n : ℤ => ‖higherAction k φ n‖) ∧
      ∑' n : ℤ, higherAction k φ n =
        -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k φ := by
    rintro φ ⟨u, ρ, hu, ⟨hρ, hG⟩, hφ⟩
    obtain ⟨h1, h2, h3⟩ := hG φ hφ
    exact ⟨h1, hφ.1, h2, h3⟩
  refine ⟨U, fun φ hφ => (hU1 φ hφ).1, fun φ hφ => (hU1 φ hφ).2.1, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨ρ, hρ, hG⟩ := hball u hu
    refine ⟨u, ρ, hu, ⟨hρ, hG⟩, g2045c_real_pair _ u hu, ?_⟩
    rw [sub_self, g2045c_pn_zero]
    exact hρ
  · rintro φ ⟨u, ρ, hu, ⟨hρ, hG⟩, hφ⟩
    have hc : pairSobolev ((k - 1 : ℕ) : ℝ) (realSlice u) := g2045c_real_pair _ u hu
    refine ⟨ρ - pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - realSlice u), sub_pos.2 hφ.2, ?_⟩
    intro ψ hψ hψφ
    refine ⟨u, ρ, hu, ⟨hρ, hG⟩, hψ, ?_⟩
    have e : ψ - realSlice u = (ψ - φ) + (φ - realSlice u) := by abel
    rw [e]
    have h := g2045b_pn_add (k - 1) ((pairSobolevSub (k - 1)).sub_mem hψ hφ.1)
      ((pairSobolevSub (k - 1)).sub_mem hφ.1 hc)
    linarith
  · intro φ hφ
    obtain ⟨hW, hp, hs, hv⟩ := hU1 φ hφ
    refine ⟨integrable_mul_L2 φ.1 (wkbR φ k), hs, ?_, ?_⟩
    · rw [← hv]
      exact (Summable.of_norm hs).hasSum
    · rintro rfl
      have h2 : ((3 - 1 : ℕ) : ℝ) = 2 := by norm_num
      rw [h2] at hp
      obtain ⟨hI, hH⟩ := G1_038_part3 φ hp
      refine ⟨hI, ?_⟩
      rw [hv, ← hH]
      have h4 : ((2 : ℂ) * Complex.I) ^ (3 - 1) = -4 := by
        rw [show 3 - 1 = 2 from rfl, mul_pow, Complex.I_sq]
        norm_num
      rw [h4]
      push_cast
      ring

-- WRAPPER-BEGIN
theorem G2_045 (k : ℕ) (hk : 2 ≤ k) :
    ∃ U : Set PotPair,
      U ⊆ sourceW ∧
      (∀ φ ∈ U, pairSobolev ((k-1 : ℕ) : ℝ) φ) ∧
      (∀ u : PhysicalL2, physicalSobolev ((k-1 : ℕ) : ℝ) u → realSlice u ∈ U) ∧
      (∀ φ ∈ U, ∃ δ : ℝ, 0 < δ ∧ ∀ ψ : PotPair,
        pairSobolev ((k-1 : ℕ) : ℝ) ψ →
        pairSobolevNorm ((k-1 : ℕ) : ℝ) (ψ-φ) < δ → ψ ∈ U) ∧
      (∀ φ ∈ U,
        Integrable (fun x : PhysicalCircle => φ.1 x * wkbR φ k x) spatialMeasure ∧
        Summable (fun n : ℤ => ‖higherAction k φ n‖) ∧
        HasSum (fun n : ℤ => higherAction k φ n)
          (-(k : ℂ)/(2*Complex.I)^(k-1) * hierarchyHamiltonian k φ) ∧
        (k=3 →
          Integrable (fun x : PhysicalCircle =>
            weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2)
            spatialMeasure ∧
          (4/3 : ℂ) * (∑' n : ℤ, higherAction 3 φ n) =
            ∫ x : PhysicalCircle,
              weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2
              ∂spatialMeasure)) :=
  g2045c_main_core k hk sourceW (fun u hu => g2045c_ball_trace k hk u hu)
-- WRAPPER-END

end NlsGge.GKDefinitionDesign
end
