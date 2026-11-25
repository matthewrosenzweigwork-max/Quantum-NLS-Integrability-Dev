import Mathlib
import NlsGge.Atomic.G1.G1036
import NlsGge.GK38.PairVolterra

/- G1-037 SUP01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1037Sup1.lean.
   Supporting module (statement M2 of G1037_STOP.md, proof development): the swap identity
   fundPair (swappedPotential phi) (-z) t = S * fundPair phi z t * S, S = [[0,1],[1,0]].
   Proof: both sides solve the Volterra integral equation of the swapped problem; uniqueness is fundCont_unique.
   The representatives potRepFst38/potRepSnd38 of the swapped potential agree a.e. with the negated swapped
   components (coverRep38_smul_ae), which suffices under the interval integral. -/
set_option autoImplicit false
open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section

def g37_S : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def g37_sw : Fin 2 → Fin 2 := ![1, 0]

theorem g37_S_mul_S : g37_S * g37_S = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g37_S, Matrix.mul_apply, Fin.sum_univ_two]

theorem g37_S_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (g37_S * A * g37_S) i j = A (g37_sw i) (g37_sw j) := by
  fin_cases i <;> fin_cases j <;>
    simp [g37_S, g37_sw, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem g37_S_conj3 (E P F : Matrix (Fin 2) (Fin 2) ℂ) :
    (g37_S * E * g37_S) * (g37_S * P * g37_S) * (g37_S * F * g37_S) = g37_S * (E * P * F) * g37_S := by
  have h1 : (g37_S * E * g37_S) * (g37_S * P * g37_S) * (g37_S * F * g37_S) =
      g37_S * E * (g37_S * g37_S) * P * (g37_S * g37_S) * F * g37_S := by
    simp only [Matrix.mul_assoc]
  rw [h1, g37_S_mul_S]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem g37_coverRep_neg_ae (f : PhysicalL2) :
    ∀ᵐ s : ℝ, coverRep38 (-f) s = -coverRep38 f s := by
  filter_upwards [coverRep38_smul_ae (-1 : ℂ) f] with s hs
  simpa using hs

theorem g37_potCoeff_swap_ae (φ : PotPair) :
    ∀ᵐ s : ℝ, potCoeff38 (swappedPotential φ) s = g37_S * potCoeff38 φ s * g37_S := by
  filter_upwards [g37_coverRep_neg_ae φ.2, g37_coverRep_neg_ae φ.1] with s h2 h1
  have e1 : potRepFst38 (swappedPotential φ) s = -potRepSnd38 φ s := h2
  have e2 : potRepSnd38 (swappedPotential φ) s = -potRepFst38 φ s := h1
  ext i j
  rw [g37_S_apply]
  fin_cases i <;> fin_cases j <;> simp [potCoeff38, e1, e2, g37_sw]

theorem g37_freeE_neg (z : ℂ) (t : ℝ) : freeE (-z) t = g37_S * freeE z t * g37_S := by
  ext i j
  rw [g37_S_apply]
  fin_cases i <;> fin_cases j <;> simp [freeE, g37_sw]

theorem g37_fundPair_swap (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    fundPair (swappedPotential φ) (-z) t = g37_S * fundPair φ z t * g37_S := by
  let F : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) := fundCont φ z
  let G : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) :=
    ⟨fun t => g37_S * F t * g37_S,
      (continuous_const.matrix_mul F.continuous).matrix_mul continuous_const⟩
  have hG : ∀ (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2), G t i j = freeE (-z) t i j +
      ∫ s in (0 : ℝ)..t, (freeE (-z) (t - s) * potCoeff38 (swappedPotential φ) s *
        Set.IccExtend zero_le_one G s) i j := by
    intro t i j
    have hIcc : ∀ s, Set.IccExtend zero_le_one G s = g37_S * Set.IccExtend zero_le_one F s * g37_S :=
      fun s => rfl
    have hint : ∫ s in (0 : ℝ)..t, (freeE (-z) (t - s) * potCoeff38 (swappedPotential φ) s *
        Set.IccExtend zero_le_one G s) i j =
        ∫ s in (0 : ℝ)..t, (freeE z (t - s) * potCoeff38 φ s * Set.IccExtend zero_le_one F s)
          (g37_sw i) (g37_sw j) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [g37_potCoeff_swap_ae φ] with s hs _
      rw [hIcc, hs, g37_freeE_neg, g37_S_conj3, g37_S_apply]
    rw [hint]
    have h0 := fundPair_integral_eq φ z t (g37_sw i) (g37_sw j)
    have hGt : G t i j = fundPair φ z t (g37_sw i) (g37_sw j) := g37_S_apply _ i j
    rw [hGt, h0, g37_freeE_neg, g37_S_apply]
    rfl
  have hu := fundCont_unique (swappedPotential φ) (-z) G hG
  have h3 : fundPair (swappedPotential φ) (-z) t = G t := by
    rw [hu]; rfl
  rw [h3]
  rfl

end
end NlsGge.GKDefinitionDesign
