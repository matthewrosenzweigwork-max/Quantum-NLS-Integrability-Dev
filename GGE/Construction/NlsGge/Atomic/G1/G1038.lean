import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.ThirdConsultation.G1.Round6
import NlsGge.ThirdConsultation.G1.IBP038Support

                                                                                              
                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem integrable_mul_L2 (u v : PhysicalL2) :
    Integrable (fun x : PhysicalCircle => u x * v x) spatialMeasure :=
  MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp u) (Lp.memLp v)

theorem wkbR_three (φ : PotPair) :
    wkbR φ 3 = -weakDerivative (weakDerivative φ.2) +
      physicalProduct φ.1 (physicalProduct (-φ.2) (-φ.2)) := by
  have h := wkbR_succ φ 2 (by norm_num)
  have e : (∑ k ∈ Finset.Icc 1 (2 - 1), physicalProduct (wkbR φ k) (wkbR φ (2 - k)))
      = physicalProduct (-φ.2) (-φ.2) := by
    simp [wkbR_one]
  have h3 : wkbR φ 3 = wkbR φ (2 + 1) := rfl
  rw [h3, h, e, wkbR_two, weakDerivative_neg']

theorem ae_phi1_B (φ : PotPair) (h1 : physicalSobolev 1 φ.1) (h2 : physicalSobolev 1 φ.2) :
    ∀ᵐ x ∂spatialMeasure, φ.1 x * physicalProduct φ.1 (physicalProduct (-φ.2) (-φ.2)) x
      = (φ.1 x)^2 * (φ.2 x)^2 := by
  have hX : productInL2 (-φ.2) (-φ.2) := productInL2_of_H1 _ _ (h1_neg φ.2 h2)
  have hB : productInL2 φ.1 (physicalProduct (-φ.2) (-φ.2)) := productInL2_of_H1 _ _ h1
  filter_upwards [physicalProduct_ae φ.1 _ hB, physicalProduct_ae (-φ.2) (-φ.2) hX,
    Lp.coeFn_neg φ.2] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  simp only [Pi.neg_apply]
  ring

theorem G1_038_part1 (φ : PotPair) :
    Integrable (fun x : PhysicalCircle => φ.1 x * φ.2 x) spatialMeasure ∧
      hierarchyHamiltonian 1 φ = ∫ x : PhysicalCircle, φ.1 x * φ.2 x ∂spatialMeasure :=
  ⟨integrable_mul_L2 φ.1 φ.2, by simp [hierarchyHamiltonian]⟩

theorem G1_038_part2 (φ : PotPair) (h : pairSobolev 1 φ) :
    Integrable (fun x : PhysicalCircle =>
        weakDerivative φ.1 x * φ.2 x - φ.1 x * weakDerivative φ.2 x) spatialMeasure ∧
      hierarchyHamiltonian 2 φ = (1/2 : ℂ) *
        ∫ x : PhysicalCircle, weakDerivative φ.1 x * φ.2 x - φ.1 x * weakDerivative φ.2 x
          ∂spatialMeasure := by
  obtain ⟨h1, h2⟩ := h
  have hibp := integral_weakDerivative_mul φ.1 φ.2 h1 h2
  have hk2 : hierarchyHamiltonian 2 φ =
      -∫ x : PhysicalCircle, φ.1 x * weakDerivative φ.2 x ∂spatialMeasure := by
    unfold hierarchyHamiltonian
    rw [if_neg (by norm_num), wkbR_two, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg (weakDerivative φ.2)] with x hx
    simp only [hx, Pi.neg_apply]
    ring
  refine ⟨(integrable_mul_L2 (weakDerivative φ.1) φ.2).sub
    (integrable_mul_L2 φ.1 (weakDerivative φ.2)), ?_⟩
  rw [hk2, integral_sub (integrable_mul_L2 (weakDerivative φ.1) φ.2)
    (integrable_mul_L2 φ.1 (weakDerivative φ.2)), hibp]
  ring

theorem G1_038_part3 (φ : PotPair) (h : pairSobolev 2 φ) :
    Integrable (fun x : PhysicalCircle =>
        weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2) spatialMeasure ∧
      hierarchyHamiltonian 3 φ = ∫ x : PhysicalCircle,
        weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2 * (φ.2 x)^2 ∂spatialMeasure := by
  obtain ⟨h1, h2⟩ := h
  have hH1 : physicalSobolev 1 φ.1 := h1_of_two φ.1 h1
  have hH2 : physicalSobolev 1 φ.2 := h1_of_two φ.2 h2
  have hd2 : physicalSobolev 1 (weakDerivative φ.2) := wd_H1_of_two φ.2 h2
  have hP : MemLp (fun x : PhysicalCircle => φ.1 x * φ.2 x) 2 spatialMeasure :=
    productInL2_of_H1 φ.1 φ.2 hH1
  have hI1 : Integrable (fun x : PhysicalCircle => (φ.1 x)^2 * (φ.2 x)^2) spatialMeasure := by
    refine (MemLp.integrable_mul (p := 2) (q := 2) hP hP).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.mul_apply]
    ring
  have hI3 : Integrable (fun x : PhysicalCircle =>
      φ.1 x * physicalProduct φ.1 (physicalProduct (-φ.2) (-φ.2)) x) spatialMeasure :=
    hI1.congr ((ae_phi1_B φ hH1 hH2).mono fun x hx => hx.symm)
  have hIBP := integral_weakDerivative_mul φ.1 (weakDerivative φ.2) hH1 hd2
  have hIBP' : ∫ x : PhysicalCircle, φ.1 x * weakDerivative (weakDerivative φ.2) x ∂spatialMeasure =
      -∫ x : PhysicalCircle, weakDerivative φ.1 x * weakDerivative φ.2 x ∂spatialMeasure := by
    rw [hIBP]
    ring
  have hpt : (fun x : PhysicalCircle => φ.1 x * wkbR φ 3 x) =ᵐ[spatialMeasure]
      fun x : PhysicalCircle => -(φ.1 x * weakDerivative (weakDerivative φ.2) x) +
        φ.1 x * physicalProduct φ.1 (physicalProduct (-φ.2) (-φ.2)) x := by
    rw [wkbR_three]
    filter_upwards [Lp.coeFn_add (-weakDerivative (weakDerivative φ.2))
        (physicalProduct φ.1 (physicalProduct (-φ.2) (-φ.2))),
      Lp.coeFn_neg (weakDerivative (weakDerivative φ.2))] with x hx1 hx2
    simp only [hx1, hx2, Pi.add_apply, Pi.neg_apply]
    ring
  have hk3 : hierarchyHamiltonian 3 φ =
      ∫ x : PhysicalCircle, φ.1 x * wkbR φ 3 x ∂spatialMeasure := by
    unfold hierarchyHamiltonian
    rw [if_neg (by norm_num)]
  refine ⟨(integrable_mul_L2 (weakDerivative φ.1) (weakDerivative φ.2)).add hI1, ?_⟩
  have hneg : Integrable (fun x : PhysicalCircle =>
      -(φ.1 x * weakDerivative (weakDerivative φ.2) x)) spatialMeasure :=
    (integrable_mul_L2 φ.1 (weakDerivative (weakDerivative φ.2))).neg
  rw [hk3, integral_congr_ae hpt, integral_add hneg hI3,
    integral_neg, integral_congr_ae (ae_phi1_B φ hH1 hH2), hIBP',
    integral_add (integrable_mul_L2 (weakDerivative φ.1) (weakDerivative φ.2)) hI1]
  ring

theorem G1_038 :
    (∀ φ : PotPair,
      Integrable (fun x : PhysicalCircle => φ.1 x * φ.2 x) spatialMeasure ∧
      hierarchyHamiltonian 1 φ =
        ∫ x : PhysicalCircle, φ.1 x * φ.2 x ∂spatialMeasure) ∧
    (∀ φ : PotPair, pairSobolev 1 φ →
      Integrable (fun x : PhysicalCircle =>
        weakDerivative φ.1 x * φ.2 x - φ.1 x * weakDerivative φ.2 x)
        spatialMeasure ∧
      hierarchyHamiltonian 2 φ = (1/2 : ℂ) *
        ∫ x : PhysicalCircle,
          weakDerivative φ.1 x * φ.2 x - φ.1 x * weakDerivative φ.2 x
          ∂spatialMeasure) ∧
    (∀ φ : PotPair, pairSobolev 2 φ →
      Integrable (fun x : PhysicalCircle =>
        weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2*(φ.2 x)^2)
        spatialMeasure ∧
      hierarchyHamiltonian 3 φ =
        ∫ x : PhysicalCircle,
          weakDerivative φ.1 x * weakDerivative φ.2 x + (φ.1 x)^2*(φ.2 x)^2
          ∂spatialMeasure) :=
  ⟨fun φ => G1_038_part1 φ, fun φ h => G1_038_part2 φ h, fun φ h => G1_038_part3 φ h⟩

end NlsGge.GKDefinitionDesign
end
