import Mathlib
import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALGaussianNormalizer38

                                                                                          
                                                
         
                                                                                       
                                                                                            
                                                                                            
                                                                                                  
                                                                                               
                                                                         
                                                                                       
                                                                                                                 
set_option autoImplicit false

open Finset

namespace NlsGge.ThirdConsultation.AL
open NlsGge.AblowitzLadik

/-- Parseval bridge: Σ_k |dft α_k|² = (2N+1) Σ_j |α_j|² (from dft_parseval38 with Φ = Ψ = α). -/
theorem al054_parseval (N : ℕ) (α : ZMod (2 * N + 1) → ℂ) :
    ∑ k, ‖ZMod.dft α k‖ ^ 2 = (2 * (N : ℝ) + 1) * ∑ j, ‖α j‖ ^ 2 := by
  have hc : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h1 := dft_parseval38 (L := 2 * N + 1) α α
  simp only [hc] at h1
  apply Complex.ofReal_injective
  push_cast at h1 ⊢
  exact_mod_cast h1

/-- Real field identity used in AL-054 (h > 0, L h = 1). -/
theorem al054_alg (h L β₀ β₁ β₂ S0 S1 S2 P Q D A0 A1 A2 : ℝ) (hh : 0 < h)
    (hL : L * h = 1)
    (hq : Q = β₀ * (h⁻¹ ^ 1 * S0) + β₁ * (h⁻¹ ^ 3 * S1) + β₂ * (h⁻¹ ^ 5 * S2))
    (hD : Q = D + h * P) (hP : P = L * S0)
    (hS0 : S0 = h ^ 2 * A0) (hS1 : S1 = h ^ 2 * A1) (hS2 : S2 = h ^ 2 * A2) :
    D = (β₀ - h) * h * A0 + β₁ / h * A1 + β₂ / h ^ 3 * A2 := by
  have hne : h ≠ 0 := hh.ne'
  have hLe : L = h⁻¹ := by
    field_simp
    linarith [hL]
  subst hLe
  subst hq hP hS0 hS1 hS2
  have hD2 : D = β₀ * (h⁻¹ ^ 1 * (h ^ 2 * A0)) + β₁ * (h⁻¹ ^ 3 * (h ^ 2 * A1)) +
      β₂ * (h⁻¹ ^ 5 * (h ^ 2 * A2)) - h * (h⁻¹ * (h ^ 2 * A0)) := by
    linarith
  rw [hD2]
  field_simp
  ring

theorem al054 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁)
    (h2 : 0 < β₂) (N : ℕ) (hh : alh38 N < β₀ / 2)
    (v : ZMod (2 * N + 1) → ℂ) :
    (∀ k : ℤ, 0 < alSymbol38 β₀ β₁ β₂ N k) ∧
    (β₀ - alh38 N) * alh38 N * (∑ j, ‖v j‖ ^ 2) +
      β₁ / alh38 N * (∑ j, ‖v j - v (j - 1)‖ ^ 2) +
      β₂ / alh38 N ^ 3 *
        (∑ j, ‖v (j + 1) - 2 * v j + v (j - 1)‖ ^ 2) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
        alSymbol38 β₀ β₁ β₂ N k * ‖alDFT38 N v k‖ ^ 2 := by
  have hpos : 0 < alh38 N := alh38_pos N
  have hne : ((alh38 N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  refine ⟨fun k => alSymbol38_pos h1.le h2.le N (by linarith) k, ?_⟩
  obtain ⟨α, hαdef⟩ : ∃ α : ZMod (2 * N + 1) → ℂ, ∀ j, α j = ((alh38 N : ℝ) : ℂ) * v j :=
    ⟨fun j => ((alh38 N : ℝ) : ℂ) * v j, fun j => rfl⟩
  have hv' : (fun j => ((alh38 N : ℝ) : ℂ)⁻¹ * α j) = v := funext fun j => by
    rw [hαdef, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hD : ∀ k : ZMod (2 * N + 1), alDFT38 N v k.valMinAbs = ZMod.dft α k := fun k => by
    have := alDFT_eq_dft38 N α k
    rw [hv'] at this
    exact this
  have hnorm : ∀ x : ℂ, ‖((alh38 N : ℝ) : ℂ) * x‖ ^ 2 = alh38 N ^ 2 * ‖x‖ ^ 2 := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    ring
  have s0 : ∑ i, ‖α i‖ ^ 2 = alh38 N ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hαdef]; exact hnorm _
  have s1 : ∑ i, ‖α i - α (i - 1)‖ ^ 2 = alh38 N ^ 2 * ∑ i, ‖v i - v (i - 1)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show α i - α (i - 1) = ((alh38 N : ℝ) : ℂ) * (v i - v (i - 1)) by
        simp only [hαdef]; ring]
      exact hnorm _
  have s2 : ∑ i, ‖α (i + 1) - 2 * α i + α (i - 1)‖ ^ 2 =
      alh38 N ^ 2 * ∑ i, ‖v (i + 1) - 2 * v i + v (i - 1)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show α (i + 1) - 2 * α i + α (i - 1) =
          ((alh38 N : ℝ) : ℂ) * (v (i + 1) - 2 * v i + v (i - 1)) by
        simp only [hαdef]; ring]
      exact hnorm _
  have hq := alQ4_quad38 β₀ β₁ β₂ N α
  have hsym : ∀ ν : ℤ, alSymbol38 β₀ β₁ β₂ N ν =
      NlsGge.Weights.weight (alQ4Coef38 β₀ β₁ β₂) (alOmega38 (alh38 N) ν) - alh38 N :=
    fun ν => (alRate38_poly38 β₀ β₁ β₂ N ν).symm
  have hR : ∑ k ∈ Finset.Icc (-(N : ℤ)) N, alSymbol38 β₀ β₁ β₂ N k * ‖alDFT38 N v k‖ ^ 2 =
      ∑ k : ZMod (2 * N + 1), alSymbol38 β₀ β₁ β₂ N k.valMinAbs * ‖ZMod.dft α k‖ ^ 2 := by
    have hF : ∑ ν ∈ Finset.Icc (-(N : ℤ)) N, alSymbol38 β₀ β₁ β₂ N ν * ‖alDFT38 N v ν‖ ^ 2 =
        ∑ k : ZMod (2 * N + 1), alSymbol38 β₀ β₁ β₂ N k.valMinAbs * ‖alDFT38 N v k.valMinAbs‖ ^ 2 :=
      (sum_valMinAbs_eq_Icc38 N _).symm
    rw [hF]
    exact Finset.sum_congr rfl fun k _ => by rw [hD k]
  have hLHS : ∑ k : ZMod (2 * N + 1),
      NlsGge.Weights.weight (alQ4Coef38 β₀ β₁ β₂) (alOmega38 (alh38 N) k.valMinAbs) *
        ‖ZMod.dft α k‖ ^ 2 =
      ∑ k : ZMod (2 * N + 1), alSymbol38 β₀ β₁ β₂ N k.valMinAbs * ‖ZMod.dft α k‖ ^ 2 +
        alh38 N * ∑ k : ZMod (2 * N + 1), ‖ZMod.dft α k‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hsym]; ring
  have hP := al054_parseval N α
  have hLh : (2 * (N : ℝ) + 1) * alh38 N = 1 := alh38_mul N
  have key := al054_alg (alh38 N) (2 * (N : ℝ) + 1) β₀ β₁ β₂
    (∑ i, ‖α i‖ ^ 2) (∑ i, ‖α i - α (i - 1)‖ ^ 2)
    (∑ i, ‖α (i + 1) - 2 * α i + α (i - 1)‖ ^ 2)
    (∑ k : ZMod (2 * N + 1), ‖ZMod.dft α k‖ ^ 2)
    (∑ k : ZMod (2 * N + 1),
      NlsGge.Weights.weight (alQ4Coef38 β₀ β₁ β₂) (alOmega38 (alh38 N) k.valMinAbs) *
        ‖ZMod.dft α k‖ ^ 2)
    (∑ k : ZMod (2 * N + 1), alSymbol38 β₀ β₁ β₂ N k.valMinAbs * ‖ZMod.dft α k‖ ^ 2)
    (∑ i, ‖v i‖ ^ 2) (∑ i, ‖v i - v (i - 1)‖ ^ 2)
    (∑ i, ‖v (i + 1) - 2 * v i + v (i - 1)‖ ^ 2)
    hpos hLh hq hLHS hP s0 s1 s2
  rw [hR]
  exact key.symm

end NlsGge.ThirdConsultation.AL
