import NlsGge.Birkhoff.L06Clause38
import NlsGge.Hierarchy.ALQ4Limit38
import NlsGge.ThirdConsultation.AL.Basic

namespace NlsGge.ThirdConsultation.AL

open Filter Topology Set MeasureTheory
open NlsGge.AblowitzLadik NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Weights
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core

/-- Fourier-cutoff clause for one good free-field realization `g` (`C:thm:AL`, unmodified Fourier
clause). Deterministic dominated convergence via `alSobolev_tendsto_gen38` with the constant rate
family `a_{h,k} = alQ4RateC38 k`, using the `q4Good` summability at a level `j` with
`3/2 - 1/(j+1) ≥ s`. -/
theorem al078_cut {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂)
    (g : ℤ → ℂ) (hg : g ∈ q4Good) (s : ℝ) (hs : s < 3 / 2) :
    Tendsto (fun N : ℕ => seqRealization38 (sobolevModeWeight s)
        (fun k : ℤ => if k ∈ symmetricModes N then alQ4UCoef38 β₀ β₁ β₂ g k else 0))
      atTop (𝓝 (alQ4UReal38 s β₀ β₁ β₂ g)) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 3 / 2 - s by linarith)
  have hm : 0 < min (β₀ / 2) (256 * β₂) := lt_min (by linarith) (by linarith)
  have hwpos : ∀ (t : ℝ) (k : ℤ), 0 < sobolevModeWeight t k := fun t k =>
    (inferInstance : Fact (∀ n : ℤ, 0 < sobolevModeWeight t n)).out k
  have hsum : Summable (fun k : ℤ => sobolevModeWeight s k * ‖g k‖ ^ 2 / alQ4B38 β₀ β₂ k) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
      ((hg n).mul_left (min (β₀ / 2) (256 * β₂))⁻¹)
    · exact div_nonneg (mul_nonneg (hwpos s k).le (sq_nonneg _))
        (alQ4B_pos38 h0 h2 k).le
    · have hpos : 0 < 1 + (k : ℝ) ^ 4 := by positivity
      have hwle : sobolevModeWeight s k ≤
          sobolevModeWeight (3 / 2 - 1 / ((n : ℝ) + 1)) k := by
        unfold sobolevModeWeight
        exact Real.rpow_le_rpow_of_exponent_le (japaneseBracket_one_le k) (by linarith)
      have hBk : alQ4B38 β₀ β₂ k = min (β₀ / 2) (256 * β₂) * (1 + (k : ℝ) ^ 4) := rfl
      rw [hBk]
      calc sobolevModeWeight s k * ‖g k‖ ^ 2 /
            (min (β₀ / 2) (256 * β₂) * (1 + (k : ℝ) ^ 4))
          = (min (β₀ / 2) (256 * β₂))⁻¹ *
              (sobolevModeWeight s k * ‖g k‖ ^ 2 / (1 + (k : ℝ) ^ 4)) := by
            field_simp
        _ ≤ (min (β₀ / 2) (256 * β₂))⁻¹ *
              (sobolevModeWeight (3 / 2 - 1 / ((n : ℝ) + 1)) k * ‖g k‖ ^ 2 /
                (1 + (k : ℝ) ^ 4)) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwle (sq_nonneg _)) hpos.le)
              (inv_nonneg.2 hm.le)
  have hfun : (fun N : ℕ => seqRealization38 (sobolevModeWeight s)
        (fun k : ℤ => if k ∈ symmetricModes N then alQ4UCoef38 β₀ β₁ β₂ g k else 0))
      = fun N : ℕ => seqRealization38 (sobolevModeWeight s)
        (alUhGen38 (fun _ k => alQ4RateC38 β₀ β₁ β₂ k) N g) := by
    funext N
    congr 1
    funext k
    by_cases hk : |k| ≤ (N : ℤ)
    · have hk' : k ∈ symmetricModes N := by
        simp only [symmetricModes, Finset.mem_Icc]; exact abs_le.mp hk
      simp [alUhGen38, alQ4UCoef38, hk, hk']
    · have hk' : k ∉ symmetricModes N := by
        simp only [symmetricModes, Finset.mem_Icc]; intro h; exact hk (abs_le.mpr h)
      simp [alUhGen38, hk, hk']
  have key := alSobolev_tendsto_gen38 s (fun _ k => alQ4RateC38 β₀ β₁ β₂ k)
    (alQ4RateC38 β₀ β₁ β₂) (alQ4B38 β₀ β₂) g (alQ4B_pos38 h0 h2)
    (fun k => alQ4B_le_rateC38 h0 h1.le h2.le k)
    (Filter.Eventually.of_forall fun N k _ => alQ4B_le_rateC38 h0 h1.le h2.le k)
    (fun k => tendsto_const_nhds) hsum
  rw [hfun]
  exact key

/-- **AL-078** (`C:thm:AL`, unmodified Fourier clause, without B/O). -/
theorem al078 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁)
    (h2 : 0 < β₂) :
    (∀ g ∈ q4Good, ∀ s : ℝ, s < 3 / 2 →
      Tendsto (fun N => seqRealization38 (sobolevModeWeight s)
        (fun k : ℤ => if k ∈ symmetricModes N then alQ4UCoef38 β₀ β₁ β₂ g k else 0))
        atTop (𝓝 (alQ4UReal38 s β₀ β₁ β₂ g))) ∧
    (∀ s : ℝ, s < 3 / 2 →
      (∀ N : ℕ, IsProbabilityMeasure
        (nuBareS38 2 (alQ4Beta38 β₀ β₁ β₂) N s)) ∧
      IsProbabilityMeasure (alQ4Rho38 s β₀ β₁ β₂) ∧
      (∀ F : BoundedContinuousFunction (SobolevHilbert s) ℝ,
        Tendsto (fun N => ∫ u, F u ∂nuBareS38 2 (alQ4Beta38 β₀ β₁ β₂) N s)
          atTop (𝓝 (∫ u, F u ∂alQ4Rho38 s β₀ β₁ β₂)))) ∧
    Tendsto (fun N => ZcalBare38 2 (alQ4Beta38 β₀ β₁ β₂) N /
      (∏ k ∈ Finset.Icc (-(N : ℤ)) N,
        Real.pi / finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) k))
      atTop (𝓝 (alQ4Z2_38 β₀ β₁ β₂)) := by
  refine ⟨fun g hg s hs => al078_cut h0 h1 h2 g hg s hs, fun s hs =>
    ⟨fun N => isProbabilityMeasure_nuBareS38 le_rfl (hβ_alQ4Beta38 h0 h1 h2) N s,
     isProbabilityMeasure_alQ4Rho38 h0 h1.le h2 s,
     fun F => (NlsGge.Birkhoff.L06_08a_free38 h0 h1 h2 hs F).1⟩,
    (NlsGge.Birkhoff.L06_08a_free38 h0 h1 h2 (s := 0) (by norm_num)
      (BoundedContinuousFunction.const (SobolevHilbert 0) (0 : ℝ))).2⟩

end NlsGge.ThirdConsultation.AL
