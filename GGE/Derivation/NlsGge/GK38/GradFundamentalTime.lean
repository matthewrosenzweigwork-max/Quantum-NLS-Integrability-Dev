import NlsGge.GK38.GradFundamentalIntegrals
import NlsGge.GK38.PairRealBridgeVC
import NlsGge.GK38.GradFundamentalStar

/-! # K1: absolutely continuous gauge primitives and their a.e. time derivatives.
GK Chapter I, Proposition3.1. The real-line extension has the accepted derivative
only a.e. inside the closed unit interval; endpoints are explicitly excluded.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory Set
namespace NlsGge.GK38
noncomputable section

theorem hasDerivAt_freeDiag38 (z : ℂ) (i : Fin 2) (s : ℝ) :
    HasDerivAt (fun r => freeE z r i i)
      (diagExp38 (-z) i * freeE z s i i) s := by
  fin_cases i
  · simpa [freeE, diagExp38, mul_neg, neg_mul] using hasDerivAt_cexp_mul (-(Complex.I * z)) s
  · simpa [freeE, diagExp38, mul_neg, neg_mul] using hasDerivAt_cexp_mul (Complex.I * z) s

theorem ac_freeDiag38 (z : ℂ) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun s => freeE z s i i) 0 1 := by
  have heq : (fun s => freeE z s i i) = (fun s => freeE (-z) (-s) i i) := by
    funext s
    fin_cases i <;> simp [freeE]
  rw [heq]
  exact (contDiff_freeE_neg_diag38 (-z) i).contDiffOn.absolutelyContinuousOnInterval

/-- An entrywise gauge primitive is AC after selecting the constant-ended extension. -/
theorem ac_gaugePrimitive38 (G : PairCont38) (z : ℂ) (C : PairMat38) (g : ℝ → PairMat38)
    (hg : ∀ i j, IntervalIntegrable (fun s => g s i j) volume 0 1)
    (hG : ∀ (t : Icc (0 : ℝ) 1) i j,
      G t i j = freeE z t i i * (C i j + ∫ s in (0 : ℝ)..(t : ℝ), g s i j))
    (i j : Fin 2) : AbsolutelyContinuousOnInterval (fun s => ext38 G s i j) 0 1 := by
  have hp := (absolutelyContinuousOnInterval_const38 (C i j) 0 1).add
    (ac_primitive38 (hg i j) Set.left_mem_uIcc)
  apply ((ac_freeDiag38 z i).smul hp).congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using hs
  change freeE z s i i * (C i j + ∫ r in (0 : ℝ)..s, g r i j) = ext38 G s i j
  rw [ext38_of_mem G hs']
  exact (hG ⟨s, hs'⟩ i j).symm

/-- The same primitive has its prescribed derivative away from the null endpoints. -/
theorem ae_hasDerivAt_gaugePrimitive38 (G : PairCont38) (z : ℂ) (C : PairMat38) (g : ℝ → PairMat38)
    (hg : ∀ i j, IntervalIntegrable (fun s => g s i j) volume 0 1)
    (hG : ∀ (t : Icc (0 : ℝ) 1) i j,
      G t i j = freeE z t i i * (C i j + ∫ s in (0 : ℝ)..(t : ℝ), g s i j))
    (i j : Fin 2) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun r => ext38 G r i j)
        (diagExp38 (-z) i * ext38 G s i j + freeE z s i i * g s i j) s := by
  filter_upwards [(hg i j).ae_hasDerivAt_integral, Measure.ae_ne (volume : Measure ℝ) 0,
    Measure.ae_ne (volume : Measure ℝ) 1] with s hp hs0 hs1 hs
  have hslt : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hsgt : s < 1 := lt_of_le_of_ne hs.2 hs1
  have hpi := (hp (by simpa [uIcc_of_le zero_le_one] using hs) 0 Set.left_mem_uIcc).const_add (C i j)
  have hder := (hasDerivAt_freeDiag38 z i s).mul hpi
  have heq : (fun r => ext38 G r i j) =ᶠ[𝓝 s]
      (fun r => freeE z r i i * (C i j + ∫ x in (0 : ℝ)..r, g x i j)) := by
    filter_upwards [Ioo_mem_nhds hslt hsgt] with r hr
    rw [ext38_of_mem G ⟨hr.1.le, hr.2.le⟩]
    exact hG ⟨r, hr.1.le, hr.2.le⟩ i j
  have h := hder.congr_of_eventuallyEq heq
  apply h.congr_deriv
  rw [ext38_of_mem G hs, hG ⟨s, hs⟩ i j]
  ring

end
end NlsGge.GK38
