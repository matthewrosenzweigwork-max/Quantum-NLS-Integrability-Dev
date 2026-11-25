import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential

                                                                                           
                                                                                             
                                                                                             
                                                                                        

set_option autoImplicit false

open MeasureTheory NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT

namespace NlsGge.Atomic.G1007

noncomputable section

/-- The restriction of a continuous matrix function to `[0,T]`. -/
def restrictT (D : ℝ → Matrix (Fin 2) (Fin 2) ℂ) {T : ℝ}
    (hc : ∀ i j : Fin 2, ContinuousOn (fun t => D t i j) (Set.Icc (0 : ℝ) T)) : PairContT T :=
  ⟨fun t => fun i j => D t.1 i j, by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact ((hc i j).comp_continuous continuous_subtype_val (fun t => t.2))⟩

theorem restrictT_apply (D : ℝ → Matrix (Fin 2) (Fin 2) ℂ) {T : ℝ}
    (hc : ∀ i j : Fin 2, ContinuousOn (fun t => D t i j) (Set.Icc (0 : ℝ) T))
    (t : Set.Icc (0 : ℝ) T) (i j : Fin 2) : restrictT D hc t i j = D t.1 i j := rfl

theorem uniqueness_core (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T)
    (D : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hc : ∀ i j : Fin 2, ContinuousOn (fun t => D t i j) (Set.Icc (0 : ℝ) T))
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j : Fin 2,
      D t i j = ∫ s in (0 : ℝ)..t,
        (freeZsFundamentalComplex z (t - s) *
          rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s * D s) i j) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, D t = 0 := by
  set N : PairContT T := restrictT D hc with hN
  have hfix : volterraPT φ z hT N = N := by
    ext t i j
    rw [volterraPT_apply, volterraFunT_apply, restrictT_apply, hD t.1 t.2 i j]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs' : s ∈ Set.Icc (0 : ℝ) T := by
      rw [Set.uIcc_of_le t.2.1] at hs
      exact ⟨hs.1, hs.2.trans t.2.2⟩
    rw [ext38T_of_mem hT N hs', ← freeE_eq]
    rfl
  have hu := isUnit_one_sub_volterraPT φ z hT
  have h0 : (1 - volterraPT φ z hT) N = 0 := by
    simp [ContinuousLinearMap.sub_apply, hfix]
  have hN0 : N = 0 := by
    have h1 := congrArg (fun S : PairContT T →L[ℂ] PairContT T => S N)
      (Ring.inverse_mul_cancel _ hu)
    simp only [ContinuousLinearMap.mul_apply] at h1
    rw [h0, map_zero] at h1
    simpa using h1.symm
  intro t ht
  ext i j
  have := congrArg (fun G : PairContT T => G ⟨t, ht⟩ i j) hN0
  simpa [hN, restrictT_apply] using this

theorem G1007_uniqueness :
    (∀ (φ : PotPair) (z : ℂ) (U V : ℝ → Matrix (Fin 2) (Fin 2) ℂ),
  let SolvesZS : (ℝ → Matrix (Fin 2) (Fin 2) ℂ) → Prop := fun W =>
    (∀ T : ℝ, 0 ≤ T → ∀ i j : Fin 2,
      IntervalIntegrable
        (fun s : ℝ => (freeZsFundamentalComplex z (T - s) *
          rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s * W s) i j)
        MeasureTheory.volume 0 T) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ i j : Fin 2,
      W t i j = (freeZsFundamentalComplex z t) i j +
        ∫ s in (0 : ℝ)..t,
          (freeZsFundamentalComplex z (t - s) *
            rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) s * W s) i j) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ i j : Fin 2,
      AbsolutelyContinuousOnInterval (fun t : ℝ => W t i j) 0 T)
  SolvesZS U → SolvesZS V → U 0 = V 0 → ∀ t : ℝ, 0 ≤ t → U t = V t
  : Prop) := by
  intro φ z U V SolvesZS hU hV _ t ht
  obtain ⟨hU1, hU2, hU3⟩ := hU
  obtain ⟨hV1, hV2, hV3⟩ := hV
  set D : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s => U s - V s with hDdef
  have hc : ∀ i j : Fin 2, ContinuousOn (fun s => D s i j) (Set.Icc (0 : ℝ) t) := by
    intro i j
    have h := ((hU3 t ht i j).sub (hV3 t ht i j)).continuousOn
    rw [Set.uIcc_of_le ht] at h
    exact h
  have hD : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ i j : Fin 2,
      D s i j = ∫ r in (0 : ℝ)..s,
        (freeZsFundamentalComplex z (s - r) *
          rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) r * D r) i j := by
    intro s hs i j
    have hs0 := hs.1
    have iU : IntervalIntegrable (fun r : ℝ => (freeZsFundamentalComplex z (s - r) *
        rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) r * U r) i j) volume 0 s := hU1 s hs0 i j
    have iV : IntervalIntegrable (fun r : ℝ => (freeZsFundamentalComplex z (s - r) *
        rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) r * V r) i j) volume 0 s := hV1 s hs0 i j
    have e : ∀ r : ℝ, (freeZsFundamentalComplex z (s - r) *
        rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) r * D r) i j =
        (freeZsFundamentalComplex z (s - r) *
          rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) r * U r) i j -
        (freeZsFundamentalComplex z (s - r) *
          rawPotCoeff38 (potRepFst38 φ) (potRepSnd38 φ) r * V r) i j := by
      intro r
      simp only [hDdef, Matrix.mul_sub, Matrix.sub_apply]
    simp_rw [e]
    rw [intervalIntegral.integral_sub iU iV]
    have := hU2 s hs0 i j
    have := hV2 s hs0 i j
    simp only [hDdef, Matrix.sub_apply]
    linear_combination (hU2 s hs0 i j) - (hV2 s hs0 i j)
  have h := uniqueness_core φ z ht D hc hD t ⟨ht, le_rfl⟩
  ext i j
  have := congrFun (congrFun h i) j
  simpa [hDdef, sub_eq_zero] using this

end

end NlsGge.Atomic.G1007

