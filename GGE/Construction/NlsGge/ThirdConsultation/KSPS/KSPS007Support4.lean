import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support
import NlsGge.ThirdConsultation.KSPS.KSPS007Support2
import NlsGge.ThirdConsultation.KSPS.KSPS007Support3

                                                                                                                     
                                                                                                                 
                                                                                   
                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2
open NlsGge.ThirdConsultation.KSPS007Support NlsGge.ThirdConsultation.KSPS007Support3
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS007Support4

def Fs (p : PotPair) (lam : ℂ) (g : ℝ → Fin 2 → ℂ) (t : ℝ) : Fin 2 → ℂ :=
  (Mf p lam t).mulVec (0 - ∫ s in (0 : ℝ)..t, ((Mf p lam s)⁻¹).mulVec (Rm.mulVec (g s)))

theorem Fs_sol (p : PotPair) (lam : ℂ) (f : PotPair) :
    (∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
        AbsolutelyContinuousOnInterval (fun t => Fs p lam (KSPSVolterra.forcingValue f) t i) 0 T) ∧
    (∀ t : ℝ, 0 ≤ t → Fs p lam (KSPSVolterra.forcingValue f) t = (freeE lam t).mulVec 0 +
      ∫ s in (0 : ℝ)..t, (freeE lam (t - s)).mulVec
        ((rawPotCoeff38 (potRepFst38 p) (potRepSnd38 p) s).mulVec
            (Fs p lam (KSPSVolterra.forcingValue f) s) -
          Rm.mulVec (KSPSVolterra.forcingValue f s))) :=
  (G1011_main p lam (KSPSVolterra.forcingValue f) 0 (hg_forcing f)
    (Fs p lam (KSPSVolterra.forcingValue f))).2 (fun t _ => rfl)

theorem Fs_cont (p : PotPair) (lam : ℂ) (f : PotPair) (k : Fin 2) :
    ContinuousOn (fun s => Fs p lam (KSPSVolterra.forcingValue f) s k) (Set.Icc (0 : ℝ) 1) := by
  have := ((Fs_sol p lam f).1 1 zero_le_one k).continuousOn
  rwa [Set.uIcc_of_le zero_le_one] at this

theorem Fs_duhamel_comp (p : PotPair) (lam : ℂ) (f : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin 2) :
    Fs p lam (KSPSVolterra.forcingValue f) t i = ∫ s in (0 : ℝ)..t, freeE lam (t - s) i i *
      (((PCm p s).mulVec (Fs p lam (KSPSVolterra.forcingValue f) s)) i -
        (Rm.mulVec (KSPSVolterra.forcingValue f s)) i) := by
  have hD := (Fs_sol p lam f).2 t ht.1
  have hint : ∀ j, IntervalIntegrable (fun s => ((freeE lam (t - s)).mulVec
      ((PCm p s).mulVec (Fs p lam (KSPSVolterra.forcingValue f) s) -
        Rm.mulVec (KSPSVolterra.forcingValue f s))) j) volume 0 t := by
    intro j
    have := duh_integrand_ii lam p f (v := Fs p lam (KSPSVolterra.forcingValue f)) (Fs_cont p lam f) j ht
    refine this.congr (fun s _ => ?_)
    simp only [freeE_mulVec_apply, Pi.sub_apply]
  have h1 := congrFun hD i
  rw [Pi.add_apply, Matrix.mulVec_zero, Pi.zero_apply, zero_add] at h1
  change Fs p lam (KSPSVolterra.forcingValue f) t i = (∫ s in (0 : ℝ)..t, (freeE lam (t - s)).mulVec
      ((PCm p s).mulVec (Fs p lam (KSPSVolterra.forcingValue f) s) -
        Rm.mulVec (KSPSVolterra.forcingValue f s))) i at h1
  rw [h1, ivInt_apply ht.1 hint i]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  simp only [freeE_mulVec_apply, Pi.sub_apply]

def Dm (F Fs : ℝ → Fin 2 → ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if j = 0 then F t i - Fs t i else 0

theorem trip_col (lam : ℂ) (p : PotPair) (F Fs : ℝ → Fin 2 → ℂ) (u s : ℝ) (i j : Fin 2) :
    (freeE lam u * PCm p s * Dm F Fs s) i j =
      freeE lam u i i * ((PCm p s).mulVec (fun k => Dm F Fs s k j)) i := by
  rw [NlsGge.Atomic.G1022S3.mul3_apply_col, freeE_mulVec_apply]
  congr 2
  funext k
  exact NlsGge.Atomic.G1022S3.mulVec_ej _ j k

theorem F_eq_Fs (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) (F : ℝ → Fin 2 → ℂ)
    (hF : KSPSVolterra.ForcedZS φ lam f F) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, F x = Fs (KSPSVolterra.toPair φ) lam (KSPSVolterra.forcingValue f) x := by
  set p := KSPSVolterra.toPair φ with hp
  have hFk : ∀ k, ContinuousOn (fun s => F s k) (Set.Icc (0 : ℝ) 1) :=
    fun k => (continuous_apply k).comp_continuousOn hF.1
  have hc : ∀ i j : Fin 2, ContinuousOn (fun t => Dm F (Fs p lam (KSPSVolterra.forcingValue f)) t i j)
      (Set.Icc (0 : ℝ) 1) := by
    intro i j
    rcases fin2_cases j with rfl | rfl
    · simp only [Dm, if_true]
      exact (hFk i).sub (Fs_cont p lam f i)
    · have h0 : (fun t => Dm F (Fs p lam (KSPSVolterra.forcingValue f)) t i 1) = fun _ => 0 := by
        funext t; simp [Dm]
      rw [h0]
      exact continuousOn_const
  have hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      Dm F (Fs p lam (KSPSVolterra.forcingValue f)) t i j = ∫ s in (0 : ℝ)..t,
        (freeZsFundamentalComplex lam (t - s) *
          rawPotCoeff38 (potRepFst38 p) (potRepSnd38 p) s *
          Dm F (Fs p lam (KSPSVolterra.forcingValue f)) s) i j := by
    intro t ht i j
    simp only [← freeE_eq]
    have e : ∀ s, (freeE lam (t - s) * rawPotCoeff38 (potRepFst38 p) (potRepSnd38 p) s *
        Dm F (Fs p lam (KSPSVolterra.forcingValue f)) s) i j =
        freeE lam (t - s) i i * ((PCm p s).mulVec (fun k => Dm F (Fs p lam (KSPSVolterra.forcingValue f)) s k j)) i :=
      fun s => trip_col lam p F _ (t - s) s i j
    simp only [e]
    rcases fin2_cases j with rfl | rfl
    · have e0 : ∀ s, (fun k => Dm F (Fs p lam (KSPSVolterra.forcingValue f)) s k 0) =
          F s - Fs p lam (KSPSVolterra.forcingValue f) s := by
        intro s; funext k; simp [Dm]
      simp only [e0]
      simp only [Dm, if_true]
      rw [forced_duhamel_comp φ lam f F hF ht i, Fs_duhamel_comp p lam f ht i,
        ← intervalIntegral.integral_sub (duh_integrand_ii lam p f hFk i ht)
          (duh_integrand_ii lam p f (Fs_cont p lam f) i ht)]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [Matrix.mulVec_sub, Pi.sub_apply]
      ring
    · have h0 : ∀ s, freeE lam (t - s) i i * ((PCm p s).mulVec
          (fun k => Dm F (Fs p lam (KSPSVolterra.forcingValue f)) s k 1)) i = 0 := by
        intro s
        have h00 : (fun k => Dm F (Fs p lam (KSPSVolterra.forcingValue f)) s k 1) = 0 := by
          funext k; simp [Dm]
        rw [h00, Matrix.mulVec_zero]; simp
      simp only [h0, intervalIntegral.integral_zero]
      simp [Dm]
  have hz := NlsGge.Atomic.G1007.uniqueness_core p lam zero_le_one
    (Dm F (Fs p lam (KSPSVolterra.forcingValue f))) hc hD
  intro x hx
  funext i
  have := congrFun (congrFun (hz x hx) i) 0
  simp only [Dm, if_true, Matrix.zero_apply] at this
  exact sub_eq_zero.mp this

theorem forced_eq_formula (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) (F : ℝ → Fin 2 → ℂ)
    (hF : KSPSVolterra.ForcedZS φ lam f F) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    F x = (KSPSVolterra.fundamental φ x lam).mulVec
      (0 - ∫ s in (0 : ℝ)..x, (KSPSVolterra.inverseFundamental φ s lam).mulVec
        (KSPSVolterra.R.mulVec (KSPSVolterra.forcingValue f s))) := by
  rw [F_eq_Fs φ lam f F hF x hx, Fs, ← fundamental_eq_Mf φ lam hx.1]
  congr 2
  refine intervalIntegral.integral_congr (fun s hs => ?_)
  rw [Set.uIcc_of_le hx.1] at hs
  rw [inverseFundamental_eq_inv φ lam hs.1, fundamental_eq_Mf φ lam hs.1]
  rfl

end NlsGge.ThirdConsultation.KSPS007Support4
