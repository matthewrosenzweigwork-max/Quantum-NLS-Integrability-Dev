import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support
import NlsGge.ThirdConsultation.KSPS.KSPS007Support2

/- KSPS-007 SUPPORT03 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS007Support3.lean.
   Structure of ForcedZS solutions: (b) the ForcedZS integral equation gives the componentwise Duhamel equation on [0,1];
   (c) uniqueness (G1-007) against the G1-011 formula solution; (d) F x = M x (0 - int_0^x M^{-1} R g) with M^{-1} = adjugate2 M. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2
open NlsGge.ThirdConsultation.KSPS007Support
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS007Support3

theorem forcingValue_zero (f : PotPair) (t : ℝ) : KSPSVolterra.forcingValue f t 0 = potRepFst38 f t := by
  simp [KSPSVolterra.forcingValue]

theorem forcingValue_one (f : PotPair) (t : ℝ) : KSPSVolterra.forcingValue f t 1 = potRepSnd38 f t := by
  simp [KSPSVolterra.forcingValue]

theorem hg_forcing (f : PotPair) : ∀ T : ℝ, 0 ≤ T → ∀ i : Fin 2,
    MemLp (fun s : ℝ => KSPSVolterra.forcingValue f s i) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  intro T hT i
  rcases fin2_cases i with rfl | rfl
  · have := NlsGge.Atomic.G1022S3.memLp_cr_mul f.1 hT (m := fun _ => (1 : ℂ)) continuousOn_const
    simpa [forcingValue_zero, potRepFst38] using this
  · have := NlsGge.Atomic.G1022S3.memLp_cr_mul f.2 hT (m := fun _ => (1 : ℂ)) continuousOn_const
    simpa [forcingValue_one, potRepSnd38] using this

theorem g_ii (f : PotPair) (i : Fin 2) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => KSPSVolterra.forcingValue f s i) volume 0 T :=
  g_int (hg_forcing f) hT i

theorem PCm_mulVec_ii (p : PotPair) {v : ℝ → Fin 2 → ℂ}
    (hv : ∀ k, ContinuousOn (fun s => v s k) (Set.Icc (0 : ℝ) 1)) (i : Fin 2) :
    IntervalIntegrable (fun s => ((PCm p s).mulVec (v s)) i) volume 0 1 := by
  have hv' : ∀ k, ContinuousOn (fun s => v s k) (Set.uIcc (0 : ℝ) 1) := by
    intro k; rw [Set.uIcc_of_le zero_le_one]; exact hv k
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ((PC_int p i 0).mul_continuousOn (hv' 0)).add ((PC_int p i 1).mul_continuousOn (hv' 1))

/-- the integrand of the componentwise Duhamel equation is interval integrable on `[0,t]`, `t ≤ 1`. -/
theorem duh_integrand_ii (lam : ℂ) (p f : _) {v : ℝ → Fin 2 → ℂ}
    (hv : ∀ k, ContinuousOn (fun s => v s k) (Set.Icc (0 : ℝ) 1)) (i : Fin 2) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun s => freeE lam (t - s) i i *
      (((PCm p s).mulVec (v s)) i - (Rm.mulVec (KSPSVolterra.forcingValue f s)) i)) volume 0 t := by
  have h1 : IntervalIntegrable (fun s => ((PCm p s).mulVec (v s)) i) volume 0 t :=
    (PCm_mulVec_ii p hv i).mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl ht.2)
  have h2 : IntervalIntegrable (fun s => (Rm.mulVec (KSPSVolterra.forcingValue f s)) i) volume 0 t := by
    rcases fin2_cases i with rfl | rfl
    · simp only [Rm_apply0]; exact (g_ii f 0 ht.1).const_mul _
    · simp only [Rm_apply1]; exact ((g_ii f 1 ht.1).const_mul _).neg
  have hc : ContinuousOn (fun s : ℝ => freeE lam (t - s) i i) (Set.uIcc 0 t) :=
    (((continuous_freeE lam).comp (continuous_const.sub continuous_id)).matrix_elem i i).continuousOn
  exact (h1.sub h2).continuousOn_mul hc

/-- ForcedZS => componentwise Duhamel on [0,1]. -/
theorem forced_duhamel_comp (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair)
    (F : ℝ → Fin 2 → ℂ) (hF : KSPSVolterra.ForcedZS φ lam f F) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin 2) :
    F x i = ∫ s in (0 : ℝ)..x, freeE lam (x - s) i i *
      (((PCm (KSPSVolterra.toPair φ) s).mulVec (F s)) i - (Rm.mulVec (KSPSVolterra.forcingValue f s)) i) := by
  obtain ⟨hFc, hF0, hFe⟩ := hF
  set p := KSPSVolterra.toPair φ with hp
  have hFk : ∀ k, ContinuousOn (fun s => F s k) (Set.Icc (0 : ℝ) 1) :=
    fun k => (continuous_apply k).comp_continuousOn hFc
  set a : ℂ := if i = 0 then -(Complex.I * lam) else Complex.I * lam with ha
  set b : ℝ → ℂ := fun s => ((PCm p s).mulVec (F s)) i - (Rm.mulVec (KSPSVolterra.forcingValue f s)) i with hb
  have hbi : IntervalIntegrable b volume 0 1 := by
    have h1 := PCm_mulVec_ii p hFk i
    have h2 : IntervalIntegrable (fun s => (Rm.mulVec (KSPSVolterra.forcingValue f s)) i) volume 0 1 := by
      rcases fin2_cases i with rfl | rfl
      · simp only [Rm_apply0]; exact (g_ii f 0 zero_le_one).const_mul _
      · simp only [Rm_apply1]; exact ((g_ii f 1 zero_le_one).const_mul _).neg
    exact h1.sub h2
  have hψ : ∀ t : ℝ, ((((-(lam • KSPSVolterra.R) + KSPSVolterra.R * KSPSVolterra.phi p t) *ᵥ F t) -
      KSPSVolterra.R *ᵥ KSPSVolterra.forcingValue f t)) i = a * F t i + b t := by
    intro t
    rw [Pi.sub_apply, Matrix.add_mulVec, R_mul_phi, Pi.add_apply]
    rcases fin2_cases i with rfl | rfl
    · simp [ha, hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two, KSPSVolterra.R, Rm]
      ring
    · simp [ha, hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two, KSPSVolterra.R, Rm]
      ring
  have hd : ∀ y ∈ Set.Icc (0 : ℝ) 1, F y i = ∫ t in (0 : ℝ)..y, (a * F t i + b t) := by
    intro y hy
    have := congrFun (hFe y hy) i
    rw [this]
    show (∫ t in (0 : ℝ)..y, _) = _
    exact intervalIntegral.integral_congr (fun t _ => hψ t)
  have key := NlsGge.ThirdConsultation.KSPS007Support2.ode_duhamel_scalar a (hFk i) hbi hd x hx
  rw [key]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  show Complex.exp (a * ((x : ℂ) - (t : ℂ))) * b t = freeE lam (x - t) i i * b t
  congr 1
  rcases fin2_cases i with rfl | rfl
  · simp only [ha, freeE]; simp
  · simp only [ha, freeE]; simp

end NlsGge.ThirdConsultation.KSPS007Support3
