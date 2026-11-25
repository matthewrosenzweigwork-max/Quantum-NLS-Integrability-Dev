import Mathlib
import NlsGge.Atomic.M.M026
import NlsGge.ThirdConsultation.M.M023Analytic
import NlsGge.ThirdConsultation.M.MSchurBound
import NlsGge.ThirdConsultation.M.M027Analytic

   
                                                                                                 

                                                                                          

                                                                                                              
                                                                                                             
                                                                                                                   
                                                                                    
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M029A

open NlsGge.ThirdConsultation.MTwoMode NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
open NlsGge.ThirdConsultation.MTwoModeB
open NlsGge.ThirdConsultation.M027A

theorem analytic_general_even (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * potentialCoefficientNorm w φ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n)
    (i j : Bool) (jj : Bool × ℤ)
    (hjj : ∀ g : NlsGge.Atomic.KST003.KSTPairL2,
      inner ℂ (schurFrame n i : NlsGge.Atomic.KST003.KSTPairL2) g = coefficientPair g jj.1 jj.2)
    (hE : shiftedPairEnergy w n false (coefficientPair
      (NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
        (schurFrame n j : NlsGge.Atomic.KST003.KSTPairL2))) ≠ ⊤) :
    ∃ a : ℂ → ℂ,
      AnalyticOnNhd ℂ a (NlsGge.Atomic.KST004.spectralStrip n) ∧
      ∀ (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n),
        HasSum (fun r : ℕ => schurPathTerm φ n lam hlam (2 * r + 2) i j) (a lam) := by
  obtain ⟨b1, _, b3, b4, _, b6⟩ := weighted_code_bridges w hw n
  obtain ⟨a, ha, -⟩ := b1 φ hφ
  obtain ⟨-, hNa⟩ := b3 a φ ha
  have hth : 8 * ‖a‖ ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n := by rw [← hNa]; exact hthreshold
  set f0 := NlsGge.Atomic.KST012.potentialOnPn (schurPhysicalPair φ) n
    (schurFrame n j : NlsGge.Atomic.KST003.KSTPairL2) with hf0
  obtain ⟨x0, hx0, -⟩ := b4 f0 hE
  let L : (SourceCode w n →L[ℂ] SourceCode w n) →L[ℂ] ℂ :=
    ((shiftWeight w n jj.1 jj.2 : ℂ)⁻¹) •
      ((lp.evalCLM ℂ (fun _ : Bool × ℤ => ℂ) 2 jj).comp
        (ContinuousLinearMap.apply ℂ (SourceCode w n) x0))
  have hLapp : ∀ X : SourceCode w n →L[ℂ] SourceCode w n,
      L X = ((shiftWeight w n jj.1 jj.2 : ℂ)⁻¹) * (X x0 jj) := fun X => rfl
  refine ⟨fun lam => L ((Tw w hw n (lam, a) * Tw w hw n (lam, a)) *
    evenNeumann (Tw w hw n (lam, a))), ?_, ?_⟩
  · intro lam0 hlam0
    have hp := analyticAt_evenNeumann w hw n (lam0, a) hlam0 hth
    have hT := analyticAt_Tw w hw n (lam0, a) hlam0
    have hF : AnalyticAt ℂ (fun q : ℂ × PotentialCode w =>
        (Tw w hw n q * Tw w hw n q) * evenNeumann (Tw w hw n q)) (lam0, a) :=
      (hT.mul hT).mul hp.1
    have hg : AnalyticAt ℂ (fun lam : ℂ => (lam, a)) lam0 :=
      AnalyticAt.prod (f := fun lam : ℂ => lam) (g := fun _ : ℂ => a) analyticAt_id analyticAt_const
    have hFg := AnalyticAt.comp (g := fun q : ℂ × PotentialCode w =>
        (Tw w hw n q * Tw w hw n q) * evenNeumann (Tw w hw n q)) (f := fun lam : ℂ => (lam, a)) hF hg
    exact (L.analyticAt _).comp hFg
  · intro lam hlam
    obtain ⟨-, hsum, -⟩ := Tw_neumann w hw n (lam, a) hlam hth
    have hS := hsum.mul_left (Tw w hw n (lam, a) * Tw w hw n (lam, a))
    have hL := L.hasSum hS
    have hterm : ∀ r : ℕ, L ((Tw w hw n (lam, a) * Tw w hw n (lam, a)) *
        (Tw w hw n (lam, a) * Tw w hw n (lam, a)) ^ r) =
        schurPathTerm φ n lam hlam (2 * r + 2) i j := by
      intro r
      have e : (Tw w hw n (lam, a) * Tw w hw n (lam, a)) *
          (Tw w hw n (lam, a) * Tw w hw n (lam, a)) ^ r =
          (Tw w hw n (lam, a)) ^ (2 * r + 2) := by
        rw [← pow_succ' (Tw w hw n (lam, a) * Tw w hw n (lam, a)) r, ← sq, ← pow_mul]
        congr 1
      rw [e, hLapp]
      have h2 : (((Tw w hw n (lam, a)) ^ (2 * r + 2)) x0) jj =
          (shiftWeight w n jj.1 jj.2 : ℂ) *
            coefficientPair (((ambientT φ n lam hlam) ^ (2 * r + 2)) f0) jj.1 jj.2 :=
        rep_pow w hw φ n a ha lam hlam x0 f0 hx0 (2 * r + 2) jj.1 jj.2
      rw [h2, ← mul_assoc, inv_mul_cancel₀ (weight_ne w hw n jj.1 jj.2), one_mul]
      exact (hjj _).symm
    have hfun : (fun r : ℕ => L ((Tw w hw n (lam, a) * Tw w hw n (lam, a)) *
        (Tw w hw n (lam, a) * Tw w hw n (lam, a)) ^ r)) =
        fun r : ℕ => schurPathTerm φ n lam hlam (2 * r + 2) i j := funext hterm
    rw [hfun] at hL
    exact hL

end NlsGge.ThirdConsultation.M029A

namespace NlsGge.ThirdConsultation.M

open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation

theorem schur_off_diagonal_analytic_extension
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    ∃ b : ℂ → ℂ,
      AnalyticOnNhd ℂ b (NlsGge.Atomic.KST004.spectralStrip n) ∧
      ∀ z : ℂ, ∀ hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n,
        b z = MTwoMode.offDiagonal φ n z hz plus := by
  have key : ∃ a : ℂ → ℂ,
      AnalyticOnNhd ℂ a (NlsGge.Atomic.KST004.spectralStrip n) ∧
      ∀ (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n),
        a lam = MTwoMode.schurEvenRemainder φ n lam hlam plus := by
    cases plus
    · obtain ⟨a, ha, hs⟩ := NlsGge.ThirdConsultation.M029A.analytic_general_even w hw φ hφ n
        hthreshold true false (true, -n)
        (fun g => NlsGge.ThirdConsultation.MTwoModeB.inner_frame_true n g)
        (by
          rw [NlsGge.ThirdConsultation.MTwoModeB.shifted_V_lower]
          exact NlsGge.ThirdConsultation.MTwoModeB.compEnergy_ne_top w φ hφ false)
      exact ⟨a, ha, fun lam hlam => by
        unfold MTwoMode.schurEvenRemainder
        exact ((hs lam hlam).tsum_eq).symm⟩
    · obtain ⟨a, ha, hs⟩ := NlsGge.ThirdConsultation.M029A.analytic_general_even w hw φ hφ n
        hthreshold false true (false, n)
        (fun g => NlsGge.ThirdConsultation.MTwoModeB.inner_frame_false n g)
        (by
          rw [NlsGge.ThirdConsultation.MTwoModeB.shifted_V_upper]
          exact NlsGge.ThirdConsultation.MTwoModeB.compEnergy_ne_top w φ hφ true)
      exact ⟨a, ha, fun lam hlam => by
        unfold MTwoMode.schurEvenRemainder
        exact ((hs lam hlam).tsum_eq).symm⟩
  obtain ⟨a, ha, hs⟩ := key
  refine ⟨fun z => MTwoMode.fourierPotential φ plus (if plus then 2 * n else -2 * n) + a z,
    fun z hz => analyticAt_const.add (ha z hz), ?_⟩
  intro z hz
  have h := schur_fourier_remainder_weighted w hw φ hφ n z hz hthreshold plus
  show MTwoMode.fourierPotential φ plus (if plus then 2 * n else -2 * n) + a z = _
  rw [hs z hz, ← h]
  ring

end NlsGge.ThirdConsultation.M

end
