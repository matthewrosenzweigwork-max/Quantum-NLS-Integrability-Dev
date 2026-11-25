import Mathlib
import NlsGge.Atomic.G4.G4037Reg
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.Atomic.X.X006
import NlsGge.GK38.PeriodicAsymptotics
import Armstrong.Work.RawBetaMagnitudeODEBridge
import Armstrong.Work.RawBetaMagnitudeEndpointPlacement
import Armstrong.Work.RawBetaMagnitudeInverseGeometry
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_characterization38

                                                                                                         
                                                                                                                               
                                                                                                                                    
                                                                                                                                           
                                                                                  
                                                                                                            
                                                                                                                                               
                                                                                    
                                                                                                                                           
                                                                                                                        
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G4037Aux

theorem g4037_local_nearest (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
    ∃ δ C0 : ℝ, 0 < δ ∧ 0 < C0 ∧ ball φ0 δ ⊆ sourceW ∧
      ∀ ψ ∈ ball φ0 δ, ∀ n m : ℤ, m ≠ n →
        ‖offDiagonalBeta n m ψ‖ ≤
          C0 * Real.sqrt (‖lamPlus ψ m - lamMinus ψ m‖ +
            min ‖muSeq ψ m - lamMinus ψ m‖ ‖muSeq ψ m - lamPlus ψ m‖) *
            Real.sqrt (min ‖muSeq ψ m - lamMinus ψ m‖ ‖muSeq ψ m - lamPlus ψ m‖) *
            Lib.c3w n m := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  obtain ⟨V1, Br, hV1o, hφ0V1, hV1W, hBr, hreg⟩ := g4037_reg_factor φ0 hφ0
  obtain ⟨V2, hV2o, hφ0V2, hV2W, BQ, hBQ, hA⟩ :=
    NlsGge.Atomic.ExistingPhysicalFamily.actualPhysicalLocalFamily_quadratic_mass φ0 hφ0
  obtain ⟨Up, hUp, Cp, hCp, hp⟩ := periodic_l2_summable38 φ0
  obtain ⟨rp, hrp, hrpU⟩ := Metric.mem_nhds_iff.mp hUp
  obtain ⟨r1, hr1, hr1V⟩ := Metric.isOpen_iff.mp hV1o φ0 hφ0V1
  obtain ⟨r2, hr2, hr2V⟩ := Metric.isOpen_iff.mp hV2o φ0 hφ0V2
  let G : ℝ := Real.sqrt (2 * Cp)
  let L : ℝ := 1 / 2 + G * Real.sqrt BQ
  let δ : ℝ := min r1 (min r2 rp)
  let C0 : ℝ := 2 * Br * Real.sqrt (1 + 2 * L) * Real.sqrt (L + 1)
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hδ : 0 < δ := lt_min hr1 (lt_min hr2 hrp)
  have hC0 : 0 < C0 := by
    dsimp [C0]
    positivity
  have hsub1 : ball φ0 δ ⊆ V1 := (ball_subset_ball (min_le_left _ _)).trans hr1V
  have hsub2 : ball φ0 δ ⊆ V2 :=
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))).trans hr2V
  have hsubp : ball φ0 δ ⊆ Up :=
    (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans hrpU
  refine ⟨δ, C0, hδ, hC0, fun x hx => hV1W (hsub1 hx), ?_⟩
  intro ψ hψ n m hmn
  have hψV1 : ψ ∈ V1 := hsub1 hψ
  have hψW : ψ ∈ sourceW := hV1W hψV1
  have hψgk : ψ ∈ gkW := sourceFamily.W_gk hψW
  let Cb : ℤ → ℂ := discC φ0
  let Rb : ℤ → ℝ := discR φ0
  obtain ⟨hfampsi, hregψ⟩ := hreg ψ hψV1
  let S : Lib.L2Seq := g4037S n ψ (Cb n)
  obtain ⟨c0, N0, hgeom0, hspec0⟩ := hfampsi
  have hfampsi' : IsolatingFamily38 ψ Cb Rb := ⟨c0, N0, hgeom0, hspec0⟩
  have hsn : Lib.sigmaOf S n ∈ closedBall (Cb n) (Rb n) := by
    dsimp only [S]
    rw [g4037S_sigma_self]
    exact mem_closedBall_self (hgeom0.1 n).1.le
  have hsigma_m : Lib.sigmaOf S m = countingCenter38 m + sourceF n ψ ⟨m, hmn⟩ :=
    g4037S_sigma_ne n ψ (Cb n) m hmn
  have hnum : p6PsiNumerator38 n (sourceF n) ψ = p2FullNumerator38 n S :=
    (g4037S_numerator n ψ (Cb n)).symm
  have hper : abelianPeriod38 m ψ (p6PsiNumerator38 n (sourceF n) ψ) = 0 := by
    have h := sourceFamily.F_period n ψ hψW m
    rwa [if_neg hmn] at h
  let gphi : GKPotential38 := ⟨ψ, hψgk⟩
  have hbridge :=
    gk151_fixedCoefficient_quadratic_terminal_bridge38
      n m hmn sourceF gphi Cb Rb hfampsi' S hsn hnum hper
  let a : ℂ := lamMinus ψ m
  let b : ℂ := lamPlus ψ m
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (ψ, z)
  let Rc : ℂ → ℂ := rawBetaFixedCoefficient38 n m (sourceF n) ψ (Cb m) (Rb m)
  let T : ℂ → ℂ := fun z => K * D z * Rc z
  have hT : AnalyticOnNhd ℂ T (ball (Cb m) (Rb m)) := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.1
  have hode : ∀ z ∈ ball (Cb m) (Rb m),
      (z - a) * (z - b) * deriv T z + (z - (a + b) / 2) * T z =
        (Lib.sigmaOf S m - z) * angleRegularFactor38 n m ((ψ, S), z) := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.2.1
  have hsource : GKSourceBetaValue38 n m hmn sourceF gphi
      (antiDiscrim ψ (muSeq ψ m) * Rc (muSeq ψ m)) := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.2.2.1
  have hterminal :
      ‖antiDiscrim ψ (muSeq ψ m) * Rc (muSeq ψ m)‖ =
        Real.sqrt (‖(muSeq ψ m - a) * (muSeq ψ m - b)‖) * ‖T (muSeq ψ m)‖ := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.2.2.2
  let pW : {chi : PotPair // chi ∈ sourceW} := ⟨ψ, hψW⟩
  have hchar :=
    gkSourceBeta_characterization38 sourceW sourceFamily.W_open sourceFamily.W_real
      sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
      sourceFamily.F_period n m hmn pW
  have hsource' : GKSourceBetaValue38 n m hmn sourceF ⟨pW.1, sourceFamily.W_gk pW.2⟩
      (antiDiscrim ψ (muSeq ψ m) * Rc (muSeq ψ m)) := by
    simpa only [pW, gphi] using hsource
  have hbeta :
      antiDiscrim ψ (muSeq ψ m) * Rc (muSeq ψ m) =
        gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
          sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
          sourceFamily.F_period n m hmn pW :=
    hchar.2.1 _ hsource'
  have heq := gk151BetaAmbient_eq_source38 sourceW sourceFamily.W_open
    sourceFamily.W_real sourceFamily.W_gk sourceF sourceFamily.F_analytic
    sourceFamily.F_zero sourceFamily.F_period n m hmn pW
  have hoff : offDiagonalBeta n m ψ =
      gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
        sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
        sourceFamily.F_period n m hmn pW := heq
  obtain ⟨cs, Ns, hgeoms, hspecs⟩ := hfampsi'
  have ha : a ∈ ball (Cb m) (Rb m) := (hspecs.1 m).1 (left_mem_segment ℝ _ _)
  have hb : b ∈ ball (Cb m) (Rb m) := (hspecs.1 m).1 (right_mem_segment ℝ _ _)
  have hmu : muSeq ψ m ∈ ball (Cb m) (Rb m) := (hspecs.1 m).2.1
  have hconv : Convex ℝ (ball (Cb m) (Rb m)) := convex_ball _ _
  have hfampsi'' : IsolatingFamily38 ψ Cb Rb := ⟨cs, Ns, hgeoms, hspecs⟩
  have hzeta : ContinuousOn
      (fun z => angleRegularFactor38 n m ((ψ, S), z)) (ball (Cb m) (Rb m)) := by
    intro z hz
    have haJoint := angleRegularFactor_joint_own_disc38 n m (Ne.symm hmn)
      ψ hψgk Cb Rb hfampsi'' S hsn z (ball_subset_closedBall hz)
    have haOne : AnalyticAt ℂ
        (fun w : ℂ => angleRegularFactor38 n m ((ψ, S), w)) z :=
      AnalyticAt.comp (g := angleRegularFactor38 n m)
        (f := fun w : ℂ => ((ψ, S), w)) haJoint
        (analyticAt_const.prod analyticAt_id)
    exact haOne.continuousAt.continuousWithinAt
  have hZ : 0 ≤ Br * Lib.c3w n m := mul_nonneg hBr.le (Lib.c3w_nonneg n m)
  have hzetaBound : ∀ z ∈ ball (Cb m) (Rb m),
      ‖angleRegularFactor38 n m ((ψ, S), z)‖ ≤ Br * Lib.c3w n m := fun z hz =>
    hregψ n m hmn z hz
  -- placement from the retained quadratic mass
  obtain ⟨A, hAfac, hAsum, hAB⟩ := hA ψ (hsub2 hψ) n
  let mi : P2Index38 n := ⟨m, hmn⟩
  have htermA : ‖A mi‖ ^ 2 ≤ ∑' k : P2Index38 n, ‖A k‖ ^ 2 := by
    simpa only [Finset.sum_singleton] using
      hAsum.sum_le_tsum ({mi} : Finset (P2Index38 n)) (fun _ _ => sq_nonneg _)
  have hApoint2 : ‖A mi‖ ^ 2 ≤ BQ := htermA.trans hAB
  have hApoint : ‖A mi‖ ≤ Real.sqrt BQ := by
    nlinarith [Real.sq_sqrt hBQ.le, Real.sqrt_nonneg BQ]
  obtain ⟨hpsum, hpB⟩ := hp ψ (hsubp hψ)
  have hpterm :
      ‖lamMinus ψ m - (m : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
        ‖lamPlus ψ m - (m : ℂ) * (Real.pi : ℂ)‖ ^ 2 ≤
          ∑' k : ℤ, (‖lamMinus ψ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
            ‖lamPlus ψ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
    simpa only [Finset.sum_singleton] using
      hpsum.sum_le_tsum ({m} : Finset ℤ) (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hgapSq : ‖lamPlus ψ m - lamMinus ψ m‖ ^ 2 ≤ 2 * Cp := by
    calc _ ≤ 2 * (‖lamMinus ψ m - (m : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
           ‖lamPlus ψ m - (m : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
          (pair_value_square_bounds38 (lamPlus ψ m) (lamMinus ψ m) ((m : ℂ) * (Real.pi : ℂ))).2
      _ ≤ 2 * (∑' k : ℤ, (‖lamMinus ψ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2 +
            ‖lamPlus ψ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hpterm (by norm_num)
      _ ≤ 2 * Cp := mul_le_mul_of_nonneg_left hpB (by norm_num)
  have h2Cp : 0 ≤ 2 * Cp := by positivity
  have hgap : ‖lamPlus ψ m - lamMinus ψ m‖ ≤ G := by
    dsimp [G]
    nlinarith [Real.sq_sqrt h2Cp, Real.sqrt_nonneg (2 * Cp)]
  have hsigma :
      countingCenter38 m + sourceF n ψ mi =
        (lamMinus ψ m + lamPlus ψ m) / 2 +
          (lamPlus ψ m - lamMinus ψ m) ^ 2 * A mi := by
    have h : countingCenter38 m + sourceF n ψ mi = tauN ψ m + gamma2 ψ m * A mi := hAfac mi
    rw [h, tauN_value38 ψ hψgk m, gamma2_value38 ψ hψgk m]
    ring
  have hplace := gk151_quadratic_root_endpoint_bound38
    (lamMinus ψ m) (lamPlus ψ m) (countingCenter38 m + sourceF n ψ mi) (A mi) G BQ
    hG0 hBQ.le (by simpa only [norm_sub_rev] using hgap) hApoint hsigma
  have hsigmaA : ‖Lib.sigmaOf S m - a‖ ≤ L * ‖a - b‖ := by
    rw [hsigma_m]
    simpa only [a, b, mi, L, norm_sub_rev (lamMinus ψ m) (lamPlus ψ m)] using hplace.1
  have hsigmaB : ‖Lib.sigmaOf S m - b‖ ≤ L * ‖a - b‖ := by
    rw [hsigma_m]
    simpa only [a, b, mi, L, norm_sub_rev (lamMinus ψ m) (lamPlus ψ m)] using hplace.2
  have hzetaBoundSeg : ∀ z ∈ segment ℝ a (muSeq ψ m),
      ‖angleRegularFactor38 n m ((ψ, S), z)‖ ≤ Br * Lib.c3w n m := fun z hz =>
    hzetaBound z (hconv.segment_subset ha hmu hz)
  rw [hoff]
  by_cases hnear : ‖muSeq ψ m - a‖ ≤ ‖muSeq ψ m - b‖
  · have hq := Lib.quadraticODE_terminal_magnitude_le38
      (ball (Cb m) (Rb m)) isOpen_ball hconv
      a b (muSeq ψ m) (Lib.sigmaOf S m)
      ha hmu T (fun z => angleRegularFactor38 n m ((ψ, S), z))
      hT hzeta hode L (Br * Lib.c3w n m) hL0 hZ
      hsigmaB hzetaBoundSeg hnear
    have htermActual :
        Real.sqrt (‖(muSeq ψ m - a) * (muSeq ψ m - b)‖) * ‖T (muSeq ψ m)‖ =
          ‖gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
            sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
            sourceFamily.F_period n m hmn pW‖ :=
      hterminal.symm.trans (congrArg norm hbeta)
    rw [htermActual] at hq
    have hmin : min ‖muSeq ψ m - lamMinus ψ m‖ ‖muSeq ψ m - lamPlus ψ m‖ =
        ‖muSeq ψ m - a‖ := by
      simpa only [a, b] using min_eq_left hnear
    rw [hmin]
    have hgapnorm : ‖a - b‖ = ‖b - a‖ := norm_sub_rev _ _
    rw [hgapnorm] at hq
    refine hq.trans (le_of_eq ?_)
    dsimp only [C0, a, b]
    ring
  · have hnear' : ‖muSeq ψ m - b‖ ≤ ‖muSeq ψ m - a‖ := (not_le.mp hnear).le
    have hode' : ∀ z ∈ ball (Cb m) (Rb m),
        (z - b) * (z - a) * deriv T z + (z - (b + a) / 2) * T z =
          (Lib.sigmaOf S m - z) * angleRegularFactor38 n m ((ψ, S), z) := by
      intro z hz
      have hh := hode z hz
      simpa only [add_comm a b, mul_comm (z - b) (z - a)] using hh
    have hzetaBound' : ∀ z ∈ segment ℝ b (muSeq ψ m),
        ‖angleRegularFactor38 n m ((ψ, S), z)‖ ≤ Br * Lib.c3w n m := fun z hz =>
      hzetaBound z (hconv.segment_subset hb hmu hz)
    have hq := Lib.quadraticODE_terminal_magnitude_le38
      (ball (Cb m) (Rb m)) isOpen_ball hconv
      b a (muSeq ψ m) (Lib.sigmaOf S m)
      hb hmu T (fun z => angleRegularFactor38 n m ((ψ, S), z))
      hT hzeta hode' L (Br * Lib.c3w n m) hL0 hZ
      (by simpa only [norm_sub_rev b a] using hsigmaA) hzetaBound' hnear'
    have htermActual :
        Real.sqrt (‖(muSeq ψ m - a) * (muSeq ψ m - b)‖) * ‖T (muSeq ψ m)‖ =
          ‖gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
            sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
            sourceFamily.F_period n m hmn pW‖ :=
      hterminal.symm.trans (congrArg norm hbeta)
    have htermSwap :
        Real.sqrt (‖(muSeq ψ m - b) * (muSeq ψ m - a)‖) * ‖T (muSeq ψ m)‖ =
          ‖gkSourceBeta38 sourceW sourceFamily.W_open sourceFamily.W_real
            sourceFamily.W_gk sourceF sourceFamily.F_analytic sourceFamily.F_zero
            sourceFamily.F_period n m hmn pW‖ := by
      rw [mul_comm (muSeq ψ m - b) (muSeq ψ m - a)]
      exact htermActual
    rw [htermSwap] at hq
    have hmin : min ‖muSeq ψ m - lamMinus ψ m‖ ‖muSeq ψ m - lamPlus ψ m‖ =
        ‖muSeq ψ m - b‖ := by
      simpa only [a, b] using min_eq_right hnear'
    rw [hmin]
    refine hq.trans (le_of_eq ?_)
    dsimp only [C0, a, b]
    ring

end G4037Aux
end
end NlsGge.GKDefinitionDesign
