import Mathlib
import NlsGge.Atomic.G1.G1067
import NlsGge.Atomic.G1.G1091
import NlsGge.Atomic.G1.G1089
import NlsGge.Atomic.G1.G1076
import NlsGge.GK38.GradFundamentalStar
import NlsGge.GK38.PoissonMixedNormingMutual
import NlsGge.GK38.PoissonMixedRealNormingData
import NlsGge.GK38.PoissonMixedTargets
import NlsGge.GK38.DirichletRealReality
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PairAnalyticDet
import NlsGge.GK38.PairPotential
import NlsGge.ThirdConsultation.G1.G1098Host

                                                                                                         
                                                                                           
                                                                                                                  
                                                                                                            
                                                                                                                   
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38
open scoped BigOperators Matrix

namespace NlsGge.GKDefinitionDesign
noncomputable section


theorem G1096_solution_eq_state (φ : PotPair) (z : ℂ) (a : PairVec38) (s : ℝ) :
    solution φ z a s = pairKernelExt38 (state φ z a) s := by
  funext i
  rw [state_ext]
  simp only [solution, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have : ext38 (fundContP φ z) s = Set.IccExtend zero_le_one (fundPair φ z) s := rfl
  rw [this]
  ring

theorem G1096_isPairSolution (φ : PotPair) (z : ℂ) (a : PairVec38) :
    IsPairSolution38 φ z (fun s => solution φ z a s) := by
  have h : (fun s => solution φ z a s) = pairKernelExt38 (state φ z a) := by
    funext s
    exact G1096_solution_eq_state φ z a s
  rw [h]
  exact state_isPairSolution38 φ z a

theorem G1096_solution_zero (φ : PotPair) (z : ℂ) (a : PairVec38) :
    solution φ z a 0 = a := by
  have hx : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : fundPair φ z ⟨0, hx⟩ = 1 := fundPair_zero φ z
  unfold solution
  rw [Set.IccExtend_of_mem _ _ hx, h1, Matrix.one_mulVec]

theorem G1096_solution_one (φ : PotPair) (z : ℂ) (a : PairVec38) :
    solution φ z a 1 = monodromyPair φ z *ᵥ a := by
  have hx : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h1 : fundPair φ z ⟨1, hx⟩ = monodromyPair φ z := (monodromyPair_eq_fundPair φ z).symm
  unfold solution
  rw [Set.IccExtend_of_mem _ _ hx, h1]

theorem G1096_dir_one (φ : PotPair) (z : ℂ) (hd : dirichletChar φ z = 0) :
    monodromyPair φ z *ᵥ ![1, 1] = ![normingFactor φ z, normingFactor φ z] := by
  have h2 : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have hX : monodromyPair φ z 1 0 + monodromyPair φ z 1 1 =
      monodromyPair φ z 0 0 + monodromyPair φ z 0 1 := by
    unfold dirichletChar at hd
    rcases div_eq_zero_iff.1 hd with h | h
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, mul_one] at h
      linear_combination h
    · exact absurd h h2
  have e0 : (monodromyPair φ z *ᵥ ![1, 1]) 0 = normingFactor φ z := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, mul_one, normingFactor]
    linear_combination (-1 / 2 : ℂ) * hX
  have e1 : (monodromyPair φ z *ᵥ ![1, 1]) 1 = normingFactor φ z := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, mul_one, normingFactor]
    linear_combination (1 / 2 : ℂ) * hX
  funext i
  fin_cases i
  · exact e0
  · exact e1

theorem G1096_term_one (φ : PotPair) (z : ℂ) :
    monodromyPair φ z *ᵥ terminalSeed φ z = ![1, -1] := by
  have hdet : monodromyPair φ z 0 0 * monodromyPair φ z 1 1 -
      monodromyPair φ z 0 1 * monodromyPair φ z 1 0 = 1 := by
    have h := det_monodromyPair φ z
    rw [Matrix.det_fin_two] at h
    exact h
  have e0 : (monodromyPair φ z *ᵥ terminalSeed φ z) 0 = 1 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, terminalSeed, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    linear_combination hdet
  have e1 : (monodromyPair φ z *ᵥ terminalSeed φ z) 1 = -1 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, terminalSeed, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    linear_combination (-1 : ℂ) * hdet
  funext i
  fin_cases i
  · exact e0
  · exact e1

theorem G1096_wedge_one (φ ψ : PotPair) (z : ℂ) (hd : dirichletChar φ z = 0) :
    wedge (solution φ z ![1, 1] 1) (solution ψ z (terminalSeed ψ z) 1) =
      -2 * normingFactor φ z := by
  rw [G1096_solution_one, G1096_solution_one, G1096_dir_one φ z hd, G1096_term_one ψ z]
  show normingFactor φ z * (-1) - normingFactor φ z * 1 = -2 * normingFactor φ z
  ring

theorem G1096_wedge_zero (φ ψ : PotPair) (z : ℂ) :
    wedge (solution φ z ![1, 1] 0) (solution ψ z (terminalSeed ψ z) 0) =
      -2 * normingFactor ψ z := by
  rw [G1096_solution_zero, G1096_solution_zero]
  show (1 : ℂ) * (-(monodromyPair ψ z 0 0 + monodromyPair ψ z 1 0)) -
      1 * (monodromyPair ψ z 0 1 + monodromyPair ψ z 1 1) = -2 * normingFactor ψ z
  unfold normingFactor
  ring

theorem G1096_false_endpoint (φ ψ : PotPair) (z : ℂ) (hφ : dirichletChar φ z = 0)
    (hψ : dirichletChar ψ z = 0) :
    wedge (solution φ z ![1, 1] 1) (solution ψ z ![1, 1] 1) -
      wedge (solution φ z ![1, 1] 0) (solution ψ z ![1, 1] 0) = 0 := by
  rw [G1096_solution_one, G1096_solution_one, G1096_solution_zero, G1096_solution_zero,
    G1096_dir_one φ z hφ, G1096_dir_one ψ z hψ]
  simp [wedge]

theorem G1096_split (A B D : PairVec38) :
    bilinearPair (Complex.I • (A + B)) D =
      Complex.I * bilinearPair A D + Complex.I * bilinearPair B D := by
  simp only [bilinearPair, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem G1096_pot_real_ae (u v : PhysicalL2) : ∀ᵐ s : ℝ,
    potRepFst38 (realSlice (u - v)) s = potRepFst38 (realSlice u) s - potRepFst38 (realSlice v) s ∧
    potRepSnd38 (realSlice (u - v)) s = potRepSnd38 (realSlice u) s - potRepSnd38 (realSlice v) s := by
  have e : realSlice (u - v) = realSlice u - realSlice v := map_sub realSlice u v
  rw [e]
  have h1 := coverRep38_sub_ae (realSlice u).1 (realSlice v).1
  have h2 := coverRep38_sub_ae (realSlice u).2 (realSlice v).2
  filter_upwards [h1, h2] with s hs1 hs2
  exact ⟨hs1, hs2⟩

theorem G1096_pairIntegral_eq (K : PairKernelCont38) (u v : PhysicalL2) :
    integralPairCLM38 K t1 (realSlice (u - v)) =
      ∫ s in (0 : ℝ)..1, (pairKernelExt38 K s 0 * potRepFst38 (realSlice (u - v)) s +
        pairKernelExt38 K s 1 * potRepSnd38 (realSlice (u - v)) s) :=
  rfl

theorem G1096_bridge (K : PairKernelCont38) (X : ℝ → PairVec38)
    (hK : ∀ s : ℝ, pairKernelExt38 K s = X s) (u v : PhysicalL2) :
    (∫ s in (0 : ℝ)..1, (pairKernelExt38 K s 0 * potRepFst38 (realSlice (u - v)) s +
        pairKernelExt38 K s 1 * potRepSnd38 (realSlice (u - v)) s)) =
      ∫ s in (0 : ℝ)..1, bilinearPair (X s)
        ![potRepFst38 (realSlice u) s - potRepFst38 (realSlice v) s,
          potRepSnd38 (realSlice u) s - potRepSnd38 (realSlice v) s] := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [G1096_pot_real_ae u v] with s hs _
  simp only [hK s, hs.1, hs.2, bilinearPair, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem G1096_core (φ ψ : PotPair) (μ : ℂ) (a b : PairVec38) :
    IntervalIntegrable (fun s : ℝ => Complex.I * bilinearPair
        (starProd38 (solution φ μ a s) (solution ψ μ b s))
        ![potRepFst38 φ s - potRepFst38 ψ s, potRepSnd38 φ s - potRepSnd38 ψ s]) volume 0 1 ∧
    (∫ s in (0 : ℝ)..1, Complex.I * bilinearPair
        (starProd38 (solution φ μ a s) (solution ψ μ b s))
        ![potRepFst38 φ s - potRepFst38 ψ s, potRepSnd38 φ s - potRepSnd38 ψ s]) =
      wedge (solution φ μ a 1) (solution ψ μ b 1) - wedge (solution φ μ a 0) (solution ψ μ b 0) := by
  have hG := G1_067 φ ψ μ μ a b
  have hfun : twoPotentialWronskianRhs φ ψ μ μ a b = fun s : ℝ => Complex.I * bilinearPair
      (starProd38 (solution φ μ a s) (solution ψ μ b s))
      ![potRepFst38 φ s - potRepFst38 ψ s, potRepSnd38 φ s - potRepSnd38 ψ s] := by
    funext s
    simp [twoPotentialWronskianRhs]
  have hint : IntervalIntegrable (fun s : ℝ => Complex.I * bilinearPair
      (starProd38 (solution φ μ a s) (solution ψ μ b s))
      ![potRepFst38 φ s - potRepFst38 ψ s, potRepSnd38 φ s - potRepSnd38 ψ s]) volume 0 1 := by
    rw [← hfun]
    exact hG.1
  refine ⟨hint, ?_⟩
  have hac : AbsolutelyContinuousOnInterval
      (fun s : ℝ => wedge (solution φ μ a s) (solution ψ μ b s)) 0 1 :=
    ac_pairBracket38 (G1096_isPairSolution φ μ a).1 (G1096_isPairSolution ψ μ b).1
  have hcount : ({0, 1} : Set ℝ).Countable := (Set.toFinite ({0, 1} : Set ℝ)).countable
  have hae : ∀ᵐ s : ℝ, s ∉ ({0, 1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (Set.Countable.measure_zero hcount volume)
  have hd : ∀ᵐ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => wedge (solution φ μ a s) (solution ψ μ b s))
        (Complex.I * bilinearPair (starProd38 (solution φ μ a x) (solution ψ μ b x))
          ![potRepFst38 φ x - potRepFst38 ψ x, potRepSnd38 φ x - potRepSnd38 ψ x]) x := by
    have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hG.2
    filter_upwards [h1, hae] with x hx hx0 hIcc
    have hIoo : x ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hIcc.1 (fun h => hx0 (by rw [← h]; simp)),
        lt_of_le_of_ne hIcc.2 (fun h => hx0 (by rw [h]; simp))⟩
    have hx' := hx hIoo
    rw [congrFun hfun x] at hx'
    exact hx'
  exact ac_integral_eq_sub38 hac hint hd t1

theorem G1096_dir_gkMu (u : PhysicalL2) (n : ℤ) :
    dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 := by
  rw [← muSeq_eq_gkMu38 u n]
  exact muSeq_root38 (realSlice u) n

theorem G1096_norming_eq (u v : PhysicalL2) (h : normingDirichletMap u = normingDirichletMap v)
    (n : ℤ) :
    gkMu v n = gkMu u n ∧
      normingFactor (realSlice v) (gkMu u n : ℂ) = normingFactor (realSlice u) (gkMu u n : ℂ) := by
  obtain ⟨Kap, Mu, hK, hM, _⟩ := NlsGge.Atomic.G1089.G1089_main
  rw [G1091S1.normingDirichletMap_eq Kap Mu hK hM u,
    G1091S1.normingDirichletMap_eq Kap Mu hK hM v] at h
  have hc : ((Kap u : ℤ → ℝ) n : ℂ) + Complex.I * ((Mu u : ℤ → ℝ) n : ℂ) =
      ((Kap v : ℤ → ℝ) n : ℂ) + Complex.I * ((Mu v : ℤ → ℝ) n : ℂ) := by
    have := congrArg (fun x : Lib.L2Z => (x : ℤ → ℂ) n) h
    simpa only [G1091S1.iotaL2_apply] using this
  have hre : (Kap u : ℤ → ℝ) n = (Kap v : ℤ → ℝ) n := by
    have := congrArg Complex.re hc
    simpa using this
  have him : (Mu u : ℤ → ℝ) n = (Mu v : ℤ → ℝ) n := by
    have := congrArg Complex.im hc
    simpa using this
  have hk : realKappa38 u n = realKappa38 v n := by
    rw [← hK u n, ← hK v n]
    exact hre
  have hμ : gkMu v n = gkMu u n := by
    have h1 := hM u n
    have h2 := hM v n
    rw [him] at h1
    linarith
  have hsig : signedNorming38 u n = signedNorming38 v n := by
    have hlog : Real.log (signedNorming38 u n) = Real.log (signedNorming38 v n) := by
      unfold realKappa38 at hk
      linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.2 (signedNorming_positive38 u n))
      (Set.mem_Ioi.2 (signedNorming_positive38 v n)) hlog
  have hp : (-1 : ℂ) ^ n ≠ 0 := zpow_ne_zero n (by norm_num : (-1 : ℂ) ≠ 0)
  have eu : (-1 : ℂ) ^ n * normingFactor (realSlice u) (gkMu u n : ℂ) =
      ((signedNorming38 u n : ℝ) : ℂ) :=
    Complex.ext (by rw [(NlsGge.Atomic.G1076S1.sign_re_im u n).2, Complex.ofReal_re])
      (by rw [(NlsGge.Atomic.G1076S1.sign_re_im u n).1, Complex.ofReal_im])
  have ev : (-1 : ℂ) ^ n * normingFactor (realSlice v) (gkMu v n : ℂ) =
      ((signedNorming38 v n : ℝ) : ℂ) :=
    Complex.ext (by rw [(NlsGge.Atomic.G1076S1.sign_re_im v n).2, Complex.ofReal_re])
      (by rw [(NlsGge.Atomic.G1076S1.sign_re_im v n).1, Complex.ofReal_im])
  rw [hμ] at ev
  refine ⟨hμ, ?_⟩
  apply mul_left_cancel₀ hp
  rw [ev, eu, hsig]

theorem G1_096 (u v : PhysicalL2)
    (h : normingDirichletMap u = normingDirichletMap v) :
    ∀ n : ℤ, ∀ minus : Bool,
      integralPairCLM38 (mixedKernel u v n minus) t1 (realSlice (u-v)) = 0
 := by
  intro n minus
  obtain ⟨hμ, hnf⟩ := G1096_norming_eq u v h n
  have hdu : dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 := G1096_dir_gkMu u n
  have hdv : dirichletChar (realSlice v) (gkMu u n : ℂ) = 0 := by
    have h' := G1096_dir_gkMu v n
    rw [hμ] at h'
    exact h'
  have hdirU : ∀ s : ℝ, pairKernelExt38 (dirState u n) s =
      solution (realSlice u) (gkMu u n : ℂ) ![1, 1] s := fun s =>
    (G1096_solution_eq_state (realSlice u) (gkMu u n : ℂ) ![1, 1] s).symm
  have hdirV : ∀ s : ℝ, pairKernelExt38 (dirState v n) s =
      solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s := by
    intro s
    rw [show dirState v n = state (realSlice v) (gkMu v n : ℂ) ![1, 1] from rfl, hμ]
    exact (G1096_solution_eq_state (realSlice v) (gkMu u n : ℂ) ![1, 1] s).symm
  have htermU : ∀ s : ℝ, pairKernelExt38 (terminalState u n) s =
      solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s :=
    fun s => (G1096_solution_eq_state (realSlice u) (gkMu u n : ℂ)
      (terminalSeed (realSlice u) (gkMu u n : ℂ)) s).symm
  have htermV : ∀ s : ℝ, pairKernelExt38 (terminalState v n) s =
      solution (realSlice v) (gkMu u n : ℂ) (terminalSeed (realSlice v) (gkMu u n : ℂ)) s := by
    intro s
    rw [show terminalState v n = state (realSlice v) (gkMu v n : ℂ)
      (terminalSeed (realSlice v) (gkMu v n : ℂ)) from rfl, hμ]
    exact (G1096_solution_eq_state (realSlice v) (gkMu u n : ℂ)
      (terminalSeed (realSlice v) (gkMu u n : ℂ)) s).symm
  cases minus
  · have hK : ∀ s : ℝ, pairKernelExt38 (mixedKernel u v n false) s =
        starProd38 (solution (realSlice u) (gkMu u n : ℂ) ![1, 1] s)
          (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s) := by
      intro s
      show starProd38 (pairKernelExt38 (dirState u n) s) (pairKernelExt38 (dirState v n) s) = _
      rw [hdirU s, hdirV s]
    rw [G1096_pairIntegral_eq, G1096_bridge _ _ hK u v]
    have hC := (G1096_core (realSlice u) (realSlice v) (gkMu u n : ℂ) ![1, 1] ![1, 1]).2
    have hz : (∫ s in (0 : ℝ)..1, Complex.I * bilinearPair
        (starProd38 (solution (realSlice u) (gkMu u n : ℂ) ![1, 1] s)
          (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s))
        ![potRepFst38 (realSlice u) s - potRepFst38 (realSlice v) s,
          potRepSnd38 (realSlice u) s - potRepSnd38 (realSlice v) s]) = 0 := by
      rw [hC]
      exact G1096_false_endpoint (realSlice u) (realSlice v) (gkMu u n : ℂ) hdu hdv
    rw [intervalIntegral.integral_const_mul] at hz
    exact (mul_eq_zero.1 hz).resolve_left Complex.I_ne_zero
  · have hK : ∀ s : ℝ, pairKernelExt38 (mixedKernel u v n true) s =
        Complex.I • (starProd38 (solution (realSlice u) (gkMu u n : ℂ) ![1, 1] s)
            (solution (realSlice v) (gkMu u n : ℂ) (terminalSeed (realSlice v) (gkMu u n : ℂ)) s) +
          starProd38 (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
            (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s)) := by
      intro s
      show Complex.I • (starProd38 (pairKernelExt38 (dirState u n) s)
          (pairKernelExt38 (terminalState v n) s) +
        starProd38 (pairKernelExt38 (dirState v n) s) (pairKernelExt38 (terminalState u n) s)) = _
      rw [hdirU s, hdirV s, htermV s, htermU s]
    rw [G1096_pairIntegral_eq, G1096_bridge _ _ hK u v]
    simp only [G1096_split]
    have hX := (G1096_core (realSlice u) (realSlice v) (gkMu u n : ℂ) ![1, 1]
      (terminalSeed (realSlice v) (gkMu u n : ℂ))).1
    have hC1 := (G1096_core (realSlice u) (realSlice v) (gkMu u n : ℂ) ![1, 1]
      (terminalSeed (realSlice v) (gkMu u n : ℂ))).2
    have hC2 := G1096_core (realSlice v) (realSlice u) (gkMu u n : ℂ) ![1, 1]
      (terminalSeed (realSlice u) (gkMu u n : ℂ))
    have hpt : ∀ s : ℝ, Complex.I * bilinearPair
        (starProd38 (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
          (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s))
        ![potRepFst38 (realSlice u) s - potRepFst38 (realSlice v) s,
          potRepSnd38 (realSlice u) s - potRepSnd38 (realSlice v) s] =
        -(Complex.I * bilinearPair
          (starProd38 (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
            (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s))
          ![potRepFst38 (realSlice v) s - potRepFst38 (realSlice u) s,
            potRepSnd38 (realSlice v) s - potRepSnd38 (realSlice u) s]) := by
      intro s
      simp only [bilinearPair, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    have hY : IntervalIntegrable (fun s : ℝ => Complex.I * bilinearPair
        (starProd38 (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
          (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s))
        ![potRepFst38 (realSlice u) s - potRepFst38 (realSlice v) s,
          potRepSnd38 (realSlice u) s - potRepSnd38 (realSlice v) s]) volume 0 1 :=
      hC2.1.neg.congr_ae (Filter.Eventually.of_forall fun s => (hpt s).symm)
    have hYint : (∫ s in (0 : ℝ)..1, Complex.I * bilinearPair
        (starProd38 (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
          (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s))
        ![potRepFst38 (realSlice u) s - potRepFst38 (realSlice v) s,
          potRepSnd38 (realSlice u) s - potRepSnd38 (realSlice v) s]) =
        -(∫ s in (0 : ℝ)..1, Complex.I * bilinearPair
          (starProd38 (solution (realSlice v) (gkMu u n : ℂ) ![1, 1] s)
            (solution (realSlice u) (gkMu u n : ℂ) (terminalSeed (realSlice u) (gkMu u n : ℂ)) s))
          ![potRepFst38 (realSlice v) s - potRepFst38 (realSlice u) s,
            potRepSnd38 (realSlice v) s - potRepSnd38 (realSlice u) s]) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      exact hpt s
    rw [intervalIntegral.integral_add hX hY, hC1, hYint, hC2.2,
      G1096_wedge_one (realSlice u) (realSlice v) (gkMu u n : ℂ) hdu,
      G1096_wedge_zero (realSlice u) (realSlice v) (gkMu u n : ℂ),
      G1096_wedge_one (realSlice v) (realSlice u) (gkMu u n : ℂ) hdv,
      G1096_wedge_zero (realSlice v) (realSlice u) (gkMu u n : ℂ), hnf]
    ring

end
end NlsGge.GKDefinitionDesign
