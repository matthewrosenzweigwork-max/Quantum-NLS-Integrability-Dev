import Mathlib
import NlsGge.Atomic.G2.G2048
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.ThirdConsultation.G2.G2073Host

                                                                                                          
                                                                         
                                                                                                                
                                                                                                                      
                                                                                                                 
                                                                                                          
                                                                                              
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Shifted sequence: coordinate n is moved so that sigma_n equals a (a z-independent shift). -/
def g2073s1ShiftSeq (s : Lib.L2Seq) (n : ℤ) (a : ℂ) : Lib.L2Seq :=
  s + (a - Lib.sigmaOf s n) • lp.single 2 n (1 : ℂ)

theorem g2073s1_sigma_n (s : Lib.L2Seq) (n : ℤ) (a : ℂ) :
    Lib.sigmaOf (g2073s1ShiftSeq s n a) n = a := by
  unfold g2073s1ShiftSeq
  rw [G2048Aux.sigma_shift_eq]
  ring

theorem g2073s1_sigma_ne (s : Lib.L2Seq) (n : ℤ) (a : ℂ) (k : ℤ) (hk : k ≠ n) :
    Lib.sigmaOf (g2073s1ShiftSeq s n a) k = Lib.sigmaOf s k := by
  unfold g2073s1ShiftSeq
  exact G2048Aux.sigma_shift_ne s n _ k hk

/-- Tube geometry: a point at distance < R m + c^{-1}/2 from the centre of disc m is outside every other gap segment. -/
theorem g2073s1_tube_avoids (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N)
    (φ : PotPair) (hspec : IsolatingSpectral38 φ C R) (m k : ℤ) (hkm : k ≠ m) (z : ℂ)
    (hz : dist z (C m) < R m + c⁻¹ / 2) : z ∉ segment ℝ (lamMinus φ k) (lamPlus φ k) := by
  intro hseg
  have hk' : dist z (C k) < R k := mem_ball.1 ((hspec.1 k).1 hseg)
  have hc1 : (1 : ℝ) ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hpos : 0 < c⁻¹ := inv_pos.2 hc0
  have hRm : 0 < R m := (hg.1 m).1
  have hRk : 0 < R k := (hg.1 k).1
  have hbd := (hg.2.2.2.1 m k (Ne.symm hkm)).1
  have h1 : (1 : ℝ) ≤ |((m - k : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hkm))
  rw [ballDistance38_eq (C m) (C k) hRm hRk] at hbd
  have hlow : c⁻¹ ≤ c⁻¹ * |((m - k : ℤ) : ℝ)| := le_mul_of_one_le_right hpos.le h1
  have hX : c⁻¹ * |((m - k : ℤ) : ℝ)| ≤ dist (C m) (C k) - R m - R k := by
    rcases le_total 0 (dist (C m) (C k) - R m - R k) with h | h
    · rwa [max_eq_right h] at hbd
    · rw [max_eq_left h] at hbd
      linarith
  have htri := dist_triangle (C m) z (C k)
  have hz' : dist (C m) z < R m + c⁻¹ / 2 := by rwa [dist_comm] at hz
  linarith

/-- L3 (closed-disc separation). -/
theorem closedBall_avoids_other_gaps (φ : PotPair) (hφ : φ ∈ gkW) (m k : ℤ) (hkm : k ≠ m)
    (z : ℂ) (hz : z ∈ Metric.closedBall (discC φ m) (discR φ m)) :
    z ∉ segment ℝ (lamMinus φ k) (lamPlus φ k) := by
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hφ
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hpos : 0 < c⁻¹ / 2 := by have := inv_pos.2 hc0; linarith
  refine g2073s1_tube_avoids (discC φ) (discR φ) c N hg φ hspec m k hkm z ?_
  have h2 := mem_closedBall.1 hz
  linarith

/-- L3 (sphere part): the sphere of disc m misses its own gap segment, hence both endpoints. -/
theorem sphere_avoids_own_gap (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (z : ℂ)
    (hz : z ∈ Metric.sphere (discC φ m) (discR φ m)) :
    z ∉ segment ℝ (lamMinus φ m) (lamPlus φ m) := by
  obtain ⟨_c, _N, _hg, hspec⟩ := isolating_family38 φ hφ
  intro hseg
  have h1 := mem_ball.1 ((hspec.1 m).1 hseg)
  have h2 := mem_sphere.1 hz
  linarith

theorem sphere_ne_lamMinus (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (z : ℂ)
    (hz : z ∈ Metric.sphere (discC φ m) (discR φ m)) : z ≠ lamMinus φ m := by
  intro h
  exact sphere_avoids_own_gap φ hφ m z hz (by rw [h]; exact left_mem_segment ℝ _ _)

theorem sphere_ne_lamPlus (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (z : ℂ)
    (hz : z ∈ Metric.sphere (discC φ m) (discR φ m)) : z ≠ lamPlus φ m := by
  intro h
  exact sphere_avoids_own_gap φ hφ m z hz (by rw [h]; exact right_mem_segment ℝ _ _)

/-- L4 (sphere in rootDomain38). -/
theorem sphere_mem_rootDomain (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (z : ℂ)
    (hz : z ∈ Metric.sphere (discC φ m) (discR φ m)) : (φ, z) ∈ rootDomain38 := by
  refine ⟨hφ, fun hz' => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz'
  by_cases hkm : k = m
  · rw [hkm] at hk
    exact sphere_avoids_own_gap φ hφ m z hz hk
  · exact closedBall_avoids_other_gaps φ hφ m k hkm z (Metric.sphere_subset_closedBall hz) hk

/-- L1: the normalized root is the sigma coordinate of the extended sequence. -/
theorem normalizedRoot_eq_sigmaOf (n m : ℤ) (φ : PotPair) (hmn : m ≠ n) :
    normalizedRoot n m φ = Lib.sigmaOf (p2Extend38 n (sourceF n φ)) m := by
  have h : p2Extend38 n (sourceF n φ) m = sourceF n φ (⟨m, hmn⟩ : P2Index38 n) :=
    p2Extend_at38 n _ ⟨m, hmn⟩
  rw [normalizedRoot, dif_pos hmn, Lib.sigmaOf, countingCenter38, h]

/-- L2: the zero-period term vanishes for m ≠ n. -/
theorem zero_period_circle (φ : PotPair) (hφ : φ ∈ sourceW) (n m : ℤ) (hmn : m ≠ n) :
    abelianPeriod38 m φ (p2Numerator38 n (sourceF n φ)) = 0 := by
  have hgk : φ ∈ gkW := G2071S1.structural.2.2.1 hφ
  have h0 : p2Fn38 n (φ, sourceF n φ) = 0 := G2071S1.structural.2.2.2.2 n φ hφ
  have h1 : p2FnCoord38 n (φ, sourceF n φ) (⟨m, hmn⟩ : P2Index38 n) = 0 := by
    rw [← p2Fn_apply38 n (φ, sourceF n φ) hgk (⟨m, hmn⟩ : P2Index38 n), h0]
    simp
  have h2 : ((n - m : ℤ) : ℂ) * abelianPeriod38 m φ (p2Numerator38 n (sourceF n φ)) = 0 := h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (Int.cast_eq_zero.1 h) (sub_ne_zero.mpr (Ne.symm hmn))
  · exact h

theorem g2073s1_std_ne (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) (z : ℂ)
    (hz : z ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) : standardRoot φ n z ≠ 0 := by
  have hs := stdRoot_ne_zero38 (lamMinus φ n) (lamPlus φ n) z hz
  simpa only [standardRoot, add_comm (lamMinus φ n), ← tauN_value38 φ hφ n,
    ← gamma2_value38 φ hφ n] using hs

/-- G2-048 limit argument with a z-independent shift: doubleRootRatio equals w_n/(a-z) times the omitted ratio. -/
theorem g2073s1_doubleRoot_shift (φ : PotPair) (n m : ℤ) (hmn : m ≠ n) (s : Lib.L2Seq) (a z : ℂ)
    (hz : (φ, z) ∈ a5OmittedRootDomain38 m) (hwn : standardRoot φ n z ≠ 0) (haz : a - z ≠ 0) :
    doubleRootRatio φ s n m z =
      standardRoot φ n z / (a - z) * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq s n a), z) := by
  have hnm : n ≠ m := fun h => hmn h.symm
  have hσn : Lib.sigmaOf (g2073s1ShiftSeq s n a) n = a := g2073s1_sigma_n s n a
  have hp0 : ((φ, g2073s1ShiftSeq s n a), z) ∈
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} := hz
  have hT := (G2_022 m).2.tendsto_at hp0
  have hrel : ∀ᶠ N : ℕ in atTop,
      (∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z) =
      standardRoot φ n z / (a - z) * ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if k=m then (1 : ℂ) else (Lib.sigmaOf (g2073s1ShiftSeq s n a) k-z)/standardRoot φ k z := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    have hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [← Finset.mul_prod_erase _ _ hn, ← Finset.mul_prod_erase _ _ hn]
    have e1 : (if n = n ∨ n = m then (1 : ℂ) else (Lib.sigmaOf s n-z)/standardRoot φ n z) = 1 := by
      simp
    have e2 : (if n = m then (1 : ℂ) else (Lib.sigmaOf (g2073s1ShiftSeq s n a) n-z)/standardRoot φ n z)
        = (a - z) / standardRoot φ n z := by
      rw [if_neg hnm, hσn]
    have e3 : ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
        (if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z) =
        ∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (if k=m then (1 : ℂ) else (Lib.sigmaOf (g2073s1ShiftSeq s n a) k-z)/standardRoot φ k z) := by
      refine Finset.prod_congr rfl (fun k hk => ?_)
      have hkn : k ≠ n := (Finset.mem_erase.1 hk).1
      by_cases hkm : k = m
      · simp [hkm]
      · rw [if_neg (by tauto), if_neg hkm, g2073s1_sigma_ne s n a k hkn]
    have key : standardRoot φ n z / (a - z) * ((a - z) / standardRoot φ n z) = 1 := by
      rw [div_mul_div_comm, mul_comm (standardRoot φ n z) (a - z), div_self (mul_ne_zero haz hwn)]
    rw [e1, e2, e3, one_mul, ← mul_assoc, key, one_mul]
  have hlim : Tendsto (fun N : ℕ => ∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z) atTop
      (𝓝 (standardRoot φ n z / (a - z) * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq s n a), z))) := by
    refine Tendsto.congr' (hrel.mono fun N h => h.symm) ?_
    exact hT.const_mul (standardRoot φ n z / (a - z))
  have hHP : HasProd (fun k : ℤ => if k=n ∨ k=m then (1 : ℂ) else (Lib.sigmaOf s k-z)/standardRoot φ k z)
      (standardRoot φ n z / (a - z) * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq s n a), z))
      (symmetricIcc ℤ) := hasProd_symmetricIcc_iff.2 hlim
  exact hHP.tprod_eq

/-- psiZeta with the z-independent shift: psiZeta = I * Ratio_m(s_a)(z) / (a - z). -/
theorem g2073s1_psi_shift (φ : PotPair) (n m : ℤ) (hmn : m ≠ n) (s : Lib.L2Seq) (a z : ℂ)
    (hz : (φ, z) ∈ a5OmittedRootDomain38 m) (hwn : standardRoot φ n z ≠ 0) (haz : a - z ≠ 0) :
    psiZeta φ s n m z = Complex.I * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq s n a), z) / (a - z) := by
  rw [psiZeta, g2073s1_doubleRoot_shift φ n m hmn s a z hz hwn haz]
  have hcal : Complex.I / standardRoot φ n z * (standardRoot φ n z / (a - z) *
      p2OmittedRatio38 m ((φ, g2073s1ShiftSeq s n a), z)) =
      Complex.I * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq s n a), z) / (a - z) *
        (standardRoot φ n z / standardRoot φ n z) := by ring
  rw [hcal, div_self hwn, mul_one]

/-- L6 (conjunct 1 of G2-073): normalizedChi is analytic on the closed disc of index m. -/
theorem normalizedChi_analytic_closedBall (φ : PotPair) (hφ : φ ∈ sourceW) (n m : ℤ) (hmn : m ≠ n) :
    AnalyticOnNhd ℂ (normalizedChi n m φ) (Metric.closedBall (discC φ m) (discR φ m)) := by
  have hgk : φ ∈ gkW := G2071S1.structural.2.2.1 hφ
  obtain ⟨c, N, hg, hspec⟩ := isolating_family38 φ hgk
  have hc1 : (1 : ℝ) ≤ c := hg.2.2.1
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc1
  have hpos : 0 < c⁻¹ / 2 := by have := inv_pos.2 hc0; linarith
  have hRm : 0 < discR φ m := (hg.1 m).1
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = discC φ m + ((discR φ m + c⁻¹ / 2 + 1 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hac : a - discC φ m = ((discR φ m + c⁻¹ / 2 + 1 : ℝ) : ℂ) := by
    rw [ha]; ring
  have hdA : dist a (discC φ m) = discR φ m + c⁻¹ / 2 + 1 := by
    rw [dist_eq_norm, hac, Complex.norm_real,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ discR φ m + c⁻¹ / 2 + 1 by linarith)]
  have hmemU : ∀ z ∈ Metric.ball (discC φ m) (discR φ m + c⁻¹ / 2),
      (φ, z) ∈ a5OmittedRootDomain38 m := fun z hz =>
    ⟨hgk, fun k hk => g2073s1_tube_avoids (discC φ) (discR φ) c N hg φ hspec m k hk z (mem_ball.1 hz)⟩
  have hane : ∀ z ∈ Metric.ball (discC φ m) (discR φ m + c⁻¹ / 2), a - z ≠ 0 := by
    intro z hz heq
    have hza : z = a := (sub_eq_zero.1 heq).symm
    have hd := mem_ball.1 hz
    rw [hza] at hd
    linarith
  have hwn : ∀ z ∈ Metric.ball (discC φ m) (discR φ m + c⁻¹ / 2), standardRoot φ n z ≠ 0 := fun z hz =>
    g2073s1_std_ne φ hgk n z
      (g2073s1_tube_avoids (discC φ) (discR φ) c N hg φ hspec m n (Ne.symm hmn) z (mem_ball.1 hz))
  have hcongr : ∀ z ∈ Metric.ball (discC φ m) (discR φ m + c⁻¹ / 2),
      normalizedChi n m φ z = (Real.pi : ℂ) * ((n - m : ℤ) : ℂ) *
        (Complex.I * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ)) n a), z) /
          (a - z)) := by
    intro z hz
    rw [show normalizedChi n m φ z = (Real.pi : ℂ) * ((n - m : ℤ) : ℂ) *
        psiZeta φ (p2Extend38 n (sourceF n φ)) n m z from rfl,
      g2073s1_psi_shift φ n m hmn (p2Extend38 n (sourceF n φ)) a z (hmemU z hz) (hwn z hz) (hane z hz)]
  have hdiv : ∀ z ∈ Metric.ball (discC φ m) (discR φ m + c⁻¹ / 2),
      AnalyticAt ℂ (fun w : ℂ => (Real.pi : ℂ) * ((n - m : ℤ) : ℂ) *
        (Complex.I * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ)) n a), w) /
          (a - w))) z := by
    intro z hz
    have hL : AnalyticAt ℂ (fun w : ℂ => p2OmittedRatio38 m
        ((φ, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ)) n a), w)) z :=
      (p2OmittedRatio_analytic38 m ((φ, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ)) n a), z)
        (hmemU z hz)).comp ((analyticAt_const).prod analyticAt_id)
    have hg' : AnalyticAt ℂ (fun w : ℂ => a - w) z := analyticAt_const.sub analyticAt_id
    have hI : AnalyticAt ℂ (fun w : ℂ => Complex.I * p2OmittedRatio38 m
        ((φ, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ)) n a), w)) z := analyticAt_const.mul hL
    have hQ : AnalyticAt ℂ (fun w : ℂ => Complex.I * p2OmittedRatio38 m
        ((φ, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ)) n a), w) / (a - w)) z :=
      hI.div hg' (hane z hz)
    exact analyticAt_const.mul hQ
  intro z hz
  have hlt : discR φ m < discR φ m + c⁻¹ / 2 := by linarith
  have hzU : z ∈ Metric.ball (discC φ m) (discR φ m + c⁻¹ / 2) := closedBall_subset_ball hlt hz
  have hev : (fun w : ℂ => (Real.pi : ℂ) * ((n - m : ℤ) : ℂ) *
        (Complex.I * p2OmittedRatio38 m ((φ, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ)) n a), w) /
          (a - w))) =ᶠ[𝓝 z] normalizedChi n m φ :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hzU) (fun w hw => (hcongr w hw).symm)
  exact (hdiv z hzU).congr hev

end
end NlsGge.GKDefinitionDesign
