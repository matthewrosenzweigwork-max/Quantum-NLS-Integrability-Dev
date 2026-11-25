import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.G1.G1040
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.PairVolterra
import NlsGge.GK38.PairVolterraProbe
import NlsGge.Atomic.G2.G2005
import NlsGge.Atomic.G2.G2006
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.GK38.Lib.EntireProductsGrowth
import NlsGge.GK38.Lib.EntireProductsCircle
import NlsGge.GK38.ProductReprRatio
import NlsGge.GK38.PeriodicAsymptotics
import NlsGge.GK38.PeriodicLabellingFreeLabels
import NlsGge.Atomic.G1.G1050
import NlsGge.Atomic.G1.G1052

/- G1-053 production: the G1-050 private copy (G1050S2 namespace tree) and the G1-052 proof (G1052S3) of the reviewed candidate G1053_PROOF01 are replaced by `import NlsGge.Atomic.G1.G1050` and `import NlsGge.Atomic.G1.G1052`. -/


                                                                                
                                                                                                                                                                                                                                                                                           
                                                                                                                                                                           
                                                                                                                                                                             
                                                                                                                                                        
                                                                               

namespace NlsGge.Atomic.G1053S3

open Filter Topology SummationFilter Set Metric NlsGge.GK38 NlsGge.Atomic.Volterra NlsGge.SpectralFoundations NlsGge.Pilot
open NlsGge.Atomic.G1050S2 NlsGge.Atomic.G1052S3
open scoped Matrix.Norms.L2Operator

noncomputable section

theorem summG (φ : PotPair) :
    Summable (fun n : ℤ => ‖lamPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) ∧
    Summable (fun n : ℤ => ‖lamMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
  obtain ⟨U, hU, C, -, h⟩ := periodic_l2G φ
  have hs := (h φ (mem_of_mem_nhds hU)).1
  exact ⟨hs.of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ => le_add_of_nonneg_left (sq_nonneg _)),
    hs.of_nonneg_of_le (fun _ => sq_nonneg _) (fun _ => le_add_of_nonneg_right (sq_nonneg _))⟩

theorem pairedProduct_eq_mulG (φ : PotPair) (z : ℂ) :
    pairedProduct38 φ z = singleProduct38 (lamPlus φ) z * singleProduct38 (lamMinus φ) z := by
  have hp := (Lib.product_entire (lamPlus φ) (summG φ).1).1 z
  have hm := (Lib.product_entire (lamMinus φ) (summG φ).2).1 z
  simpa only [pairedProduct38, singleProduct38, pairedFactors_eq_mul38] using hp.tprod_mul hm

theorem multipliable_pairedG (φ : PotPair) (z : ℂ) :
    Multipliable (pairedFactors38 φ z) (symmetricIcc ℤ) := by
  have hp := (Lib.product_entire (lamPlus φ) (summG φ).1).1 z
  have hm := (Lib.product_entire (lamMinus φ) (summG φ).2).1 z
  have he : pairedFactors38 φ z = fun m =>
      ((lamPlus φ m - z) / (πn m : ℂ)) * ((lamMinus φ m - z) / (πn m : ℂ)) :=
    funext (pairedFactors_eq_mul38 φ z)
  rw [he]
  exact hp.mul hm

theorem differentiable_periodicProductG (φ : PotPair) : Differentiable ℂ (periodicProduct38 φ) := by
  have hp := (Lib.product_entire (lamPlus φ) (summG φ).1).2.1
  have hm := (Lib.product_entire (lamMinus φ) (summG φ).2).2.1
  have he : periodicProduct38 φ = fun z => (-4 : ℂ) * (singleProduct38 (lamPlus φ) z * singleProduct38 (lamMinus φ) z) :=
    funext fun z => congrArg (fun v : ℂ => (-4 : ℂ) * v) (pairedProduct_eq_mulG φ z)
  rw [he]
  exact (hp.mul hm).const_mul (-4)

theorem analyticOrderAt_periodicProductG (φ : PotPair) (w : ℂ) :
    analyticOrderAt (periodicProduct38 φ) w = analyticOrderAt (perChar φ) w := by
  have hp := Lib.product_entire (lamPlus φ) (summG φ).1
  have hm := Lib.product_entire (lamMinus φ) (summG φ).2
  have hc : analyticOrderAt (fun _ : ℂ => (-4 : ℂ)) w = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  have he : periodicProduct38 φ = (fun _ : ℂ => (-4 : ℂ)) *
      (singleProduct38 (lamPlus φ) * singleProduct38 (lamMinus φ)) :=
    funext (fun z => congrArg (fun v : ℂ => (-4 : ℂ) * v) (pairedProduct_eq_mulG φ z))
  have hap : AnalyticAt ℂ (singleProduct38 (lamPlus φ)) w := hp.2.1.analyticAt w
  have ham : AnalyticAt ℂ (singleProduct38 (lamMinus φ)) w := hm.2.1.analyticAt w
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (-4 : ℂ)) w := analyticAt_const
  rw [he, analyticOrderAt_mul hconst (hap.mul ham),
    hc, zero_add, analyticOrderAt_mul hap ham]
  change analyticOrderAt (singleProduct38 (lamPlus φ)) w +
    analyticOrderAt (singleProduct38 (lamMinus φ)) w = _
  unfold singleProduct38
  rw [hp.2.2 w, hm.2.2 w, add_comm]
  exact lamMinusPlus_occurrence38 φ w

theorem circle_growthG (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖pairedProduct38 φ z - Complex.sin z ^ 2‖ ≤ ε * ‖Complex.sin z‖ ^ 2 := by
  let η := min 1 (ε / 3)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 3 := min_le_right _ _
  have hcoeff : 2 * η + η ^ 2 ≤ ε := by nlinarith
  obtain ⟨Np, hp⟩ := product_growthG (lamPlus φ) (summG φ).1 η hη
  obtain ⟨Nm, hm⟩ := product_growthG (lamMinus φ) (summG φ).2 η hη
  refine ⟨max Np Nm, ?_⟩
  intro n hn z hz
  rw [pairedProduct_eq_mulG]
  exact (productRepr_pair_error38 _ _ _ η hη.le
    (hp n ((le_max_left _ _).trans hn) z hz)
    (hm n ((le_max_right _ _).trans hn) z hz)).trans
    (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))

theorem normalized_growthG (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖periodicProduct38 φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ε * ‖(-4 : ℂ) * Complex.sin z ^ 2‖ := by
  obtain ⟨N, hN⟩ := circle_growthG φ ε hε
  refine ⟨N, fun n hn z hz => ?_⟩
  have hp := hN n hn z hz
  have heP : periodicProduct38 φ z - (-4 * Complex.sin z ^ 2) =
      (-4 : ℂ) * (pairedProduct38 φ z - Complex.sin z ^ 2) := by
    unfold periodicProduct38; ring
  rw [heP, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, norm_pow]
  nlinarith

theorem actual_growthG (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖perChar φ z - (-4 * Complex.sin z ^ 2)‖ ≤ ε * ‖(-4 : ℂ) * Complex.sin z ^ 2‖ := by
  obtain ⟨Up, hUp, Rp, hp⟩ := perChar_asympG φ (4 * ε) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge (Rp / Real.pi)
  refine ⟨N + 1, fun n hn z hz => ?_⟩
  have hR : Rp < ‖z‖ := by
    have hNn : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hbase : Rp ≤ (N : ℝ) * Real.pi := (div_le_iff₀ Real.pi_pos).mp hN
    rw [hz]
    nlinarith [Real.pi_pos]
  have hsep := productRepr_circle_separation38 hz
  have h := hp φ (mem_of_mem_nhds hUp) z hR hsep
  simpa only [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow, mul_assoc, mul_comm,
    mul_left_comm] using h

theorem circle_ratioG (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      ‖perChar φ z / periodicProduct38 φ z - 1‖ < ε := by
  let δ := min (1 / 4) (ε / 8)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := (min_le_left _ _).trans (by norm_num)
  have hδε : 4 * δ < ε := by
    have h := min_le_right (1 / 4 : ℝ) (ε / 8)
    change δ ≤ ε / 8 at h
    linarith
  obtain ⟨Np, hp⟩ := normalized_growthG φ δ hδ
  obtain ⟨Na, ha⟩ := actual_growthG φ δ hδ
  refine ⟨max Np Na, fun n hn z hz => ?_⟩
  have hgp := hp n ((le_max_left _ _).trans hn) z hz
  have hfp := ha n ((le_max_right _ _).trans hn) z hz
  have hs := productRepr_circle_sin_ne_zero38 hz
  have htP : (-4 : ℂ) * Complex.sin z ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hs)
  obtain ⟨-, hrP⟩ := productRepr_relative_ratio38 _ _ _ δ hδ.le hδhalf htP hfp hgp
  exact hrP.trans_lt hδε

theorem perChar_eq_periodicProductG (φ : PotPair) : perChar φ = periodicProduct38 φ := by
  apply Lib.entire_eq_of_ratio_tendsto_one
    (fun w => (analyticOnNhd_perChar_z φ w (mem_univ w)).differentiableAt)
    (differentiable_periodicProductG φ)
  · intro w
    exact (analyticOrderAt_periodicProductG φ w).le
  · intro ε hε
    exact circle_ratioG φ ε hε

theorem G1053_main :
((
  ∀ (φ : PotPair) (lam : ℂ),
    Filter.Tendsto
      (fun K : ℕ =>
        -4 * ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          ((lamPlus φ m - lam) * (lamMinus φ m - lam)) /
            (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)) ^ 2)
      Filter.atTop
      (nhds ((Matrix.trace (monodromyPair φ lam)) ^ 2 - 4))
  : Prop)) := by
  intro φ lam
  have hP := (multipliable_pairedG φ lam).hasProd
  unfold HasProd at hP
  rw [symmetricIcc_eq_map_Icc_nat, tendsto_map'_iff] at hP
  have h2 := hP.const_mul (-4 : ℂ)
  have hlim : (-4 : ℂ) * pairedProduct38 φ lam = (Matrix.trace (monodromyPair φ lam)) ^ 2 - 4 := by
    have := congrFun (perChar_eq_periodicProductG φ) lam
    change discrim φ lam ^ 2 - 4 = periodicProduct38 φ lam at this
    exact this.symm
  have hfun : (fun K : ℕ => -4 * ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      ((lamPlus φ m - lam) * (lamMinus φ m - lam)) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)) ^ 2) =
      fun K : ℕ => (-4 : ℂ) * ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), pairedFactors38 φ lam m := by
    funext K
    congr 1
    refine Finset.prod_congr rfl fun m _ => ?_
    unfold pairedFactors38
    rw [piN_cast]
  rw [hfun, ← hlim]
  exact h2

end

end NlsGge.Atomic.G1053S3
