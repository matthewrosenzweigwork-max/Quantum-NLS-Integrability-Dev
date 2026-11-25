                                                                                                                                                                                                                                                                                                    
import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.G1.G1008
import NlsGge.Atomic.G1.G1015
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.GK38.DirichletCounting
import NlsGge.GK38.Lib.EntireProducts
import NlsGge.GK38.ProductReprConstruction
import NlsGge.Atomic.G2.G2005
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.GK38.Lib.EntireProductsGrowth
import NlsGge.GK38.Lib.EntireProductsCircle
import NlsGge.Atomic.G2.G2006
import NlsGge.Atomic.G1.G1043
import NlsGge.Atomic.G1.G1050

                                                                                                                    
                                                                                                                                 
                                                                                                                          
                                                                                                                                 
                                                                                                                             
                                                                                                                                       
                                                                                                          

set_option autoImplicit false

                                                                             
section
                                                                                                                           
                                                                                                                            
                                                                                                                                   
                                                                                                                     
                                                                                                                            
                                                                                                                              
                                                                                                             

                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator




/-! ### G1-017: high-frequency local uniform asymptotics -/

open NlsGge.Atomic.G1043S1.K42.K17.K16


open NlsGge.Pilot


/-! ### The final statement -/


                                                                                
                                                                           
                                                                                                                  
                                                                                                                       
                                                  
                                                                                                                    
                                                                                                                      
                                                                                                                    
                                                                                                                               
                                                                                                      
                                                                               


end

                                                                             
section
                                                                                                                   
                                                                                                                       
                                                                                                                                    
                                                                                                                          
                                                                                                            
                                                                                                   

set_option autoImplicit false

                                                                             
section
                                                                                                         
                                                                                     
                                                                                              
                                                                                             
                                                                                                         

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT
open scoped Matrix.Norms.L2Operator


end

open MeasureTheory Filter Topology Set
open NlsGge.GK38
/-! ### The first Volterra term -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
open scoped Matrix.Norms.L2Operator





end


                                                                                
                                                                                                                    
                                                                                                                      
                                                                               

section
set_option autoImplicit false

open Filter Topology Finset NlsGge.GK38.Lib NlsGge.Atomic.G2

end

                                                                                
                                                                                            
                                                                                                                           
                                                                                                                          
                                                                                                                      
                                                                                          
                                                                                                                    
                                                                                                                          
                                                                                                                                 
                                                
                                                                                                        
                                                                        
                                                                                                                       
                                           
                                                                               

namespace NlsGge.Atomic.G1044S3M

open Filter Topology SummationFilter Set Metric NlsGge.GK38

noncomputable section

theorem exists_cutoff (φ : PotPair) : ∃ N : ℕ, RootCountingAt38 (dirichletChar φ) 1 N := by
  obtain ⟨U, hU, N, hN⟩ := NlsGge.Atomic.G1043S1.K42.dirichlet_counting_s3 φ
  exact ⟨N, hN φ (mem_of_mem_nhds hU)⟩

/-- The cutoff, chosen from the G1-017-based counting. -/
def Ncut (φ : PotPair) : ℕ := Classical.choose (exists_cutoff φ)

theorem Ncut_spec (φ : PotPair) : RootCountingAt38 (dirichletChar φ) 1 (Ncut φ) :=
  Classical.choose_spec (exists_cutoff φ)

/-- The Dirichlet labels (the production canonical candidate at the G1-017-based cutoff). -/
def mu (φ : PotPair) : ℤ → ℂ := criticalCandidate38 (dirichletChar φ) (Ncut φ)

theorem mu_enum (φ : PotPair) : RootEnumeration38 (dirichletChar φ) (mu φ) :=
  criticalCandidate_enumeration38 (Ncut_spec φ)

theorem mu_far_mem (φ : PotPair) {n : ℤ} (hn : (Ncut φ : ℤ) < |n|) :
    mu φ n ∈ ball (countingCenter38 n) (Real.pi / 4) := by
  have h := Ncut_spec φ
  have hn' : ¬ (-(Ncut φ : ℤ) ≤ n ∧ n ≤ (Ncut φ : ℤ)) := fun hh =>
    absurd (abs_le.2 hh) (not_le.2 hn)
  have hi := criticalCandidate_far_index38 h hn'
  have hm : (smallRoots (dirichletChar φ) n).getD 0 0 ∈ smallRoots (dirichletChar φ) n := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have := ((counting_mem_zeroMultiset38 h (countingCenter38 n) (Real.pi / 4) _).mp
    ((sortComplexRoots_mem38 _ _).mp hm))
  simp only [mu, criticalCandidate38, if_neg hn']
  exact this.1

theorem mu_summable (φ : PotPair) :
    Summable (fun n : ℤ => ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
  obtain ⟨V, hV, hφV, N, C, h⟩ := NlsGge.Atomic.G1043S1.G1043_whole φ
  obtain ⟨μ', hfar, hsum, -⟩ := h φ hφV
  set M : ℕ := max N (Ncut φ) with hM
  have heq : ∀ n : ℤ, M < n.natAbs → mu φ n = μ' n := by
    intro n hn
    have h1 : N < n.natAbs := lt_of_le_of_lt (le_max_left _ _) hn
    have h2 : (Ncut φ : ℤ) < |n| := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hn
    exact (hfar n h1).2.2 _ (mu_far_mem φ h2) ((mu_enum φ).1 n)
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hfin : (Set.Icc (-(M : ℤ)) (M : ℤ)).Finite := Set.finite_Icc _ _
  filter_upwards [hfin.compl_mem_cofinite] with n hn
  have hn' : M < n.natAbs := by
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hn
    omega
  have h1 : N < n.natAbs := lt_of_le_of_lt (le_max_left _ _) hn'
  rw [Real.norm_of_nonneg (by positivity), if_pos h1, heq n hn']

theorem mu_multipliable (φ : PotPair) (z : ℂ) :
    Multipliable (fun m : ℤ => (mu φ m - z) / (πn m : ℂ)) (symmetricIcc ℤ) :=
  (Lib.product_entire (mu φ) (mu_summable φ)).1 z

def normProd (φ : PotPair) (z : ℂ) : ℂ :=
  -∏'[symmetricIcc ℤ] m : ℤ, (mu φ m - z) / (πn m : ℂ)

theorem differentiable_normProd (φ : PotPair) :
    Differentiable ℂ (normProd φ) :=
  (Lib.product_entire (mu φ) (mu_summable φ)).2.1.neg

theorem order_normProd (φ : PotPair) (w : ℂ) :
    analyticOrderAt (normProd φ) w = analyticOrderAt (dirichletChar φ) w := by
  change analyticOrderAt (-(fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ,
    (mu φ m - z) / (πn m : ℂ))) w = _
  rw [analyticOrderAt_neg, (Lib.product_entire (mu φ) (mu_summable φ)).2.2 w]
  exact ((mu_enum φ).2.2 w).2

                                                                                                            

theorem piN_cast (m : ℤ) : ((πn m : ℝ) : ℂ) = if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ) := by
  unfold πn NlsGge.GK38.Lib.piN
  split_ifs <;> push_cast <;> rfl

theorem partial_prod_tendsto (σ : ℤ → ℂ)
    (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) (z : ℂ) :
    Tendsto (fun K : ℕ => ∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (σ m - z) / (πn m : ℂ)) atTop
      (𝓝 (singleProduct38 σ z)) := by
  have hP := ((Lib.product_entire σ hσ).1 z).hasProd
  unfold HasProd at hP
  rw [symmetricIcc_eq_map_Icc_nat, tendsto_map'_iff] at hP
  exact hP

theorem product_growthG (σ : ℤ → ℂ)
    (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = n * Real.pi + Real.pi / 2 →
      ‖singleProduct38 σ z + Complex.sin z‖ ≤ ε * ‖Complex.sin z‖ := by
  intro ε hε
  let s : Lib.L2Z := ⟨fun m => σ m - (m : ℂ) * (Real.pi : ℂ),
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr (by simpa using hσ)⟩
  obtain ⟨F, hF1, -, hF3⟩ := NlsGge.Atomic.G1050S2.K10.g2010_ratio_one s
  obtain ⟨N0, hN0⟩ := hF3 ε hε
  refine ⟨N0, fun n hn z hz => ?_⟩
  have hzs : z ∈ Metric.sphere (0 : ℂ) ((n : ℝ) * Real.pi + Real.pi / 2) := by
    simpa [mem_sphere_zero_iff_norm] using hz
  have hsin : Complex.sin z ≠ 0 := by
    have hd := Lib.pi_mul_dd_le hz
    exact (NlsGge.Atomic.G1050S2.K10.sin_ne_zero_of_norm hz)
  have hr := hN0 n hn z hzs
  have hlim := partial_prod_tendsto σ hσ z
  have hlim2 : Tendsto (fun K : ℕ => -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (σ m - z) / (πn m : ℂ))) atTop (𝓝 (-(singleProduct38 σ z))) := hlim.neg
  have hF := hF1 z
  have heq : (fun K : ℕ => -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (((m : ℂ) * (Real.pi : ℂ) + (s : ℤ → ℂ) m) - z) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)))) =
      fun K : ℕ => -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (σ m - z) / (πn m : ℂ)) := by
    funext K
    congr 1
    refine Finset.prod_congr rfl fun m _ => ?_
    rw [piN_cast]
    congr 1
    show (m : ℂ) * (Real.pi : ℂ) + (σ m - (m : ℂ) * (Real.pi : ℂ)) - z = σ m - z
    ring
  rw [heq] at hF
  have hFeq : F z = -(singleProduct38 σ z) := tendsto_nhds_unique hF hlim2
  rw [hFeq] at hr
  have hne : ‖Complex.sin z‖ ≠ 0 := norm_ne_zero_iff.mpr hsin
  have he : singleProduct38 σ z + Complex.sin z = -((-(singleProduct38 σ z)) / Complex.sin z - 1) *
      Complex.sin z := by field_simp; ring
  rw [he, norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)


/-- Fixed-potential strict circle ratio, with sine and denominator nonzero first. -/
theorem mu_ratio_circle (φ : PotPair) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
      ‖z‖ = (n : ℝ) * Real.pi + Real.pi / 2 →
      Complex.sin z ≠ 0 ∧ normProd φ z ≠ 0 ∧
        ‖dirichletChar φ z / normProd φ z - 1‖ < ε := by
  let δ : ℝ := min (ε / 8) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδquarter : δ ≤ 1 / 4 := min_le_right _ _
  have hδeps : δ ≤ ε / 8 := min_le_left _ _
  obtain ⟨Np, hp⟩ := product_growthG (mu φ) (mu_summable φ) δ hδ
  obtain ⟨U, hU, R, hR⟩ := NlsGge.Atomic.G1043S1.K42.dirichlet_asymp_s3 φ (δ / sineOffDiscsConstant38)
    (div_pos hδ sineOffDiscsConstant38_pos)
  obtain ⟨Nr, hNr⟩ := exists_nat_ge (R / Real.pi)
  have hNrR : R ≤ (Nr : ℝ) * Real.pi + Real.pi / 2 := by
    have hh := (div_le_iff₀ Real.pi_pos).mp hNr
    linarith [Real.pi_pos]
  refine ⟨max Np Nr, fun n hn z hz => ?_⟩
  have hnp : Np ≤ n := (le_max_left _ _).trans hn
  have hnr : (Nr : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_right Np Nr).trans hn
  have hzR : R ≤ ‖z‖ := by
    rw [hz]
    nlinarith [Real.pi_pos]
  have hsep : ∀ m : ℤ, Real.pi / 4 ≤ ‖z - countingCenter38 m‖ := by
    intro m
    have hh := Lib.pi_mul_dd_le hz m
    have hd := Lib.half_le_circDist n m
    rw [norm_sub_rev] at hh
    change Real.pi * Lib.circDist n m ≤ ‖z - countingCenter38 m‖ at hh
    nlinarith [Real.pi_pos]
  have hsin : Complex.sin z ≠ 0 := counting_sin_ne_zero38 hsep
  have hspos : 0 < ‖Complex.sin z‖ := norm_pos_iff.mpr hsin
  have hprod : ‖normProd φ z - Complex.sin z‖ ≤ δ * ‖Complex.sin z‖ := by
    have hh := hp n hnp z hz
    have he : normProd φ z - Complex.sin z =
        -((∏'[symmetricIcc ℤ] m : ℤ, (mu φ m - z) / (πn m : ℂ)) + Complex.sin z) := by
      dsimp [normProd]
      ring
    rw [he, norm_neg]
    exact hh
  have hchar : ‖dirichletChar φ z - Complex.sin z‖ ≤ δ * ‖Complex.sin z‖ := by
    have hh := hR φ (mem_of_mem_nhds hU) z hzR
    have hbound := sine_off_discs_lower_bound38 z hsep
    have hle := mul_le_mul_of_nonneg_left hbound (div_pos hδ sineOffDiscsConstant38_pos).le
    have he : δ / sineOffDiscsConstant38 * (sineOffDiscsConstant38 * ‖Complex.sin z‖) =
        δ * ‖Complex.sin z‖ := by
      field_simp [sineOffDiscsConstant38_pos.ne']
    exact hh.trans (by simpa only [he] using hle)
  have hlower : ‖Complex.sin z‖ / 2 ≤ ‖normProd φ z‖ := by
    have hh := norm_sub_norm_le (Complex.sin z) (normProd φ z)
    rw [norm_sub_rev] at hh
    nlinarith
  have hnz : normProd φ z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hlower)
  have hnum : ‖dirichletChar φ z - normProd φ z‖ ≤ 2 * δ * ‖Complex.sin z‖ := by
    have hh := norm_sub_le (dirichletChar φ z - Complex.sin z)
      (normProd φ z - Complex.sin z)
    have he : dirichletChar φ z - Complex.sin z -
        (normProd φ z - Complex.sin z) =
        dirichletChar φ z - normProd φ z := by ring
    rw [he] at hh
    linarith
  refine ⟨hsin, hnz, ?_⟩
  rw [div_sub_one hnz, norm_div]
  have hle : ‖dirichletChar φ z - normProd φ z‖ /
      ‖normProd φ z‖ ≤ 4 * δ := by
    apply (div_le_iff₀ (norm_pos_iff.mpr hnz)).mpr
    have hh := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 4 * δ by positivity)
    nlinarith
  exact hle.trans_lt (by linarith)

/-- The full Dirichlet characteristic, including its roots, is the normalized symmetric product. -/
theorem mu_product (φ : PotPair) (z : ℂ) :
    dirichletChar φ z = -∏'[symmetricIcc ℤ] m : ℤ, (mu φ m - z) / (πn m : ℂ) := by
  have he := Lib.entire_eq_of_ratio_tendsto_one
    (fun w => (analyticOnNhd_dirichletChar_z φ w (mem_univ _)).differentiableAt)
    (differentiable_normProd φ)
    (fun w => (order_normProd φ w).le)
    (fun ε hε => by
      obtain ⟨N, hN⟩ := mu_ratio_circle φ ε hε
      exact ⟨N, fun n hn w hw => (hN n hn w hw).2.2⟩)
  exact congrFun he z

theorem G1044_main :
    ((
  ∃ mu : PotPair → ℤ → ℂ,
    (∀ ψ : PotPair, ∀ z : ℂ,
        analyticOrderAt (fun w : ℂ => dirichletChar ψ w) z = Set.encard {n : ℤ | mu ψ n = z}) ∧
    (∀ ψ : PotPair, ∀ lam : ℂ,
        Filter.Tendsto
          (fun K : ℕ =>
            -(∏ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
              (mu ψ m - lam) / (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))))
          Filter.atTop
          (nhds (dirichletChar ψ lam))) ∧
    (∀ ψ : PotPair,
        Summable (fun n : ℤ => ‖mu ψ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2))
  : Prop)) := by
  refine ⟨mu, ?_, ?_, ?_⟩
  · intro ψ z
    exact ((mu_enum ψ).2.2 z).2.symm
  · intro ψ lam
    have hP := (mu_multipliable ψ lam).hasProd
    unfold HasProd at hP
    rw [symmetricIcc_eq_map_Icc_nat, tendsto_map'_iff] at hP
    have hP2 := hP.neg
    rw [mu_product ψ lam]
    refine hP2.congr (fun K => ?_)
    simp only [Function.comp_apply]
    congr 1
    refine Finset.prod_congr rfl (fun m _ => ?_)
    rw [piN_cast]
  · intro ψ
    exact mu_summable ψ

end

end NlsGge.Atomic.G1044S3M

