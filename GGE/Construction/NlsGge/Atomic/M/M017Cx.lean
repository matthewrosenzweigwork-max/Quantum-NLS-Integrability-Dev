import Mathlib
import NlsGge.Atomic.M.M016Laurent
import NlsGge.Atomic.M.M017CxCore
import NlsGge.Atomic.M.M017CxGK
import NlsGge.Atomic.M.M008Collapsed
import NlsGge.Atomic.M.M014Host
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.Atomic.M.M010Support1

                                                                                               
                                                                                                                   
                                                                                                                    
                                                                                                                  
                                                                                                 
                                                                                                               
                                                                                                                   
                                                                                                                     
                                                                                         
                                                                                                                   
                                
                                                                                                          
                                                                                       
                                                                                                             
                                                                                 

set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem higher_action_trace_finitegap
    (N : ℕ) (φ : KSPS.SobolevC N)
    (hW : KSPS.toPotPair φ ∈ gkW)
    (hfg : finiteGapPair (KSPS.toPotPair φ))
    (k : ℕ) (hk : 2 ≤ k) (hkN : k ≤ N + 1) :
    Summable (fun n : ℤ => complexHigherAction (KSPS.toPotPair φ) n k) ∧
    (∑' n : ℤ, complexHigherAction (KSPS.toPotPair φ) n k) =
      -((2 * Complex.I) ^ (k - 1))⁻¹ *
        hierarchyCharge φ ⟨k, (by omega), hkN⟩ := by
  set ψ : PotPair := KSPS.toPotPair φ with hψ
  set G : ℂ → ℂ := fun z => deriv (discrim ψ) z / canonRoot38 ψ z with hGdef
  -- the action is k⁻¹ π⁻¹ times the abelian period of z^k Δ'
  have hJ : ∀ n : ℤ, complexHigherAction ψ n k =
      (k : ℂ)⁻¹ * ((1 / (Real.pi : ℂ)) * abelianPeriod38 n ψ (fun z : ℂ => z ^ k * deriv (discrim ψ) z)) := by
    intro n
    rw [complexHigherAction, dif_pos (by omega : 1 ≤ k)]
    rfl
  -- collapsed gaps contribute zero
  obtain ⟨c0, N0, hgeom, hspec⟩ := isolating_family38 ψ hW
  have hzero : ∀ n : ℤ, NlsGge.GKDefinitionDesign.gap ψ n = 0 → abelianPeriod38 n ψ (fun z : ℂ => z ^ k * deriv (discrim ψ) z) = 0 := by
    intro n hgap
    have hlp : lamPlus ψ n = lamMinus ψ n := sub_eq_zero.1 hgap
    obtain ⟨g, hg, hgeq⟩ := MContour.omega_extends_collapsed_complex ψ hW n hlp
    have hR : 0 < discR ψ n := (hgeom.1 n).1
    have ha : lamMinus ψ n ∈ ball (discC ψ n) (discR ψ n) :=
      (hspec.1 n).1 (left_mem_segment ℝ _ _)
    have hsph : sphere (discC ψ n) (discR ψ n) ⊆ actionCutDomain38 ψ := by
      have hf := isolating_family38 ψ hW
      simpa only [sub_zero, one_smul, zero_smul, add_zero, one_mul, zero_mul] using
        action_contour_sphere_subset38 ψ (discC ψ) (discC ψ) (discR ψ) (discR ψ) hf hf n 0
          ⟨le_rfl, zero_le_one⟩
    show (∮ z in C(discC ψ n, discR ψ n), z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z) = 0
    refine M017Cx.circle_zero_of_punctured (discC ψ n) (lamMinus ψ n) (discR ψ n) hR
      (fun z => z ^ k * g z) (fun z => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z)
      ((analyticOnNhd_id.pow k).mul hg) ha ?_ ?_
    · intro z hz hne
      show z ^ k * g z = z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z
      rw [hgeq z hz hne, MContour.omega, mul_div_assoc]
    · intro z hz
      exact M017Cx.quot_analyticAt ψ hW k z (hsph hz)
  have hfin : {n : ℤ | NlsGge.GKDefinitionDesign.gap ψ n ≠ 0}.Finite := hfg
  set S : Finset ℤ := hfin.toFinset with hS
  have hsupp : ∀ n : ℤ, n ∉ S → complexHigherAction ψ n k = 0 := by
    intro n hn
    have hg0 : NlsGge.GKDefinitionDesign.gap ψ n = 0 := by
      by_contra h
      exact hn ((Set.Finite.mem_toFinset hfin).2 h)
    rw [hJ n, hzero n hg0, mul_zero, mul_zero]
  have hsum : Summable (fun n : ℤ => complexHigherAction ψ n k) := summable_of_ne_finset_zero hsupp
  refine ⟨hsum, ?_⟩
  -- the same exterior F from M-016
  obtain ⟨R, F, hrep, -, hPLC⟩ := finitegap_primitive_laurent N φ hW hfg
  obtain ⟨C, R1, -, -, hb⟩ := hPLC k (by omega) hkN
  -- derivative of F on cut-free points outside the disc
  obtain ⟨P, L, hP, hPL, hval⟩ := MPrimitive.symmetric_value_data_lim ψ hW
  have hCo := MPrimitive.cutFreeFiber_isOpen ψ hW
  have hLP : ∀ w ∈ MPrimitive.cutFreeFiber ψ, L w = P w := fun w hw => by
    have h1 := hPL w (Or.inl hw)
    rw [nhdsWithin_eq_nhds.mpr (hCo.mem_nhds hw)] at h1
    exact tendsto_nhds_unique h1 (hP w hw).continuousAt.tendsto
  have hFder : ∀ z : ℂ, R < ‖z‖ → z ∉ gapSegments38 ψ → HasDerivAt F (G z) z := by
    intro z hzR hzc
    have hU : {w : ℂ | R < ‖w‖} ∩ MPrimitive.cutFreeFiber ψ ∈ 𝓝 z :=
      ((isOpen_lt continuous_const continuous_norm).inter hCo).mem_nhds ⟨hzR, hzc⟩
    have heq : (fun w => P w - L (lamMinus ψ 0)) =ᶠ[𝓝 z] F := by
      filter_upwards [hU] with w hw
      obtain ⟨hw', e⟩ := hrep.2 w hw.1
      rw [e]
      have := hval w hw'.2
      rw [show primitive ⟨(ψ, w), hw'⟩ = MPrimitive.symmetricPrimitive ⟨(ψ, w), ⟨hW, hw'.2⟩⟩ from rfl,
        this, hLP w hw.2]
    exact ((hP z hzc).sub_const _).congr_of_eventuallyEq heq.symm
  have hGcont : ∀ z : ℂ, z ∉ gapSegments38 ψ → ContinuousAt G z := by
    intro z hz
    have h := (M017Cx.quot_analyticAt ψ hW 0 z hz).continuousAt
    have e : (fun w : ℂ => w ^ 0 * deriv (discrim ψ) w / canonRoot38 ψ w) = G := by
      funext w; simp [hGdef]
    rwa [e] at h
  -- the circles
  have hρ : Tendsto (fun ν : ℕ => (ν : ℝ) * Real.pi + Real.pi / 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const Real.pi_pos)
  obtain ⟨Lc, hLc⟩ := M017Cx.partial_sum_circle ψ hW k
  set ν₀ : ℕ := S.sup Int.natAbs with hν₀
  have hcirc : ∀ᶠ ν : ℕ in atTop, Lc ≤ ν ∧ ν₀ ≤ ν ∧ R < (ν : ℝ) * Real.pi + Real.pi / 2 :=
    (eventually_ge_atTop Lc).and ((eventually_ge_atTop ν₀).and (hρ.eventually (eventually_gt_atTop R)))
  have hder : ∀ᶠ ν : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) ((ν : ℝ) * Real.pi + Real.pi / 2),
      HasDerivAt F (G z) z := by
    filter_upwards [hcirc] with ν hν z hz
    have hzn : ‖z‖ = (ν : ℝ) * Real.pi + Real.pi / 2 := by simpa using hz
    exact hFder z (by rw [hzn]; exact hν.2.2) ((hLc ν hν.1).1 z hz)
  have hGc : ∀ᶠ ν : ℕ in atTop, ContinuousOn G (sphere (0 : ℂ) ((ν : ℝ) * Real.pi + Real.pi / 2)) := by
    filter_upwards [hcirc] with ν hν z hz
    exact (hGcont z ((hLc ν hν.1).1 z hz)).continuousWithinAt
  have hT : ∀ᶠ ν : ℕ in atTop, (∑' n : ℤ, complexHigherAction ψ n k) =
      (k : ℂ)⁻¹ * ((1 / (Real.pi : ℂ)) * ∮ z in C(0, (ν : ℝ) * Real.pi + Real.pi / 2), z ^ k * G z) := by
    filter_upwards [hcirc] with ν hν
    have hout : ∀ n : ℤ, n ∉ Finset.Icc (-(ν : ℤ)) ν → complexHigherAction ψ n k = 0 := by
      intro n hn
      refine hsupp n fun hnS => hn ?_
      have h1 : n.natAbs ≤ ν₀ := Finset.le_sup (f := Int.natAbs) hnS
      rw [Finset.mem_Icc]
      omega
    rw [tsum_eq_sum hout]
    simp only [hJ]
    rw [← Finset.mul_sum, ← Finset.mul_sum, (hLc ν hν.1).2]
    have hint : (fun z : ℂ => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z) = fun z => z ^ k * G z := by
      funext z
      simp only [hGdef]
      ring
    rw [hint]
  exact M017Cx.trace_from_laurent N k hk hkN F G (fun j hj => hierarchyCharge φ ⟨j, hj.1, hj.2⟩) C R1
    hb (fun ν : ℕ => (ν : ℝ) * Real.pi + Real.pi / 2) hρ hder hGc _ hT

end NlsGge.ThirdConsultation.M
