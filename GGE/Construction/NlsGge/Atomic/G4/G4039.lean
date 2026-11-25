import Mathlib
import NlsGge.Atomic.G4.G4039Host
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.GK38.Defs

                                                                                                    
                                                                           
                                                                                                                      
                                                                                                                   
                                                                                                                        
                                                                                                                                  
                                                                                                                                      
                                                                                                                  
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open scoped ENNReal BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G4039Aux

/-- The retained local square-sum bounds of the single selected family, stated for `cartesianX`/`cartesianY`. -/
theorem local_l2 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ sourceBetaW ∧ ∃ C : ℝ, 0 < C ∧
      ∀ φ : PotPair, φ ∈ V →
        Summable (fun n : ℤ => ‖cartesianX n φ‖ ^ 2) ∧
        (∑' n : ℤ, ‖cartesianX n φ‖ ^ 2) ≤ C ∧
        Summable (fun n : ℤ => ‖cartesianY n φ‖ ^ 2) ∧
        (∑' n : ℤ, ‖cartesianY n φ‖ ^ 2) ≤ C :=
  (Classical.choose_spec
    NlsGge.Atomic.ExistingPhysicalFamily.physicalLocalFamily_with_retained_bounds).2.1 φ₀ hφ₀

/-- Summability and the total square sum over `Bool × ℤ` from the two rows. -/
theorem sq_sum_prod (f : Bool × ℤ → ℂ)
    (hx : Summable (fun n : ℤ => ‖f (true, n)‖ ^ 2))
    (hy : Summable (fun n : ℤ => ‖f (false, n)‖ ^ 2)) :
    Summable (fun j : Bool × ℤ => ‖f j‖ ^ 2) ∧
    (∑' j : Bool × ℤ, ‖f j‖ ^ 2) =
      (∑' n : ℤ, ‖f (true, n)‖ ^ 2) + ∑' n : ℤ, ‖f (false, n)‖ ^ 2 := by
  set g : Bool × ℤ → ℝ := fun j => ‖f j‖ ^ 2 with hg
  set e : Bool × ℤ ≃ ℤ ⊕ ℤ := Equiv.boolProdEquivSum ℤ with he
  have hl : (g ∘ e.symm) ∘ Sum.inl = fun n : ℤ => ‖f (false, n)‖ ^ 2 := by
    funext n; simp [he, hg, Equiv.boolProdEquivSum]
  have hr : (g ∘ e.symm) ∘ Sum.inr = fun n : ℤ => ‖f (true, n)‖ ^ 2 := by
    funext n; simp [he, hg, Equiv.boolProdEquivSum]
  have h1 : Summable ((g ∘ e.symm) ∘ Sum.inl) := by rw [hl]; exact hy
  have h2 : Summable ((g ∘ e.symm) ∘ Sum.inr) := by rw [hr]; exact hx
  have hS : Summable (g ∘ e.symm) := Summable.sum _ h1 h2
  have hsum : Summable g := by
    have := (e.symm.summable_iff (f := g)).1 hS
    exact this
  refine ⟨hsum, ?_⟩
  have ht : ∑' j, g j = ∑' i, (g ∘ e.symm) i := (e.symm.tsum_eq g).symm
  have e1 : (∑' i : ℤ, (g ∘ e.symm) (Sum.inl i)) = ∑' n : ℤ, ‖f (false, n)‖ ^ 2 :=
    congrArg tsum hl
  have e2 : (∑' i : ℤ, (g ∘ e.symm) (Sum.inr i)) = ∑' n : ℤ, ‖f (true, n)‖ ^ 2 :=
    congrArg tsum hr
  rw [ht, Summable.tsum_sum h1 h2, e1, e2, add_comm]

end G4039Aux

theorem G4039 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
    ∃ V : Set PotPair,
      V ∈ 𝓝 φ₀ ∧ V ⊆ sourceBetaW ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ φ ∈ V,
          Memℓp (cartesianSequence φ) 2 ∧
          ‖birkhoffCartesian φ‖ ≤ C ∧
          (∀ n : ℤ,
            birkhoffCartesian φ (true, n) = cartesianX n φ ∧
            birkhoffCartesian φ (false, n) = cartesianY n φ) := by
  obtain ⟨V, hVn, hVS, C, hC, hbd⟩ := G4039Aux.local_l2 φ₀ hφ₀
  refine ⟨V, hVn, hVS, Real.sqrt (2 * C), Real.sqrt_pos.2 (by positivity), fun φ hφ => ?_⟩
  obtain ⟨hsx, hbx, hsy, hby⟩ := hbd φ hφ
  have hrx : ∀ n : ℤ, cartesianSequence φ (true, n) = cartesianX n φ := fun n => by
    simp [cartesianSequence]
  have hry : ∀ n : ℤ, cartesianSequence φ (false, n) = cartesianY n φ := fun n => by
    simp [cartesianSequence]
  obtain ⟨hsum, htsum⟩ := G4039Aux.sq_sum_prod (cartesianSequence φ)
    (by simpa only [hrx] using hsx) (by simpa only [hry] using hsy)
  have hmem : Memℓp (cartesianSequence φ) 2 := by
    rw [memℓp_gen_iff (by simp)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum
  have hbir : birkhoffCartesian φ = ⟨cartesianSequence φ, hmem⟩ := by
    simp [birkhoffCartesian, hmem]
  refine ⟨hmem, ?_, fun n => ?_⟩
  · have hn := lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (E := fun _ : Bool × ℤ => ℂ)
      (by simp) (⟨cartesianSequence φ, hmem⟩ : lp (fun _ : Bool × ℤ => ℂ) 2)
    rw [hbir, hn]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hS : (∑' j : Bool × ℤ, ‖cartesianSequence φ j‖ ^ 2) ≤ 2 * C := by
      rw [htsum]
      simp only [hrx, hry]
      linarith
    have hS0 : 0 ≤ ∑' j : Bool × ℤ, ‖cartesianSequence φ j‖ ^ 2 :=
      tsum_nonneg (fun j => by positivity)
    change (∑' j : Bool × ℤ, ‖cartesianSequence φ j‖ ^ 2) ^ (1 / (2 : ℝ)) ≤ _
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hS0 hS (by norm_num)
  · rw [hbir]
    exact ⟨hrx n, hry n⟩

end
end NlsGge.GKDefinitionDesign
