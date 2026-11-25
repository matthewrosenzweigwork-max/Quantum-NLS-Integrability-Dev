import Mathlib
import NlsGge.Sobolev.WeightedHilbert
import NlsGge.Atomic.DM.DM048
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST027
import NlsGge.GK38.Lib.WeaklyAnalytic
import NlsGge.GK38.Lib.WeaklyAnalyticGateaux
import NlsGge.GK38.Lib.HilbertValuedAnalytic
import NlsGge.Atomic.G4.G4004

                                                                            
                                                                                          
                                                                                                                    
                                                                                                                        
                                                                                                                      
                                                                                 
                                                                        
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology
open scoped InnerProductSpace

namespace NlsGge.ThirdConsultation.KST.KST036C

open NlsGge.Atomic.KST002 NlsGge.Pilot NlsGge.GK38.Lib NlsGge.ThirdConsultation.KST

/-- Weierstrass step on a single weighted channel: coordinates differentiable on an open `D ⊆ ℂ` and norm bounded
imply that every continuous linear functional of `g` is differentiable on `D`. -/
theorem dual_comp_channel (W : ℤ → ℝ) [Fact (∀ n : ℤ, 0 < W n)] {D : Set ℂ} (hD : IsOpen D)
    {g : ℂ → WeightedHilbert W}
    (hc : ∀ n : ℤ, DifferentiableOn ℂ (fun ζ => (g ζ : ℤ → ℂ) n) D) {C : ℝ}
    (hC : ∀ ζ ∈ D, ‖g ζ‖ ≤ C) (ℓ : WeightedHilbert W →L[ℂ] ℂ) :
    DifferentiableOn ℂ (fun ζ => ℓ (g ζ)) D := by
  let T : WeightedHilbert W ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 := weightedIsometry W
  let ℓ' : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] ℂ :=
    ℓ.comp (T.symm.toContinuousLinearEquiv : lp (fun _ : ℤ => ℂ) 2 →L[ℂ] WeightedHilbert W)
  have h1 : ∀ n : ℤ, DifferentiableOn ℂ (fun ζ => (T ∘ g) ζ n) D := by
    intro n
    have e : (fun ζ => (T ∘ g) ζ n) =
        fun ζ => (Real.sqrt (W n) : ℂ) * (g ζ : ℤ → ℂ) n := funext fun ζ => rfl
    rw [e]
    exact (differentiableOn_const _).mul (hc n)
  have h2 : ∀ ζ ∈ D, ‖(T ∘ g) ζ‖ ≤ C := fun ζ hζ => by
    simpa [Function.comp, LinearIsometryEquiv.norm_map] using hC ζ hζ
  have h3 := differentiableOn_dual_comp hD h1 h2 ℓ'
  refine h3.congr fun ζ _ => ?_
  simp [ℓ', T]

/-- The weak-analyticity half of the criterion on the pair carrier. -/
theorem weaklyAnalytic_of_coords {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ω : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    {f : E → Weighted ω} {U : Set E} (hU : IsOpen U)
    (hc : ∀ (channel : Bool) (m : ℤ), AnalyticOnNhd ℂ (fun x => f x channel m) U)
    (hb : LocBdd U f) : WeaklyAnalyticOn f U := by
  intro x hx h ℓ
  obtain ⟨r, hr, C, hrU, hC⟩ := exists_ball_of_locBdd hU hb hx
  set D : Set ℂ := {ζ : ℂ | x + ζ • h ∈ ball x r} with hD
  have hcont : Continuous (fun ζ : ℂ => x + ζ • h) := by fun_prop
  have hDo : IsOpen D := (Metric.isOpen_ball (x := x) (ε := r)).preimage hcont
  have h0 : (0 : ℂ) ∈ D := by simpa [hD] using (mem_ball_self hr : x ∈ ball x r)
  set w : Weighted ω := (InnerProductSpace.toDual ℂ (Weighted ω)).symm ℓ with hw
  have hℓ : ∀ v, ℓ v = ⟪w, v⟫_ℂ := fun v => by
    rw [hw, InnerProductSpace.toDual_symm_apply]
  have hterm : ∀ b : Bool, DifferentiableOn ℂ
      (fun ζ : ℂ => (innerSL ℂ (w b)) (f (x + ζ • h) b)) D := by
    intro b
    refine dual_comp_channel (fun k => periodOneWeight ω k ^ 2)
      hDo (g := fun ζ => f (x + ζ • h) b) ?_ (C := C) ?_ (innerSL ℂ (w b))
    · intro n ζ hζ
      have h1 : DifferentiableAt ℂ (fun y => f y b n) (x + ζ • h) :=
        ((hc b n) _ (hrU hζ)).differentiableAt
      have h2 : DifferentiableAt ℂ (fun ζ : ℂ => x + ζ • h) ζ := by fun_prop
      exact (h1.comp ζ h2).differentiableWithinAt
    · intro ζ hζ
      exact (PiLp.norm_apply_le (f (x + ζ • h)) b).trans (hC _ hζ)
  have hsum : DifferentiableOn ℂ (fun ζ : ℂ => ℓ (f (x + ζ • h))) D := by
    have e : (fun ζ : ℂ => ℓ (f (x + ζ • h))) =
        fun ζ => ∑ b : Bool, (innerSL ℂ (w b)) (f (x + ζ • h) b) := by
      funext ζ
      rw [hℓ, PiLp.inner_apply]
      rfl
    rw [e]
    exact DifferentiableOn.fun_sum fun b _ => hterm b
  exact hsum.analyticAt (hDo.mem_nhds h0)

/-- **Hilbert-valued analytic criterion (GK Thm A.5 / G4-004 form), concrete `Weighted ω`.** -/
theorem coord_criterion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ω : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (f : E → Weighted ω) (s : Set E) (hs : IsOpen s)
    (hcoord : ∀ channel m, AnalyticOnNhd ℂ (fun x => f x channel m) s)
    (hbounded : ∀ x ∈ s, ∃ e : ℝ, 0 < e ∧ ∃ C : ℝ,
      ∀ y ∈ Metric.ball x e, ‖f y‖ ≤ C) :
    AnalyticOnNhd ℂ f s := by
  have hb : LocBdd s f := fun x hx => by
    obtain ⟨e, he, C, h⟩ := hbounded x hx
    exact ⟨e, he, C, h⟩
  exact NlsGge.Atomic.G4.analyticOnNhd_of_weakAnalytic_locallyBounded hs
    (weaklyAnalytic_of_coords ω hs hcoord hb) hb

end NlsGge.ThirdConsultation.KST.KST036C
end
