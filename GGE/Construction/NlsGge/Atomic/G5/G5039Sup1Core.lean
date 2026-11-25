import Mathlib
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.Atomic.G5.G5017Host
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G4.G4043

                                                                                
                                                                                            
                                                                                                         
                                                                                                          
                                                                                                              
                                                                                                                    
                                                                                                                    
                                                                                                   
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5039Aux
noncomputable section

theorem pairPoissonCLM_lin_left (a b : ℂ) (A B M : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM (a • A + b • B) M = a * pairPoissonCLM A M + b * pairPoissonCLM B M := by
  unfold pairPoissonCLM
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem pairPoissonCLM_lin_right (a b : ℂ) (L A B : PotPair →L[ℂ] ℂ) :
    pairPoissonCLM L (a • A + b • B) = a * pairPoissonCLM L A + b * pairPoissonCLM L B := by
  rw [pairPoissonCLM_antisymm, pairPoissonCLM_lin_left, pairPoissonCLM_antisymm L A,
    pairPoissonCLM_antisymm L B]
  ring

/-- Polar decomposition of a Cartesian differential on the chart `X^2+Y^2 ≠ 0`. -/
theorem decompX (X Y : ℂ) (A B : PotPair →L[ℂ] ℂ) (hR : X ^ 2 + Y ^ 2 ≠ 0) :
    A = (X / (X ^ 2 + Y ^ 2)) • (X • A + Y • B) +
      (-Y) • ((X ^ 2 + Y ^ 2)⁻¹ • (X • B - Y • A)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem decompY (X Y : ℂ) (A B : PotPair →L[ℂ] ℂ) (hR : X ^ 2 + Y ^ 2 ≠ 0) :
    B = (Y / (X ^ 2 + Y ^ 2)) • (X • A + Y • B) +
      X • ((X ^ 2 + Y ^ 2)⁻¹ • (X • B - Y • A)) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- The action differential on `sourceBetaW`, from the landed identity `I = (X^2+Y^2)/2` (G4043). -/
theorem fderiv_action_eq (j : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW)
    (hX : DifferentiableAt ℂ (cartesianX j) φ) (hY : DifferentiableAt ℂ (cartesianY j) φ) :
    fderiv ℂ (fun ψ => gkActionC38 ψ j) φ =
      cartesianX j φ • fderiv ℂ (cartesianX j) φ + cartesianY j φ • fderiv ℂ (cartesianY j) φ := by
  have hev : (fun ψ => gkActionC38 ψ j) =ᶠ[𝓝 φ]
      fun ψ => (cartesianX j ψ * cartesianX j ψ + cartesianY j ψ * cartesianY j ψ) * (2 : ℂ)⁻¹ := by
    filter_upwards [sourceFamily.V_open.mem_nhds hφ] with ψ hψ
    rw [G4043 j ψ hψ]
    ring
  have hd : HasFDerivAt
      (fun ψ => (cartesianX j ψ * cartesianX j ψ + cartesianY j ψ * cartesianY j ψ) * (2 : ℂ)⁻¹)
      ((2 : ℂ)⁻¹ • ((cartesianX j φ • fderiv ℂ (cartesianX j) φ +
          cartesianX j φ • fderiv ℂ (cartesianX j) φ) +
        (cartesianY j φ • fderiv ℂ (cartesianY j) φ +
          cartesianY j φ • fderiv ℂ (cartesianY j) φ))) φ :=
    HasFDerivAt.mul_const
      (HasFDerivAt.add (HasFDerivAt.mul hX.hasFDerivAt hX.hasFDerivAt)
        (HasFDerivAt.mul hY.hasFDerivAt hY.hasFDerivAt)) (2 : ℂ)⁻¹
  rw [hev.fderiv_eq, hd.fderiv]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pairPoissonCLM_self (L : PotPair →L[ℂ] ℂ) : pairPoissonCLM L L = 0 := by
  have h := pairPoissonCLM_antisymm L L
  linear_combination h / 2

/-- Expansion of a bracket of two polar combinations. -/
theorem expand (I T I' T' : PotPair →L[ℂ] ℂ) (a b c d : ℂ) :
    pairPoissonCLM (a • I + b • T) (c • I' + d • T') =
      a * c * pairPoissonCLM I I' + a * d * pairPoissonCLM I T' +
        b * c * pairPoissonCLM T I' + b * d * pairPoissonCLM T T' := by
  rw [pairPoissonCLM_lin_left, pairPoissonCLM_lin_right, pairPoissonCLM_lin_right]
  ring

theorem dX_polar (j : ℤ) (φ : PotPair)
    (hdI : fderiv ℂ (fun ψ => gkActionC38 ψ j) φ =
      cartesianX j φ • fderiv ℂ (cartesianX j) φ + cartesianY j φ • fderiv ℂ (cartesianY j) φ)
    (hR : cartesianX j φ ^ 2 + cartesianY j φ ^ 2 ≠ 0) :
    fderiv ℂ (cartesianX j) φ =
      (cartesianX j φ / (cartesianX j φ ^ 2 + cartesianY j φ ^ 2)) •
          fderiv ℂ (fun ψ => gkActionC38 ψ j) φ +
        (-cartesianY j φ) • angleDerivative j φ := by
  rw [hdI]
  exact decompX _ _ _ _ hR

theorem dY_polar (j : ℤ) (φ : PotPair)
    (hdI : fderiv ℂ (fun ψ => gkActionC38 ψ j) φ =
      cartesianX j φ • fderiv ℂ (cartesianX j) φ + cartesianY j φ • fderiv ℂ (cartesianY j) φ)
    (hR : cartesianX j φ ^ 2 + cartesianY j φ ^ 2 ≠ 0) :
    fderiv ℂ (cartesianY j) φ =
      (cartesianY j φ / (cartesianX j φ ^ 2 + cartesianY j φ ^ 2)) •
          fderiv ℂ (fun ψ => gkActionC38 ψ j) φ +
        cartesianX j φ • angleDerivative j φ := by
  rw [hdI]
  exact decompY _ _ _ _ hR

/-- Same-index case. -/
theorem core39_same (φ : PotPair) (m : ℤ)
    (hdI : fderiv ℂ (fun ψ => gkActionC38 ψ m) φ =
      cartesianX m φ • fderiv ℂ (cartesianX m) φ + cartesianY m φ • fderiv ℂ (cartesianY m) φ)
    (hR : cartesianX m φ ^ 2 + cartesianY m φ ^ 2 ≠ 0)
    (hII : pairPoisson (fun ψ => gkActionC38 ψ m) (fun ψ => gkActionC38 ψ m) φ = 0)
    (hTI : pairPoissonCLM (angleDerivative m φ) (fderiv ℂ (fun ψ => gkActionC38 ψ m) φ) = 1)
    (hTT : anglePoisson m m φ = 0) :
    pairPoissonCLM (fderiv ℂ (cartesianX m) φ) (fderiv ℂ (cartesianY m) φ) = -1 := by
  have hIT : pairPoissonCLM (fderiv ℂ (fun ψ => gkActionC38 ψ m) φ) (angleDerivative m φ) = -1 := by
    rw [pairPoissonCLM_antisymm, hTI]
  have hII' : pairPoissonCLM (fderiv ℂ (fun ψ => gkActionC38 ψ m) φ)
      (fderiv ℂ (fun ψ => gkActionC38 ψ m) φ) = 0 := hII
  have hTT' : pairPoissonCLM (angleDerivative m φ) (angleDerivative m φ) = 0 := hTT
  have hX := dX_polar m φ hdI hR
  have hY := dY_polar m φ hdI hR
  rw [hX, hY, expand, hII', hIT, hTI, hTT']
  field_simp
  ring

/-- Distinct-index case. -/
theorem core39_diff (φ : PotPair) (m n : ℤ)
    (hdIm : fderiv ℂ (fun ψ => gkActionC38 ψ m) φ =
      cartesianX m φ • fderiv ℂ (cartesianX m) φ + cartesianY m φ • fderiv ℂ (cartesianY m) φ)
    (hdIn : fderiv ℂ (fun ψ => gkActionC38 ψ n) φ =
      cartesianX n φ • fderiv ℂ (cartesianX n) φ + cartesianY n φ • fderiv ℂ (cartesianY n) φ)
    (hRm : cartesianX m φ ^ 2 + cartesianY m φ ^ 2 ≠ 0)
    (hRn : cartesianX n φ ^ 2 + cartesianY n φ ^ 2 ≠ 0)
    (hII : pairPoissonCLM (fderiv ℂ (fun ψ => gkActionC38 ψ m) φ)
      (fderiv ℂ (fun ψ => gkActionC38 ψ n) φ) = 0)
    (hTI : pairPoissonCLM (angleDerivative m φ) (fderiv ℂ (fun ψ => gkActionC38 ψ n) φ) = 0)
    (hTI' : pairPoissonCLM (angleDerivative n φ) (fderiv ℂ (fun ψ => gkActionC38 ψ m) φ) = 0)
    (hTT : pairPoissonCLM (angleDerivative m φ) (angleDerivative n φ) = 0) :
    pairPoissonCLM (fderiv ℂ (cartesianX m) φ) (fderiv ℂ (cartesianX n) φ) = 0 ∧
    pairPoissonCLM (fderiv ℂ (cartesianX m) φ) (fderiv ℂ (cartesianY n) φ) = 0 ∧
    pairPoissonCLM (fderiv ℂ (cartesianY m) φ) (fderiv ℂ (cartesianY n) φ) = 0 := by
  have hIT : pairPoissonCLM (fderiv ℂ (fun ψ => gkActionC38 ψ m) φ) (angleDerivative n φ) = 0 := by
    rw [pairPoissonCLM_antisymm, hTI', neg_zero]
  rw [dX_polar m φ hdIm hRm, dY_polar m φ hdIm hRm, dX_polar n φ hdIn hRn, dY_polar n φ hdIn hRn,
    expand, expand, expand, hII, hIT, hTI, hTT]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Core of G5-039 at one point `φ`, from the landed bracket facts as explicit hypotheses. -/
theorem core39 (φ : PotPair) (m n : ℤ)
    (hdI : ∀ j : ℤ, fderiv ℂ (fun ψ => gkActionC38 ψ j) φ =
      cartesianX j φ • fderiv ℂ (cartesianX j) φ + cartesianY j φ • fderiv ℂ (cartesianY j) φ)
    (hRm : cartesianX m φ ^ 2 + cartesianY m φ ^ 2 ≠ 0)
    (hRn : cartesianX n φ ^ 2 + cartesianY n φ ^ 2 ≠ 0)
    (hII : ∀ a b : ℤ, pairPoisson (fun ψ => gkActionC38 ψ a) (fun ψ => gkActionC38 ψ b) φ = 0)
    (hθI : ∀ a b : ℤ, (a = m ∨ a = n) →
      pairPoissonCLM (angleDerivative a φ) (fderiv ℂ (fun ψ => gkActionC38 ψ b) φ) =
        if b = a then 1 else 0)
    (hθθ : anglePoisson m n φ = 0) :
  pairPoisson (cartesianX m) (cartesianX n) φ = 0 ∧
  pairPoisson (cartesianX m) (cartesianY n) φ =
    -(if m = n then (1 : ℂ) else 0) ∧
  pairPoisson (cartesianY m) (cartesianY n) φ = 0 := by
  show pairPoissonCLM (fderiv ℂ (cartesianX m) φ) (fderiv ℂ (cartesianX n) φ) = 0 ∧
    pairPoissonCLM (fderiv ℂ (cartesianX m) φ) (fderiv ℂ (cartesianY n) φ) =
      -(if m = n then (1 : ℂ) else 0) ∧
    pairPoissonCLM (fderiv ℂ (cartesianY m) φ) (fderiv ℂ (cartesianY n) φ) = 0
  by_cases hmn : m = n
  · subst hmn
    have h1 := hθI m m (Or.inl rfl)
    rw [if_pos rfl] at h1
    refine ⟨pairPoissonCLM_self _, ?_, pairPoissonCLM_self _⟩
    rw [if_pos rfl]
    exact core39_same φ m (hdI m) hRm (hII m m) h1 hθθ
  · have h1 := hθI m n (Or.inl rfl)
    have h2 := hθI n m (Or.inr rfl)
    rw [if_neg (Ne.symm hmn)] at h1
    rw [if_neg hmn] at h2
    rw [if_neg hmn, neg_zero]
    exact core39_diff φ m n (hdI m) (hdI n) hRm hRn (hII m n) h1 h2 hθθ

end
end G5039Aux
end NlsGge.GKDefinitionDesign
