import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationC1

/-! # Coherence of the literal Hamiltonian under zero padding

Equal zero extensions give the same physical inverse field and Hamiltonian.
Differentiating equal coordinate lines proves equality of the vector fields at
common coordinates. No frequency or rotation premise enters this comparison.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

open NlsGge.Birkhoff

local notation "B0" =>
  NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38.toBirkhoffTop38

/-- The literal Hamiltonians agree when the two finite vectors have the same
zero extension, because their actual inverse Birkhoff fields are identical. -/
theorem HLambda_eq_of_extZero38 (Λ Γ : Finset ℤ) (w : Λ → ℂ) (v : Γ → ℂ)
    (h : extZero38 Λ w = extZero38 Γ v) : HΛ Λ w = HΛ Γ v := by
  unfold HΛ BirkhoffTop38.finiteGapField38
  rw [h]

/-- Zero extension commutes with a coordinate line. The coordinate on the full
integer sequence is the same integer label, including the zero mode. -/
theorem extZero_coordinate_line38 (Λ : Finset ℤ) (w : Λ → ℂ) (i : Λ)
    (c : ℂ) (s : ℝ) :
    extZero38 Λ (fun j => w j + (s : ℂ) * (Pi.single i c : Λ → ℂ) j) =
      fun n => extZero38 Λ w n + (s : ℂ) * (Pi.single i.1 c : ℤ → ℂ) n := by
  classical
  funext n
  by_cases hn : n ∈ Λ
  · rw [extZero38_apply_of_mem _ hn, extZero38_apply_of_mem _ hn]
    by_cases hi : (⟨n, hn⟩ : Λ) = i
    · have he : n = i.1 := congrArg Subtype.val hi
      simp only [he, Pi.single_eq_same]
    · have he : n ≠ i.1 := fun h => hi (Subtype.ext h)
      simp only [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne he]
  · rw [extZero38_apply_of_not_mem _ hn, extZero38_apply_of_not_mem _ hn]
    have he : n ≠ i.1 := fun h => hn (h ▸ i.2)
    simp only [Pi.single_eq_of_ne he, mul_zero, add_zero]

/-- At a common coordinate the real coordinate differentials agree across
finite planes with identical zero extensions. -/
theorem HLambda_coordinate_fderiv_eq38 (Λ Γ : Finset ℤ) (w : Λ → ℂ) (v : Γ → ℂ)
    (h : extZero38 Λ w = extZero38 Γ v) (i : Λ) (j : Γ) (hij : i.1 = j.1)
    (c : ℂ) :
    fderiv ℝ (HΛ Λ) w (Pi.single i c) =
      fderiv ℝ (HΛ Γ) v (Pi.single j c) := by
  have hl := finitePlane_line_hasDerivAt38 Λ w (Pi.single i c) 0
  have hr := finitePlane_line_hasDerivAt38 Γ v (Pi.single j c) 0
  have hL : HasFDerivAt (HΛ Λ) (fderiv ℝ (HΛ Λ) w)
      (fun k => w k + (0 : ℂ) * (Pi.single i c : Λ → ℂ) k) := by
    simpa only [zero_mul, add_zero] using
      (analytic_HLambda38 Λ w (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hR : HasFDerivAt (HΛ Γ) (fderiv ℝ (HΛ Γ) v)
      (fun k => v k + (0 : ℂ) * (Pi.single j c : Γ → ℂ) k) := by
    simpa only [zero_mul, add_zero] using
      (analytic_HLambda38 Γ v (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have he : (fun s : ℝ => HΛ Λ (fun k => w k + (s : ℂ) * (Pi.single i c : Λ → ℂ) k)) =
      fun s : ℝ => HΛ Γ (fun k => v k + (s : ℂ) * (Pi.single j c : Γ → ℂ) k) := by
    funext s
    apply HLambda_eq_of_extZero38
    rw [extZero_coordinate_line38, extZero_coordinate_line38, h, hij]
  have hd := hL.comp_hasDerivAt 0 hl
  change HasDerivAt (fun s : ℝ => HΛ Λ
    (fun k => w k + (s : ℂ) * (Pi.single i c : Λ → ℂ) k))
    (fderiv ℝ (HΛ Λ) w (Pi.single i c)) 0 at hd
  rw [he] at hd
  have hdR := hR.comp_hasDerivAt 0 hr
  exact hd.unique hdR

/-- Zero padding preserves the Hamiltonian vector field at every common
coordinate. The two finite sets need not coincide or be nested. -/
theorem YLambda_eq_of_extZero38 (Λ Γ : Finset ℤ) (w : Λ → ℂ) (v : Γ → ℂ)
    (h : extZero38 Λ w = extZero38 Γ v) (i : Λ) (j : Γ) (hij : i.1 = j.1) :
    YΛ Λ w i = YΛ Γ v j := by
  unfold YΛ
  rw [HLambda_coordinate_fderiv_eq38 Λ Γ w v h i j hij 1,
    HLambda_coordinate_fderiv_eq38 Λ Γ w v h i j hij Complex.I]

end LiebLiniger.FixedPeriod.EXT
