import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualComplexZsDysonVolterraWithinODEV3
import NlsGge.Spectral.ActualComplexZsDysonRepresentativeInvarianceV1
import NlsGge.Spectral.ActualPhysicalUnitCharacteristicEquation33V1
import NlsGge.Spectral.ComplexQuadraticInsideUnitRootUnique36V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # S2 (campaign 38): Floquet link on the imaginary axis through a periodic Riccati solution

Dictionary (fixed once): for `ψ' = zsCoefficientComplex U z ψ` (v2's `L_u`), `Γ := I·ψ₂/ψ₁`
satisfies `Γ' = 2izΓ + ū - uΓ²` and `ψ₁'/ψ₁ = -iz + uΓ`. At `z = iη`:
`Γ' = -2ηΓ + ū - uΓ²`, matching the hierarchy's formal `riccatiGamma38_eq` (`X ↔ 1/(2iz)`). -/

/-- A vector solution of the ZS system on `[0,2]` is the Dyson fundamental matrix applied to its
initial value (continuous potential). -/
theorem actualComplexZsDysonTsum_mulVec_eq_of_solution_E02_38 (U : ℝ → ℂ) (z : ℂ)
    (hU : ContinuousOn U (Set.Icc (0:ℝ) 2)) (ψ : ℝ → Fin 2 → ℂ)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) 2,
      HasDerivWithinAt ψ (zsCoefficientComplex U z t *ᵥ ψ t) (Set.Icc (0:ℝ) 2) t) :
    ∀ t ∈ Set.Icc (0:ℝ) 2, actualComplexZsDysonTsum U z t *ᵥ ψ 0 = ψ t := by
  obtain ⟨G, hG0, hGd, hGdet, hGeq⟩ := exists_normalized_actualComplexZsDysonFundamental_Icc U z hU
  -- f t := adj(G t) ψ t, written entrywise
  let f : ℝ → Fin 2 → ℂ := fun t =>
    ![G t 1 1 * ψ t 0 - G t 0 1 * ψ t 1, -(G t 1 0) * ψ t 0 + G t 0 0 * ψ t 1]
  have hentry : ∀ t ∈ Set.Icc (0:ℝ) 2, ∀ i j : Fin 2,
      HasDerivWithinAt (fun s => G s i j) ((zsCoefficientComplex U z t * G t) i j)
        (Set.Icc (0:ℝ) 2) t := by
    intro t ht i j
    have h1 := (hasDerivWithinAt_pi.1 (hGd t ht)) i
    exact (hasDerivWithinAt_pi.1 h1) j
  have hψe : ∀ t ∈ Set.Icc (0:ℝ) 2, ∀ i : Fin 2,
      HasDerivWithinAt (fun s => ψ s i) ((zsCoefficientComplex U z t *ᵥ ψ t) i)
        (Set.Icc (0:ℝ) 2) t := fun t ht i => (hasDerivWithinAt_pi.1 (hψ t ht)) i
  have hfd : ∀ t ∈ Set.Icc (0:ℝ) 2, HasDerivWithinAt f 0 (Set.Icc (0:ℝ) 2) t := by
    intro t ht
    apply hasDerivWithinAt_pi.2
    intro i
    fin_cases i
    · have h := ((hentry t ht 1 1).mul (hψe t ht 0)).sub ((hentry t ht 0 1).mul (hψe t ht 1))
      refine HasDerivWithinAt.congr_deriv (f := fun s => f s 0) h ?_
      simp [zsCoefficientComplex, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    · have h := ((hentry t ht 1 0).neg.mul (hψe t ht 0)).add ((hentry t ht 0 0).mul (hψe t ht 1))
      refine HasDerivWithinAt.congr_deriv (f := fun s => f s 1) h ?_
      simp [zsCoefficientComplex, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
  have hconst : ∀ t ∈ Set.Icc (0:ℝ) 2, f t = f 0 := by
    intro t ht
    have hcont : ContinuousOn f (Set.Icc (0:ℝ) 2) := fun s hs => (hfd s hs).continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun s hs => (hfd s (Set.Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs)) t ht
  intro t ht
  have hf := hconst t ht
  have hG0' : f 0 = ψ 0 := by
    ext i; fin_cases i <;> simp [f, hG0, Matrix.one_apply]
  rw [hG0'] at hf
  have hGt : G t = actualComplexZsDysonTsum U z t := hGeq ht
  rw [← hGt]
  have hdet := hGdet t ht
  rw [Matrix.det_fin_two] at hdet
  ext i
  fin_cases i
  · have h0 := congrFun hf 0
    have h1 := congrFun hf 1
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [← h0, ← h1]
    linear_combination (ψ t 0) * hdet
  · have h0 := congrFun hf 0
    have h1 := congrFun hf 1
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [← h0, ← h1]
    linear_combination (ψ t 1) * hdet


/-- S2: on the imaginary axis the concrete quasimomentum is given by a periodic Riccati solution:
`k(iη) = iη + i ∫₀¹ U Γ`, where `U` is a continuous 1-periodic representative of `u` and
`Γ' = -2ηΓ + Ū - UΓ²` is periodic. The two smallness hypotheses only fix the logarithm integer. -/
theorem actualQuasimomentum_imaginaryAxis_riccati_E02_38 (u : PhysicalL2) (U : ℝ → ℂ)
    (hUc : Continuous U)
    (hU : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 2)] U)
    (η : ℝ) (hη : 1 < η) (Γ : ℝ → ℂ) (hΓc : Continuous Γ) (hΓ1 : Γ 1 = Γ 0)
    (hΓ : ∀ x, HasDerivAt Γ (-2*η*Γ x + star (U x) - U x * Γ x ^ 2) x)
    (hsmall : ‖∫ x in (0:ℝ)..1, U x * Γ x‖ < 1)
    (hk : ‖actualQuasimomentumE02_38 u (Complex.I*η) - Complex.I*η‖ < 1) :
    actualQuasimomentumE02_38 u (Complex.I*η) =
      Complex.I*η + Complex.I * ∫ x in (0:ℝ)..1, U x * Γ x := by
  set z : ℂ := Complex.I * η with hz
  set J : ℂ := ∫ x in (0:ℝ)..1, U x * Γ x with hJ
  have hzim : 0 < z.im := by simp [z]; linarith
  -- the Floquet solution
  let g : ℝ → ℂ := fun x => (η:ℂ) + U x * Γ x
  have hgc : Continuous g := continuous_const.add (hUc.mul hΓc)
  let Φ : ℝ → ℂ := fun x => ∫ s in (0:ℝ)..x, g s
  have hΦ : ∀ x, HasDerivAt Φ (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      hgc.aestronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  let ψ : ℝ → Fin 2 → ℂ := fun x => ![Complex.exp (Φ x), -Complex.I * Γ x * Complex.exp (Φ x)]
  have hψd : ∀ x, HasDerivAt ψ (zsCoefficientComplex U z x *ᵥ ψ x) x := by
    intro x
    have h1 : HasDerivAt (fun y => Complex.exp (Φ y)) (Complex.exp (Φ x) * g x) x :=
      (hΦ x).cexp
    have h2 : HasDerivAt (fun y => -Complex.I * Γ y * Complex.exp (Φ y))
        (-Complex.I * (-2*η*Γ x + star (U x) - U x * Γ x ^ 2) * Complex.exp (Φ x) +
          -Complex.I * Γ x * (Complex.exp (Φ x) * g x)) x :=
      ((hΓ x).const_mul (-Complex.I)).mul h1
    apply hasDerivAt_pi.2
    intro i
    fin_cases i
    · refine HasDerivAt.congr_deriv (f := fun y => ψ y 0) h1 ?_
      simp [ψ, zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two, g, z,
        Matrix.vecTail]
      ring_nf
      linear_combination (Complex.exp (Φ x) * η + Complex.exp (Φ x) * U x * Γ x) * Complex.I_sq
    · refine HasDerivAt.congr_deriv (f := fun y => ψ y 1) h2 ?_
      simp [ψ, zsCoefficientComplex, Matrix.mulVec, dotProduct, Fin.sum_univ_two, g, z,
        Matrix.vecTail]
      ring_nf
      linear_combination (Complex.I * η * Γ x * Complex.exp (Φ x)) * Complex.I_sq
  have hmono := actualComplexZsDysonTsum_mulVec_eq_of_solution_E02_38 U z hUc.continuousOn ψ
    (fun t _ => (hψd t).hasDerivWithinAt) 1 (by norm_num)
  have hD := actualComplexZsDysonTsum_eq_of_ae_eq _ U z hU 1 (by norm_num)
  set w : ℂ := Complex.exp (Φ 1)
  have hΦ0 : Φ 0 = 0 := by simp [Φ]
  have hψ0 : ψ 0 = ![1, -Complex.I * Γ 0] := by
    ext i; fin_cases i <;> simp [ψ, hΦ0]
  have hψ1 : ψ 1 = w • ψ 0 := by
    rw [hψ0]; ext i; fin_cases i <;> simp [ψ, w, hΓ1] ; ring
  have heig : (actualComplexZsDysonTsum
      (fun x => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (x : SpectralCircle)) z 1).mulVec
      (ψ 0) = w • ψ 0 := by
    rw [hD, hmono, hψ1]
  have hne : ψ 0 ≠ 0 := by
    rw [hψ0]; intro h; have := congrFun h 0; simp at this
  have hroot := (actualPhysicalUnit_eigenmultiplier_iff_quadratic33 u z w).mp ⟨ψ 0, hne, heig⟩
  -- Φ 1 = η + J
  have hΦ1 : Φ 1 = (η:ℂ) + J := by
    simp only [Φ, g]
    rw [intervalIntegral.integral_add (f := fun _ => (η:ℂ)) (g := fun x => U x * Γ x)
      intervalIntegrable_const ((hUc.mul hΓc).intervalIntegrable _ _)]
    simp [hJ]
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hwnorm : 1 < ‖w‖ := by
    rw [Complex.norm_exp, hΦ1, Complex.add_re, Complex.ofReal_re]
    have := Complex.abs_re_le_norm J
    apply Real.one_lt_exp_iff.mpr
    linarith [(abs_le.mp (this.trans hsmall.le)).1]
  -- the inside root
  have hinv : w⁻¹ ^ 2 - 2*actualPhysicalUnitHalfTrace32 u z * w⁻¹ + 1 = 0 := by
    field_simp
    linear_combination hroot
  have hinvn : ‖w⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hwnorm
  have hkb := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  set k := actualQuasimomentumE02_38 u z
  have hkroot : Complex.exp (Complex.I*k)^2 - 2*actualPhysicalUnitHalfTrace32 u z *
      Complex.exp (Complex.I*k) + 1 = 0 := by
    rw [← hkb.2.1 z hzim, Complex.cos]
    have he : Complex.exp (Complex.I*k) * Complex.exp (-(Complex.I*k)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    rw [show k*Complex.I = Complex.I*k by ring, show -k*Complex.I = -(Complex.I*k) by ring]
    linear_combination -he
  have hknorm : ‖Complex.exp (Complex.I*k)‖ < 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (hkb.2.2.1 z hzim))
  have heq : Complex.exp (Complex.I*k) = w⁻¹ :=
    complexQuadratic_insideUnitRoot_unique36V1 _ _ _ hkroot hinv hknorm hinvn
  rw [← Complex.exp_neg] at heq
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  -- I k = -(η + J) + m 2πI, so k = Iη + I J + 2π m
  have hkm : k = z + Complex.I * J + (m:ℂ) * (2*Real.pi) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [hΦ1] at hm
    have : Complex.I * (Complex.I * k) = Complex.I * (-((η:ℂ) + J) + (m:ℂ) * (2*Real.pi*Complex.I)) := by
      rw [hm]
    simp only [z]
    linear_combination (-1:ℂ) * this + (k - (m:ℂ)*(2*Real.pi)) * hI
  have hm0 : m = 0 := by
    by_contra hne
    have h1 : ‖(m:ℂ) * (2*Real.pi)‖ ≤ ‖k - z‖ + ‖Complex.I * J‖ := by
      have : (m:ℂ) * (2*Real.pi) = (k - z) - Complex.I * J := by rw [hkm]; ring
      rw [this]; exact norm_sub_le _ _
    have h2pi : ‖(2*(Real.pi:ℂ))‖ = 2*Real.pi := by
      rw [show (2*(Real.pi:ℂ)) = ((2*Real.pi:ℝ):ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.two_pi_pos]
    have hmn : ‖(m:ℂ) * (2*(Real.pi:ℂ))‖ = |(m:ℝ)| * (2*Real.pi) := by
      rw [norm_mul, Complex.norm_intCast, h2pi]
    have hIJ : ‖Complex.I * J‖ = ‖J‖ := by simp
    rw [hmn, hIJ] at h1
    have h2 : (1:ℝ) ≤ |(m:ℝ)| := by
      have : (1:ℤ) ≤ |m| := Int.one_le_abs hne
      exact_mod_cast this
    nlinarith [Real.pi_gt_three, hk, hsmall]
  rw [hkm, hm0]; simp

end NlsGge.SpectralFoundations
end
