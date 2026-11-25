                                                                                                                                                                                                                                                         
                                                                                
import Mathlib
import NlsGge.Hierarchy.ALTransferDefs38

                                                                                                 
                                                                
                                                                                                       
                                                                                                
                                                                                         
                                                                              
                                                                       
                                                                                             

set_option autoImplicit false

open NlsGge.AblowitzLadik
open scoped Matrix

namespace NlsGge.ThirdConsultation.AL

noncomputable def cmvRho38 (a : ℂ) : ℝ := Real.sqrt (1 - ‖a‖ ^ 2)

noncomputable def cmvTheta38 (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star a, (cmvRho38 a : ℂ); (cmvRho38 a : ℂ), -a]

noncomputable def cmvTwistedTheta38 (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star a, (cmvRho38 a : ℂ) * b⁻¹;
     (cmvRho38 a : ℂ) * b, -a]

noncomputable def cmvPairEmbed38 {p : ℕ} (a c : ZMod p)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (ZMod p) (ZMod p) ℂ :=
  fun i j =>
    if i = a then
      if j = a then B 0 0 else if j = c then B 0 1 else 0
    else if i = c then
      if j = a then B 1 0 else if j = c then B 1 1 else 0
    else 0

noncomputable def cmvEven38 {p : ℕ} (β : ZMod p → ℂ) : Matrix (ZMod p) (ZMod p) ℂ :=
  ∑ r : Fin (p / 2),
    cmvPairEmbed38 ((2 * r.val : ℕ) : ZMod p)
      ((2 * r.val + 1 : ℕ) : ZMod p)
      (cmvTheta38 (β ((2 * r.val : ℕ) : ZMod p)))

noncomputable def cmvOdd38 {p : ℕ} (β : ZMod p → ℂ) (b : ℂ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  ∑ r : Fin (p / 2),
    cmvPairEmbed38 ((2 * r.val + 1 : ℕ) : ZMod p)
      ((2 * r.val + 2 : ℕ) : ZMod p)
      (cmvTwistedTheta38 (β ((2 * r.val + 1 : ℕ) : ZMod p))
        (if 2 * r.val + 2 = p then b else 1))

noncomputable def floquetCMV38 {p : ℕ} [NeZero p] (β : ZMod p → ℂ) (b : ℂ) :
    Matrix (ZMod p) (ZMod p) ℂ :=
  cmvEven38 β * cmvOdd38 β b

theorem cmv_rho_sq (a : ℂ) (ha : ‖a‖ ≤ 1) :
    (cmvRho38 a : ℂ) * (cmvRho38 a : ℂ) = 1 - a * starRingEnd ℂ a := by
  have h1 : cmvRho38 a * cmvRho38 a = 1 - ‖a‖ ^ 2 := by
    unfold cmvRho38
    exact Real.mul_self_sqrt (by nlinarith [norm_nonneg a])
  have h2 : a * starRingEnd ℂ a = ((‖a‖ : ℂ)) ^ 2 := Complex.mul_conj' a
  have h3 : ((cmvRho38 a * cmvRho38 a : ℝ) : ℂ) = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by rw [h1]
  push_cast at h3
  rw [h2]
  linear_combination h3

theorem cmv_theta_mem (a : ℂ) (ha : ‖a‖ ≤ 1) :
    cmvTheta38 a ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hρ := cmv_rho_sq a ha
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmvTheta38, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def] <;>
    first | linear_combination hρ | ring

theorem cmv_twist_mem (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ = 1) :
    cmvTwistedTheta38 a b ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hρ := cmv_rho_sq a ha
  have hbb : b * starRingEnd ℂ b = 1 := by
    rw [Complex.mul_conj']
    simp [hb]
  have hbinv : b⁻¹ = starRingEnd ℂ b := inv_eq_of_mul_eq_one_right hbb
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmvTwistedTheta38, hbinv, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def] <;>
    first | linear_combination hρ | linear_combination hρ + (cmvRho38 a : ℂ) ^ 2 * hbb | ring


/-! ### Block sums over `ZMod p` -/

theorem P_row_zero {p : ℕ} {a c : ZMod p} {B : Matrix (Fin 2) (Fin 2) ℂ} {i j : ZMod p}
    (hi1 : i ≠ a) (hi2 : i ≠ c) : cmvPairEmbed38 a c B i j = 0 := by
  simp [cmvPairEmbed38, hi1, hi2]

theorem P_col_zero {p : ℕ} {a c : ZMod p} {B : Matrix (Fin 2) (Fin 2) ℂ} {i j : ZMod p}
    (hj1 : j ≠ a) (hj2 : j ≠ c) : cmvPairEmbed38 a c B i j = 0 := by
  simp [cmvPairEmbed38, hj1, hj2]

theorem P_mul_disj {p : ℕ} [NeZero p] {a c a' c' : ZMod p} {B B' : Matrix (Fin 2) (Fin 2) ℂ}
    (hdisj : ∀ x : ZMod p, (x = a ∨ x = c) → x ≠ a' ∧ x ≠ c') :
    (cmvPairEmbed38 a c B)ᴴ * cmvPairEmbed38 a' c' B' = 0 := by
  ext i k
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro j _
  rw [Matrix.conjTranspose_apply]
  by_cases hj : j = a ∨ j = c
  · obtain ⟨h1, h2⟩ := hdisj j hj
    rw [P_row_zero h1 h2, mul_zero]
  · push Not at hj
    rw [P_row_zero hj.1 hj.2, star_zero, zero_mul]

theorem P_mul_same {p : ℕ} [NeZero p] {a c : ZMod p} (hac : a ≠ c)
    (B B' : Matrix (Fin 2) (Fin 2) ℂ) :
    (cmvPairEmbed38 a c B)ᴴ * cmvPairEmbed38 a c B' = cmvPairEmbed38 a c (Bᴴ * B') := by
  ext i k
  have hsub : ∑ j : ZMod p, (cmvPairEmbed38 a c B)ᴴ i j * cmvPairEmbed38 a c B' j k
      = ∑ j ∈ ({a, c} : Finset (ZMod p)), (cmvPairEmbed38 a c B)ᴴ i j * cmvPairEmbed38 a c B' j k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    rw [Matrix.conjTranspose_apply, P_row_zero hx.1 hx.2, star_zero, zero_mul]
  rw [Matrix.mul_apply, hsub, Finset.sum_pair hac]
  rcases eq_or_ne i a with hia | hia <;> rcases eq_or_ne i c with hic | hic <;>
    rcases eq_or_ne k a with hka | hka <;> rcases eq_or_ne k c with hkc | hkc <;>
    simp [cmvPairEmbed38, hac, hac.symm, hia, hic, hka, hkc, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring

theorem P_one_entry {p : ℕ} {a c : ZMod p} (hac : a ≠ c) (i k : ZMod p) (hi : i = a ∨ i = c) :
    cmvPairEmbed38 a c (1 : Matrix (Fin 2) (Fin 2) ℂ) i k
      = (1 : Matrix (ZMod p) (ZMod p) ℂ) i k := by
  rw [Matrix.one_apply]
  rcases hi with hi | hi <;> rw [hi]
  · by_cases hka : k = a
    · rw [hka]; simp [cmvPairEmbed38]
    · have hka' : a ≠ k := Ne.symm hka
      by_cases hkc : k = c
      · rw [hkc]; simp [cmvPairEmbed38, hac, hac.symm]
      · simp [cmvPairEmbed38, hka, hka', hkc]
  · by_cases hkc : k = c
    · rw [hkc]; simp [cmvPairEmbed38, hac.symm]
    · have hkc' : c ≠ k := Ne.symm hkc
      by_cases hka : k = a
      · rw [hka]; simp [cmvPairEmbed38, hac.symm]
      · simp [cmvPairEmbed38, hka, hkc', hkc]

theorem P_one_sum {p : ℕ} [NeZero p] {m : ℕ} (f g : Fin m → ZMod p) (hfg : ∀ r, f r ≠ g r)
    (hcov : ∀ i : ZMod p, ∃! r : Fin m, i = f r ∨ i = g r) :
    ∑ r : Fin m, cmvPairEmbed38 (f r) (g r) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i k
  obtain ⟨r0, hr0, huniq⟩ := hcov i
  rw [Matrix.sum_apply, Finset.sum_eq_single r0]
  · exact P_one_entry (hfg r0) i k hr0
  · intro r _ hr
    have hn : ¬ (i = f r ∨ i = g r) := fun h => hr (huniq r h)
    push Not at hn
    rw [P_row_zero hn.1 hn.2]
  · intro h
    exact absurd (Finset.mem_univ r0) h

theorem cmv_block_mem {p : ℕ} [NeZero p] {m : ℕ} (f g : Fin m → ZMod p)
    (B : Fin m → Matrix (Fin 2) (Fin 2) ℂ)
    (hfg : ∀ r, f r ≠ g r) (hcov : ∀ i : ZMod p, ∃! r : Fin m, i = f r ∨ i = g r)
    (hB : ∀ r, B r ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    (∑ r : Fin m, cmvPairEmbed38 (f r) (g r) (B r)) ∈ Matrix.unitaryGroup (ZMod p) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hdisj : ∀ r s : Fin m, r ≠ s → ∀ x : ZMod p, (x = f r ∨ x = g r) →
      x ≠ f s ∧ x ≠ g s := by
    intro r s hrs x hx
    constructor
    · intro h
      exact hrs ((hcov x).unique hx (Or.inl h))
    · intro h
      exact hrs ((hcov x).unique hx (Or.inr h))
  have key : ∀ r : Fin m, ∑ s : Fin m,
      (cmvPairEmbed38 (f r) (g r) (B r))ᴴ * cmvPairEmbed38 (f s) (g s) (B s)
        = cmvPairEmbed38 (f r) (g r) (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    intro r
    rw [Finset.sum_eq_single r]
    · rw [P_mul_same (hfg r), ← Matrix.star_eq_conjTranspose]
      have hBr : star (B r) * B r = 1 := (Matrix.mem_unitaryGroup_iff'.1 (hB r))
      rw [hBr]
    · intro s _ hs
      exact P_mul_disj (fun x hx => hdisj r s (Ne.symm hs) x hx)
    · intro h; exact absurd (Finset.mem_univ r) h
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun r _ => key r)]
  exact P_one_sum f g hfg hcov


/-! ### Cover conditions for the even and odd pairs -/

theorem cmv_even_cover {p : ℕ} [NeZero p] (hp : p % 2 = 0) (i : ZMod p) :
    ∃! r : Fin (p / 2), i = ((2 * r.val : ℕ) : ZMod p) ∨ i = ((2 * r.val + 1 : ℕ) : ZMod p) := by
  have hv : i.val < p := ZMod.val_lt i
  have hiff : ∀ n : ℕ, n < p → (i = (n : ZMod p) ↔ i.val = n) := by
    intro n hn
    constructor
    · intro h
      rw [h, ZMod.val_natCast_of_lt hn]
    · intro h
      apply ZMod.val_injective p
      rw [h, ZMod.val_natCast_of_lt hn]
  refine ⟨⟨i.val / 2, by omega⟩, ?_, ?_⟩
  · show i = ((2 * (i.val / 2) : ℕ) : ZMod p) ∨ i = ((2 * (i.val / 2) + 1 : ℕ) : ZMod p)
    have hsplit : i.val = 2 * (i.val / 2) ∨ i.val = 2 * (i.val / 2) + 1 := by omega
    rcases hsplit with h | h
    · left
      rw [hiff (2 * (i.val / 2)) (by omega)]
      exact h
    · right
      rw [hiff (2 * (i.val / 2) + 1) (by omega)]
      exact h
  · intro r hr
    have hr' := r.isLt
    rcases hr with h | h
    · rw [hiff (2 * r.val) (by omega)] at h
      apply Fin.ext
      show r.val = i.val / 2
      omega
    · rw [hiff (2 * r.val + 1) (by omega)] at h
      apply Fin.ext
      show r.val = i.val / 2
      omega

theorem cmv_odd_cover {p : ℕ} [NeZero p] (hp : p % 2 = 0) (i : ZMod p) :
    ∃! r : Fin (p / 2), i = ((2 * r.val + 1 : ℕ) : ZMod p) ∨ i = ((2 * r.val + 2 : ℕ) : ZMod p) := by
  obtain ⟨r, hr, huniq⟩ := cmv_even_cover hp (i - 1)
  have e : i = (i - 1) + 1 := by ring
  refine ⟨r, ?_, ?_⟩
  · rcases hr with h | h
    · left
      rw [e, h]
      push_cast <;> ring
    · right
      rw [e, h]
      push_cast <;> ring
  · intro s hs
    apply huniq
    rcases hs with h | h
    · left
      rw [h]
      push_cast <;> ring
    · right
      rw [h]
      push_cast <;> ring

/-! ### Unitarity of the even, odd and Floquet blocks -/

theorem cmv_even_mem {p : ℕ} [NeZero p] (hp : p % 2 = 0) (β : ZMod p → ℂ)
    (hβ : IsALField38 β) : cmvEven38 β ∈ Matrix.unitaryGroup (ZMod p) ℂ := by
  unfold cmvEven38
  refine cmv_block_mem (fun r : Fin (p / 2) => ((2 * r.val : ℕ) : ZMod p))
    (fun r : Fin (p / 2) => ((2 * r.val + 1 : ℕ) : ZMod p))
    (fun r : Fin (p / 2) => cmvTheta38 (β ((2 * r.val : ℕ) : ZMod p))) ?_ (cmv_even_cover hp) ?_
  · intro r
    intro h
    have hr := r.isLt
    have h1 := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (n := p) (a := 2 * r.val) (by omega),
      ZMod.val_natCast_of_lt (n := p) (a := 2 * r.val + 1) (by omega)] at h1
    omega
  · intro r
    exact cmv_theta_mem _ (hβ _).le

theorem cmv_odd_mem {p : ℕ} [NeZero p] (hp : p % 2 = 0) (β : ZMod p → ℂ)
    (hβ : IsALField38 β) (b : ℂ) (hb : ‖b‖ = 1) :
    cmvOdd38 β b ∈ Matrix.unitaryGroup (ZMod p) ℂ := by
  unfold cmvOdd38
  refine cmv_block_mem (fun r : Fin (p / 2) => ((2 * r.val + 1 : ℕ) : ZMod p))
    (fun r : Fin (p / 2) => ((2 * r.val + 2 : ℕ) : ZMod p))
    (fun r : Fin (p / 2) => cmvTwistedTheta38 (β ((2 * r.val + 1 : ℕ) : ZMod p))
        (if 2 * r.val + 2 = p then b else 1)) ?_ (cmv_odd_cover hp) ?_
  · intro r
    intro h
    have hr := r.isLt
    have h1 := congrArg ZMod.val h
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (show 2 * r.val + 1 < p by omega)] at h1
    by_cases h2 : 2 * r.val + 2 < p
    · rw [Nat.mod_eq_of_lt h2] at h1
      omega
    · rw [show 2 * r.val + 2 = p by omega, Nat.mod_self] at h1
      omega
  · intro r
    apply cmv_twist_mem
    · exact (hβ _).le
    · split_ifs
      · exact hb
      · simp

theorem cmv_floquet_mem {p : ℕ} [NeZero p] (hp : p % 2 = 0) (β : ZMod p → ℂ)
    (hβ : IsALField38 β) (b : ℂ) (hb : ‖b‖ = 1) :
    floquetCMV38 β b ∈ Matrix.unitaryGroup (ZMod p) ℂ := by
  unfold floquetCMV38
  exact Submonoid.mul_mem _ (cmv_even_mem hp β hβ) (cmv_odd_mem hp β hβ b hb)

/-! ### Norm preservation of unitary matrices on `EuclideanSpace` -/

theorem cmv_norm_pres {p : ℕ} [NeZero p] (M : Matrix (ZMod p) (ZMod p) ℂ)
    (hM : Mᴴ * M = 1) (v : EuclideanSpace ℂ (ZMod p)) :
    ‖Matrix.toEuclideanLin M v‖ = ‖v‖ := by
  have hcomp : ∀ X Y : Matrix (ZMod p) (ZMod p) ℂ,
      Matrix.toEuclideanLin (X * Y) = (Matrix.toEuclideanLin X).comp (Matrix.toEuclideanLin Y) := by
    intro X Y
    simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.toLin_mul (EuclideanSpace.basisFun (ZMod p) ℂ).toBasis (EuclideanSpace.basisFun (ZMod p) ℂ).toBasis (EuclideanSpace.basisFun (ZMod p) ℂ).toBasis X Y
  have hone : Matrix.toEuclideanLin (1 : Matrix (ZMod p) (ZMod p) ℂ) = LinearMap.id := by
    simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.toLin_one (EuclideanSpace.basisFun (ZMod p) ℂ).toBasis
  have hA : (Matrix.toEuclideanLin Mᴴ).comp (Matrix.toEuclideanLin M) = LinearMap.id := by
    rw [← hcomp, hM, hone]
  have hadj := Matrix.toEuclideanLin_conjTranspose_eq_adjoint M
  have hAdj : LinearMap.adjoint (Matrix.toEuclideanLin M) (Matrix.toEuclideanLin M v) = v := by
    have h := congrArg (fun f : EuclideanSpace ℂ (ZMod p) →ₗ[ℂ] EuclideanSpace ℂ (ZMod p) => f v) hA
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
    rw [hadj] at h
    exact h
  have h1 := LinearMap.adjoint_inner_left (Matrix.toEuclideanLin M) v (Matrix.toEuclideanLin M v)
  rw [hAdj] at h1
  have key : (inner ℂ (Matrix.toEuclideanLin M v) (Matrix.toEuclideanLin M v) : ℂ)
      = inner ℂ v v := h1.symm
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at key
  have h3 : ‖Matrix.toEuclideanLin M v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast key
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h3

/-! ### The theorem `al006` -/

theorem al006 (p : ℕ) [NeZero p] (hp : Even p)
    (β : ZMod p → ℂ) (hβ : IsALField38 β)
    (b : ℂ) (hb : ‖b‖ = 1) :
  (∀ j : ZMod p, cmvTheta38 (β j) ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  cmvEven38 β ∈ Matrix.unitaryGroup (ZMod p) ℂ ∧
  cmvOdd38 β b ∈ Matrix.unitaryGroup (ZMod p) ℂ ∧
  floquetCMV38 β b ∈ Matrix.unitaryGroup (ZMod p) ℂ ∧
  ∀ v : EuclideanSpace ℂ (ZMod p),
    ‖Matrix.toEuclideanLin (floquetCMV38 β b) v‖ = ‖v‖ := by
  have hp2 : p % 2 = 0 := Nat.even_iff.1 hp
  have hF := cmv_floquet_mem hp2 β hβ b hb
  exact ⟨fun j => cmv_theta_mem _ (hβ j).le, cmv_even_mem hp2 β hβ, cmv_odd_mem hp2 β hβ b hb, hF,
    fun v => cmv_norm_pres _ (Matrix.mem_unitaryGroup_iff'.1 hF) v⟩

end NlsGge.ThirdConsultation.AL
