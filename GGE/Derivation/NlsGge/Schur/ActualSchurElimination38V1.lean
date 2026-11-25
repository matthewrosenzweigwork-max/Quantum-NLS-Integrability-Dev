import NlsGge.Schur.ActualSchurOffDiagonalRemainder38V1
import NlsGge.Schur.ActualSchurCenterContraction38V1
import NlsGge.Schur.FreeCoordinateDomainInverse
import NlsGge.Schur.ResonantParityPairBasisAction

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-! ### Elementary coordinate identities for `P`, `Q`, `D` on `SectorSquare n` -/

lemma resonantSquare_idem38 (n : ℤ) (x : SectorSquare n) :
    resonantSquare n (resonantSquare n x) = resonantSquare n x := by
  apply lp.ext; funext i; by_cases h : i.2 = resonantIndex n <;> simp [h]

lemma complementarySquare_resonantSquare38 (n : ℤ) (x : SectorSquare n) :
    complementarySquare n (resonantSquare n x) = 0 := by
  apply lp.ext; funext i; by_cases h : i.2 = resonantIndex n <;> simp [h]

lemma resonantSquare_complementarySquare38 (n : ℤ) (x : SectorSquare n) :
    resonantSquare n (complementarySquare n x) = 0 := by
  apply lp.ext; funext i; by_cases h : i.2 = resonantIndex n <;> simp [h]

lemma resonantSquare_add_complementarySquare38 (n : ℤ) (x : SectorSquare n) :
    resonantSquare n x + complementarySquare n x = x := by
  apply lp.ext; funext i; by_cases h : i.2 = resonantIndex n <;> simp [h]

lemma complementarySquare_idem38 (n : ℤ) (x : SectorSquare n) :
    complementarySquare n (complementarySquare n x) = complementarySquare n x := by
  apply lp.ext; funext i; by_cases h : i.2 = resonantIndex n <;> simp [h]

lemma freeResolventSquare_resonant38 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : SectorSquare n) :
    resonantSquare n (freeResolventSquare n z hz x) = 0 := by
  apply lp.ext; funext i; by_cases h : i.2 = resonantIndex n <;> simp [h]

lemma freeResolventSquare_comp_resonant38 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : SectorSquare n) :
    freeResolventSquare n z hz (resonantSquare n x) = 0 := by
  apply lp.ext; funext i; by_cases h : i.2 = resonantIndex n <;> simp [h]

lemma complementarySquare_freeResolventSquare38 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : SectorSquare n) :
    complementarySquare n (freeResolventSquare n z hz x) = freeResolventSquare n z hz x := by
  have h := freeResolventSquare_resonant38 n z hz x
  have h2 := resonantSquare_add_complementarySquare38 n (freeResolventSquare n z hz x)
  rw [h, zero_add] at h2
  exact h2

lemma freeResolventSquare_complementarySquare38 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (x : SectorSquare n) :
    freeResolventSquare n z hz (complementarySquare n x) = freeResolventSquare n z hz x := by
  have h := freeResolventSquare_comp_resonant38 n z hz x
  have h2 := congrArg (freeResolventSquare n z hz)
    (resonantSquare_add_complementarySquare38 n x)
  rw [map_add, h, zero_add] at h2
  exact h2


/-- Shifted Dirac on `P`-range vectors: `(z - L0) y = (z - nπ) y`. -/
lemma resonantSquare_shifted38 (n : ℤ) (z : ℂ) (x : freeWeightedDomainPointwise n) :
    resonantSquare n (freeShiftedCoordinateDirac n z x) =
      (z - spectralCenter n) • resonantSquare n x.val := by
  apply lp.ext; funext i
  by_cases h : i.2 = resonantIndex n
  · have hv : i.2.val = n := by rw [h]; rfl
    have e : (freeShiftedCoordinateDirac n z x) i = z * x.val i - spectralCenter i.2.val * x.val i :=
      rfl
    rw [resonantSquare_apply, if_pos h, e, hv]
    simp [h, sub_mul]
  · simp [h]

lemma freeWeightedDomain_of_resonant38 (n : ℤ) (y : SectorSquare n)
    (hy : resonantSquare n y = y) : y ∈ freeWeightedDomainPointwise n := by
  change Memℓp (freeWeightedCoordinates n y) 2
  have hyi : ∀ i : Bool × Sector n, i.2 ≠ resonantIndex n → y i = 0 := by
    intro i hi
    have := congrArg (fun f : SectorSquare n => f i) hy
    simpa [hi] using this.symm
  have he : freeWeightedCoordinates n y = spectralCenter n • (y : Bool × Sector n → ℂ) := by
    funext i
    by_cases h : i.2 = resonantIndex n
    · have hv : i.2.val = n := by rw [h]; rfl
      simp [freeWeightedCoordinates, hv]
    · simp [freeWeightedCoordinates, hyi i h]
  rw [he]
  exact (lp.memℓp y).const_smul _

/-- The coordinate Schur effective operator `P Ṽ P + P Ṽ (D S) Ṽ P`. -/
def schurEffectiveSquare38 (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
    (Vt St : SectorSquare n →L[ℂ] SectorSquare n) : SectorSquare n →L[ℂ] SectorSquare n :=
  (resonantSquare n).comp (Vt.comp (resonantSquare n)) +
    (resonantSquare n).comp
      (Vt.comp (((freeResolventSquare n z hz).comp St).comp
        (Vt.comp (resonantSquare n))))

section Core

variable (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n)
  (Vt St : SectorSquare n →L[ℂ] SectorSquare n)

/-- `S = 1 + Q Ṽ D S`. -/
lemma schurCore_hSw38
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (w : SectorSquare n) :
    St w = w + complementarySquare n (Vt (freeResolventSquare n z hz (St w))) := by
  have h := congrArg (fun T : SectorSquare n →L[ℂ] SectorSquare n => T w) hS1
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    one_apply_eq_self] at h
  exact sub_eq_iff_eq_add.mp h

/-- `D S w = D w + D Ṽ (D S w)`. -/
lemma schurCore_hDSw38
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (w : SectorSquare n) :
    freeResolventSquare n z hz (St w) =
      freeResolventSquare n z hz w +
        freeResolventSquare n z hz (Vt (freeResolventSquare n z hz (St w))) := by
  conv_lhs => rw [schurCore_hSw38 n z hz Vt St hS1 w]
  rw [map_add, freeResolventSquare_complementarySquare38]

/-- Injectivity of `1 - D Ṽ` from invertibility of `1 - Q Ṽ D`. -/
lemma schurCore_inj38
    (hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1)
    (d : SectorSquare n) (hd : d = freeResolventSquare n z hz (Vt d)) : d = 0 := by
  set h := complementarySquare n (Vt d) with hh
  have hdh : d = freeResolventSquare n z hz h := by
    rw [hh, freeResolventSquare_complementarySquare38]; exact hd
  have hK : h - complementarySquare n (Vt (freeResolventSquare n z hz h)) = 0 := by
    rw [← hdh]; exact sub_self _
  have h0 : h = 0 := by
    have h1 := congrArg (fun T : SectorSquare n →L[ℂ] SectorSquare n => T h) hS2
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      one_apply_eq_self] at h1
    rw [hK, map_zero] at h1
    exact h1.symm
  rw [hdh, h0, map_zero]


/-- Forward direction of the coordinate Schur elimination. -/
theorem schurCore_forward38
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (hS2 : St.comp ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))) = 1)
    (x : freeWeightedDomainPointwise n) (hx0 : x.val ≠ 0)
    (heq : z • x.val - freeCoordinateDirac n x - Vt x.val = 0) :
    ∃ y : SectorSquare n, y ≠ 0 ∧ resonantSquare n y = y ∧
      (z - spectralCenter n) • y = schurEffectiveSquare38 n z hz Vt St y := by
  have hsh : freeShiftedCoordinateDirac n z x = Vt x.val := by
    have : freeShiftedCoordinateDirac n z x = z • x.val - freeCoordinateDirac n x := rfl
    rw [this]; exact sub_eq_zero.mp heq
  have hq : complementarySquare n x.val = freeResolventSquare n z hz (Vt x.val) := by
    rw [← hsh]
    exact (freeShiftedCoordinateDirac_left_inverse_complement n z hz x).symm
  set y := resonantSquare n x.val with hy
  set q := complementarySquare n x.val with hqdef
  have hxyq : x.val = y + q := (resonantSquare_add_complementarySquare38 n x.val).symm
  have hPy : resonantSquare n y = y := resonantSquare_idem38 n _
  set w := Vt y with hw
  have hq2 : q = freeResolventSquare n z hz w + freeResolventSquare n z hz (Vt q) := by
    calc q = freeResolventSquare n z hz (Vt x.val) := hq
      _ = freeResolventSquare n z hz (Vt (y + q)) := by rw [← hxyq]
      _ = _ := by rw [map_add, map_add]
  have hq3 : q = freeResolventSquare n z hz (St w) := by
    have hd : q - freeResolventSquare n z hz (St w) =
        freeResolventSquare n z hz (Vt (q - freeResolventSquare n z hz (St w))) := by
      have e := schurCore_hDSw38 n z hz Vt St hS1 w
      simp only [map_sub]
      calc q - freeResolventSquare n z hz (St w)
          = (freeResolventSquare n z hz w + freeResolventSquare n z hz (Vt q)) -
            (freeResolventSquare n z hz w +
              freeResolventSquare n z hz (Vt (freeResolventSquare n z hz (St w)))) := by
            rw [← hq2, ← e]
        _ = _ := by abel
    exact sub_eq_zero.mp (schurCore_inj38 n z hz Vt St hS2 _ hd)
  refine ⟨y, ?_, hPy, ?_⟩
  · intro hy0
    apply hx0
    have hw0 : w = 0 := by rw [hw, hy0, map_zero]
    have hq0 : q = 0 := by rw [hq3, hw0, map_zero, map_zero]
    rw [hxyq, hy0, hq0, add_zero]
  · have hP := congrArg (resonantSquare n) hsh
    rw [resonantSquare_shifted38] at hP
    have hVx : Vt x.val = Vt y + Vt q := by rw [hxyq, map_add]
    rw [← hy] at hP
    rw [hP, hVx, map_add, hq3]
    unfold schurEffectiveSquare38
    simp only [add_apply, ContinuousLinearMap.comp_apply, hPy, hw]


/-- Backward direction of the coordinate Schur elimination. -/
theorem schurCore_backward38
    (hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
        (complementarySquare n).comp (Vt.comp (freeResolventSquare n z hz))).comp St = 1)
    (y : SectorSquare n) (hy0 : y ≠ 0) (hPy : resonantSquare n y = y)
    (hker : (z - spectralCenter n) • y = schurEffectiveSquare38 n z hz Vt St y) :
    ∃ x : freeWeightedDomainPointwise n, x.val ≠ 0 ∧
      z • x.val - freeCoordinateDirac n x - Vt x.val = 0 := by
  set w := Vt y with hw
  set g := St w with hg
  have hyd := freeWeightedDomain_of_resonant38 n y hPy
  have hDd := freeResolventSquare_mem_freeWeightedDomain n z hz g
  let x : freeWeightedDomainPointwise n :=
    ⟨y, hyd⟩ + ⟨freeResolventSquare n z hz g, hDd⟩
  have hxv : x.val = y + freeResolventSquare n z hz g := rfl
  have hPx : resonantSquare n x.val = y := by
    rw [hxv, map_add, hPy, freeResolventSquare_resonant38, add_zero]
  have hshx : freeShiftedCoordinateDirac n z x =
      (z - spectralCenter n) • y + complementarySquare n g := by
    have h1 : freeShiftedCoordinateDirac n z x =
        freeShiftedCoordinateDirac n z ⟨y, hyd⟩ +
          freeShiftedCoordinateDirac n z ⟨freeResolventSquare n z hz g, hDd⟩ := map_add _ _ _
    rw [h1, freeShiftedCoordinateDirac_right_inverse_complement]
    congr 1
    -- the resonant vector `y`: both components of `(z - L0) y` agree with `(z - nπ) y`
    have hQy : complementarySquare n y = 0 := by
      conv_lhs => rw [← hPy]
      exact complementarySquare_resonantSquare38 n y
    have hP := resonantSquare_shifted38 n z ⟨y, hyd⟩
    have hQ : complementarySquare n (freeShiftedCoordinateDirac n z ⟨y, hyd⟩) = 0 := by
      apply lp.ext; funext i
      by_cases h : i.2 = resonantIndex n
      · simp [h]
      · have hyi : y i = 0 := by
          have := congrArg (fun f : SectorSquare n => f i) hPy
          simpa [h] using this.symm
        have e : (freeShiftedCoordinateDirac n z ⟨y, hyd⟩) i =
            z * y i - spectralCenter i.2.val * y i := rfl
        simp [h, e, hyi]
    have hsum := resonantSquare_add_complementarySquare38 n
      (freeShiftedCoordinateDirac n z ⟨y, hyd⟩)
    rw [hP, hQ, add_zero] at hsum
    rw [← hsum]
    simp only [hPy]
  have hshd : freeShiftedCoordinateDirac n z x = z • x.val - freeCoordinateDirac n x := rfl
  have hVx : Vt x.val = w + Vt (freeResolventSquare n z hz g) := by
    rw [hxv, map_add]
  have hSw := schurCore_hSw38 n z hz Vt St hS1 w
  refine ⟨x, ?_, ?_⟩
  · intro h0
    apply hy0
    rw [← hPx, h0, map_zero]
  · rw [← hshd, hshx, hVx]
    set Wv := (z - spectralCenter n) • y + complementarySquare n g - (w + Vt (freeResolventSquare n z hz g)) with hWv
    have hsum := resonantSquare_add_complementarySquare38 n Wv
    have hPW : resonantSquare n Wv = 0 := by
      rw [hWv, map_sub, map_add, map_add, map_smul, hPy, resonantSquare_complementarySquare38]
      have hk : (z - spectralCenter n) • y = resonantSquare n (Vt y) +
          resonantSquare n (Vt (freeResolventSquare n z hz g)) := by
        rw [hker]
        unfold schurEffectiveSquare38
        simp only [add_apply, ContinuousLinearMap.comp_apply, hPy]
        rfl
      rw [hk, ← hw]
      abel
    have hQW : complementarySquare n Wv = 0 := by
      rw [hWv, map_sub, map_add, map_add, map_smul]
      have hQy : complementarySquare n y = 0 := by
        conv_lhs => rw [← hPy]
        exact complementarySquare_resonantSquare38 n y
      have hSw' : g = w + complementarySquare n (Vt (freeResolventSquare n z hz g)) := hSw
      have hQg : complementarySquare n g = complementarySquare n w +
          complementarySquare n (Vt (freeResolventSquare n z hz g)) := by
        have := congrArg (complementarySquare n) hSw'
        rwa [map_add, complementarySquare_idem38] at this
      rw [hQy, smul_zero, zero_add, complementarySquare_idem38, hQg]
      abel
    rw [← hsum, hPW, hQW, add_zero]

end Core


/-! ### The 2x2 kernel statement on the resonant coordinate vectors -/

lemma sq_single_apply38 (n : ℤ) (i j : Bool × Sector n) :
    (lp.single 2 i (1 : ℂ) : SectorSquare n) j = if j = i then 1 else 0 := by
  simp [Pi.single_apply]

lemma combo_apply38 (n : ℤ) (α β : ℂ) (i : Bool × Sector n) :
    (α • lp.single 2 (true, resonantIndex n) (1 : ℂ) +
      β • lp.single 2 (false, resonantIndex n) (1 : ℂ) : SectorSquare n) i =
    α * (lp.single 2 (true, resonantIndex n) (1 : ℂ) : SectorSquare n) i +
      β * (lp.single 2 (false, resonantIndex n) (1 : ℂ) : SectorSquare n) i := rfl

/-- A `P`-range vector is the combination of its two resonant coordinates. -/
lemma resonant_decomp38 (n : ℤ) (y : SectorSquare n) (hy : resonantSquare n y = y) :
    y = y (true, resonantIndex n) • lp.single 2 (true, resonantIndex n) (1 : ℂ) +
      y (false, resonantIndex n) • lp.single 2 (false, resonantIndex n) (1 : ℂ) := by
  apply lp.ext; funext ⟨b, m⟩
  rw [combo_apply38, sq_single_apply38, sq_single_apply38]
  by_cases h : m = resonantIndex n
  · subst h
    cases b <;> simp
  · have hyi : y (b, m) = 0 := by
      have := congrArg (fun f : SectorSquare n => f (b, m)) hy
      simpa [h] using this.symm
    cases b <;> simp [h, hyi]

lemma resonant_combo_mem38 (n : ℤ) (α β : ℂ) :
    resonantSquare n (α • lp.single 2 (true, resonantIndex n) (1 : ℂ) +
      β • lp.single 2 (false, resonantIndex n) (1 : ℂ)) =
      α • lp.single 2 (true, resonantIndex n) (1 : ℂ) +
        β • lp.single 2 (false, resonantIndex n) (1 : ℂ) := by
  apply lp.ext; funext ⟨b, m⟩
  rw [resonantSquare_apply]
  by_cases h : m = resonantIndex n
  · rw [if_pos h]
  · rw [combo_apply38, sq_single_apply38, sq_single_apply38]
    cases b <;> simp [h]

lemma resonant_combo_coord38 (n : ℤ) (α β : ℂ) :
    (α • lp.single 2 (true, resonantIndex n) (1 : ℂ) +
      β • lp.single 2 (false, resonantIndex n) (1 : ℂ) : SectorSquare n)
        (true, resonantIndex n) = α ∧
    (α • lp.single 2 (true, resonantIndex n) (1 : ℂ) +
      β • lp.single 2 (false, resonantIndex n) (1 : ℂ) : SectorSquare n)
        (false, resonantIndex n) = β := by
  rw [combo_apply38, combo_apply38, sq_single_apply38, sq_single_apply38,
    sq_single_apply38, sq_single_apply38]
  simp

/-- The scalar `2 x 2` determinant of `l - T` on the resonant basis. -/
def resonantDet38 (n : ℤ) (l : ℂ) (T : SectorSquare n →L[ℂ] SectorSquare n) : ℂ :=
  (l - T (lp.single 2 (true, resonantIndex n) (1 : ℂ)) (true, resonantIndex n)) *
    (l - T (lp.single 2 (false, resonantIndex n) (1 : ℂ)) (false, resonantIndex n)) -
  T (lp.single 2 (false, resonantIndex n) (1 : ℂ)) (true, resonantIndex n) *
    T (lp.single 2 (true, resonantIndex n) (1 : ℂ)) (false, resonantIndex n)

theorem resonantKernel_iff_det38 (n : ℤ) (l : ℂ) (T : SectorSquare n →L[ℂ] SectorSquare n)
    (hT : ∀ u, resonantSquare n (T u) = T u) :
    (∃ y : SectorSquare n, y ≠ 0 ∧ resonantSquare n y = y ∧ l • y = T y) ↔
      resonantDet38 n l T = 0 := by
  set e1 : SectorSquare n := lp.single 2 (true, resonantIndex n) (1 : ℂ) with he1
  set e2 : SectorSquare n := lp.single 2 (false, resonantIndex n) (1 : ℂ) with he2
  have hTy : ∀ α β : ℂ, T (α • e1 + β • e2) = α • T e1 + β • T e2 := by
    intro α β; rw [map_add, map_smul, map_smul]
  have hlap : ∀ (α β : ℂ) (i : Bool × Sector n),
      (l • (α • e1 + β • e2) : SectorSquare n) i = l * (α * e1 i + β * e2 i) := fun _ _ _ => rfl
  have hTap : ∀ (α β : ℂ) (i : Bool × Sector n),
      (α • T e1 + β • T e2 : SectorSquare n) i = α * T e1 i + β * T e2 i := fun _ _ _ => rfl
  have hc : e1 (true, resonantIndex n) = 1 ∧ e2 (true, resonantIndex n) = 0 ∧
      e1 (false, resonantIndex n) = 0 ∧ e2 (false, resonantIndex n) = 1 := by
    simp [he1, he2]
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hc
  have hdet : resonantDet38 n l T = (l - T e1 (true, resonantIndex n)) *
      (l - T e2 (false, resonantIndex n)) -
      T e2 (true, resonantIndex n) * T e1 (false, resonantIndex n) := rfl
  rw [hdet]
  constructor
  · rintro ⟨y, hy0, hPy, hker⟩
    have hd : y = y (true, resonantIndex n) • e1 + y (false, resonantIndex n) • e2 :=
      resonant_decomp38 n y hPy
    have hα : y (true, resonantIndex n) ≠ 0 ∨ y (false, resonantIndex n) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hy0
      rw [hd, hcon.1, hcon.2]; simp
    generalize y (true, resonantIndex n) = α at hd hα
    generalize y (false, resonantIndex n) = β at hd hα
    have hk := hker
    rw [hd, hTy] at hk
    have h1 := congrArg (fun f : SectorSquare n => f (true, resonantIndex n)) hk
    have h2 := congrArg (fun f : SectorSquare n => f (false, resonantIndex n)) hk
    simp only [hlap, hTap, hc1, hc2, hc3, hc4] at h1 h2
    generalize T e1 (true, resonantIndex n) = a11 at h1 h2 ⊢
    generalize T e1 (false, resonantIndex n) = a21 at h1 h2 ⊢
    generalize T e2 (true, resonantIndex n) = a12 at h1 h2 ⊢
    generalize T e2 (false, resonantIndex n) = a22 at h1 h2 ⊢
    rcases hα with h | h
    · have : ((l - a11) * (l - a22) - a12 * a21) * α = 0 := by
        linear_combination (l - a22) * h1 + a12 * h2
      exact (mul_eq_zero.mp this).resolve_right h
    · have : ((l - a11) * (l - a22) - a12 * a21) * β = 0 := by
        linear_combination (l - a11) * h2 + a21 * h1
      exact (mul_eq_zero.mp this).resolve_right h
  · intro hdet0
    obtain ⟨α, β, hne, h1, h2⟩ : ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧
        l * α = α * T e1 (true, resonantIndex n) + β * T e2 (true, resonantIndex n) ∧
        l * β = α * T e1 (false, resonantIndex n) + β * T e2 (false, resonantIndex n) := by
      generalize T e1 (true, resonantIndex n) = a11 at hdet0 ⊢
      generalize T e1 (false, resonantIndex n) = a21 at hdet0 ⊢
      generalize T e2 (true, resonantIndex n) = a12 at hdet0 ⊢
      generalize T e2 (false, resonantIndex n) = a22 at hdet0 ⊢
      by_cases hp : (a12 ≠ 0 ∨ l - a11 ≠ 0)
      · refine ⟨a12, l - a11, hp, ?_, ?_⟩
        · ring
        · linear_combination hdet0
      · push Not at hp
        by_cases hq : (l - a22 ≠ 0 ∨ a21 ≠ 0)
        · refine ⟨l - a22, a21, hq, ?_, ?_⟩
          · linear_combination hdet0
          · ring
        · push Not at hq
          refine ⟨1, 0, Or.inl one_ne_zero, ?_, ?_⟩
          · have : l = a11 := by linear_combination hp.2
            rw [this]; ring
          · rw [hq.2]; ring
    refine ⟨α • e1 + β • e2, ?_, resonant_combo_mem38 n α β, ?_⟩
    · intro h0
      have c1 := resonant_combo_coord38 n α β
      rw [← he1, ← he2, h0] at c1
      simp at c1
      rcases hne with h | h
      · exact h c1.1.symm
      · exact h c1.2.symm
    · apply lp.ext; funext ⟨b, m⟩
      rw [hTy]
      change l * (α • e1 + β • e2 : SectorSquare n) (b, m) =
        (α • T e1 + β • T e2 : SectorSquare n) (b, m)
      rw [hTap, combo_apply38]
      by_cases hm : m = resonantIndex n
      · subst hm
        cases b
        · rw [hc3, hc4]
          linear_combination h2
        · rw [hc1, hc2]
          linear_combination h1
      · have hz1 : (T (α • e1 + β • e2)) (b, m) = 0 := by
          have := congrArg (fun f : SectorSquare n => f (b, m)) (hT (α • e1 + β • e2))
          simp only [resonantSquare_apply] at this
          simpa [hm] using this.symm
        rw [hTy, hTap] at hz1
        have e1z : e1 (b, m) = 0 := by
          rw [he1, sq_single_apply38, if_neg]
          intro h; exact hm (congrArg Prod.snd h)
        have e2z : e2 (b, m) = 0 := by
          rw [he2, sq_single_apply38, if_neg]
          intro h; exact hm (congrArg Prod.snd h)
        rw [hz1, e1z, e2z]; ring


/-! ### Transport from `ParityPair n` to the coordinate space -/

section Transport

variable (n : ℤ)

lemma toSq_apply38 (T : ParityPair n →L[ℂ] ParityPair n) (x : SectorSquare n) :
    actualSchurEndomorphismToSquareV5_30 n T x =
      parityPairRepr n (T ((parityPairRepr n).symm x)) := rfl

lemma toSq_comp38 (A B : ParityPair n →L[ℂ] ParityPair n) :
    actualSchurEndomorphismToSquareV5_30 n (A.comp B) =
      (actualSchurEndomorphismToSquareV5_30 n A).comp
        (actualSchurEndomorphismToSquareV5_30 n B) := by
  ext x : 1
  simp [toSq_apply38]

lemma toSq_one38 :
    actualSchurEndomorphismToSquareV5_30 n (1 : ParityPair n →L[ℂ] ParityPair n) = 1 := by
  ext x : 1
  simp [toSq_apply38]

lemma toSq_sub38 (A B : ParityPair n →L[ℂ] ParityPair n) :
    actualSchurEndomorphismToSquareV5_30 n (A - B) =
      actualSchurEndomorphismToSquareV5_30 n A - actualSchurEndomorphismToSquareV5_30 n B := by
  ext x : 1
  simp [toSq_apply38]

lemma toSq_add38 (A B : ParityPair n →L[ℂ] ParityPair n) :
    actualSchurEndomorphismToSquareV5_30 n (A + B) =
      actualSchurEndomorphismToSquareV5_30 n A + actualSchurEndomorphismToSquareV5_30 n B := by
  ext x : 1
  simp [toSq_apply38]

lemma toSq_resonant38 :
    actualSchurEndomorphismToSquareV5_30 n (resonantParityPair n) = resonantSquare n := by
  ext x : 1
  simp [toSq_apply38, resonantParityPair]

lemma toSq_complementary38 :
    actualSchurEndomorphismToSquareV5_30 n (freeResolventComplementaryProjectionTransported n) =
      complementarySquare n := by
  ext x : 1
  simp [toSq_apply38, freeResolventComplementaryProjectionTransported]

lemma toSq_freeResolvent38 (z : ℂ) (hz : z ∈ spectralDisk n) :
    actualSchurEndomorphismToSquareV5_30 n (freeResolventParityPair n z hz) =
      freeResolventSquare n z hz := by
  ext x : 1
  simp [toSq_apply38, freeResolventParityPair]

/-- Matrix entries of the actual operator are the coordinate entries of its transport. -/
lemma schurCoefficient_eq_toSq38 (i j : Bool × Sector n) (x : ℂ × ActualSchurEffectiveH1PairV3_30) :
    actualSchurCoefficientAfterDext31 n i j x =
      actualSchurEndomorphismToSquareV5_30 n (actualSchurEffectiveOperatorAfterDextV3_30 n x)
        (lp.single 2 j (1 : ℂ)) i := by
  rw [toSq_apply38, ← parityPairRepr_vector, LinearIsometryEquiv.symm_apply_apply,
    parityPairRepr_inner]
  rfl

end Transport


/-! ### The concrete statement -/

/-- The actual parity-pair potential `V(p)` written in the Fourier coordinates:
`Ṽ = repr ∘ V ∘ repr.symm` on `SectorSquare n`. -/
def actualSchurCoordinatePotential38 (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  actualSchurEndomorphismToSquareV5_30 n
    (actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p)

/-- The secular determinant `(λ - nπ - a₊₊)(λ - nπ - a₋₋) - a₊₋ a₋₊` of the actual
`2 x 2` Schur matrix, with `a_ij = ⟪e_i, A_n(λ) e_j⟫` the actual coefficients. -/
def actualSchurSecularDet38 (n : ℤ) (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30) : ℂ :=
  (z - spectralCenter n -
      actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (true, resonantIndex n) (z, p)) *
    (z - spectralCenter n -
      actualSchurCoefficientAfterDext31 n (false, resonantIndex n) (false, resonantIndex n) (z, p)) -
  actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n) (z, p) *
    actualSchurCoefficientAfterDext31 n (false, resonantIndex n) (true, resonantIndex n) (z, p)

/-- Schur elimination in the Fourier-coordinate model: a nonzero domain solution of
`(z - L₀ - Ṽ) x = 0` exists iff the secular determinant vanishes. -/
theorem actualSchur_eigenvalue_iff_secularDet_zero38V1
    (R : ℝ) (hR : 1 ≤ R)
    (n : ℤ) (hn : 1 ≤ |(n : ℝ)|)
    (hlarge : 4 * freeResolventSchurUniformConstant *
      physicalH1MultiplierConstant * R ^ 2 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    (∃ x : freeWeightedDomainPointwise n, x.val ≠ 0 ∧
      z • x.val - freeCoordinateDirac n x - actualSchurCoordinatePotential38 n p x.val = 0) ↔
    actualSchurSecularDet38 n z p = 0 := by
  set V : ParityPair n →L[ℂ] ParityPair n :=
    actualParityPairPotentialParameterAfterScalarWrapperCLM23 n p with hV
  set D : ParityPair n →L[ℂ] ParityPair n := freeResolventParityPair n z hz with hD
  set Q : ParityPair n →L[ℂ] ParityPair n := freeResolventComplementaryProjectionTransported n
    with hQ
  set P : ParityPair n →L[ℂ] ParityPair n := resonantParityPair n with hP
  set S : ParityPair n →L[ℂ] ParityPair n := actualComplementaryQVDJointInverseV5_30 n (z, p)
    with hS
  have hDext : actualFreeResolventCenterExtensionV1_30 n z = D :=
    actualFreeResolventCenterExtension_eq_actualV1_30 n z hz
  have hK : actualComplementaryQVDJointParameterV5_30 n (z, p) = Q.comp (V.comp D) := by
    dsimp [actualComplementaryQVDJointParameterV5_30]
    rw [hDext]
  have hM : actualSchurEffectiveOperatorAfterDextV3_30 n (z, p) =
      P.comp (V.comp P) + P.comp (V.comp ((D.comp S).comp (V.comp P))) := by
    dsimp [actualSchurEffectiveOperatorAfterDextV3_30]
    rw [hDext]
    rfl
  have htwo := actualComplementaryQVDJointInverseV5_30_twoSided
    R hR n hn hlarge z p hz hp₁ hp₂
  rw [hK] at htwo
  obtain ⟨htwo1, htwo2⟩ := htwo
  -- transported identities
  have hS1 : ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
      (complementarySquare n).comp
        ((actualSchurCoordinatePotential38 n p).comp (freeResolventSquare n z hz))).comp
      (actualSchurEndomorphismToSquareV5_30 n S) = 1 := by
    have h := congrArg (actualSchurEndomorphismToSquareV5_30 n) htwo2
    rw [toSq_comp38, toSq_sub38, toSq_one38, toSq_comp38, toSq_comp38, toSq_complementary38,
      toSq_freeResolvent38] at h
    exact h
  have hS2 : (actualSchurEndomorphismToSquareV5_30 n S).comp
      ((1 : SectorSquare n →L[ℂ] SectorSquare n) -
      (complementarySquare n).comp
        ((actualSchurCoordinatePotential38 n p).comp (freeResolventSquare n z hz))) = 1 := by
    have h := congrArg (actualSchurEndomorphismToSquareV5_30 n) htwo1
    rw [toSq_comp38, toSq_sub38, toSq_one38, toSq_comp38, toSq_comp38, toSq_complementary38,
      toSq_freeResolvent38] at h
    exact h
  have hA : actualSchurEndomorphismToSquareV5_30 n (actualSchurEffectiveOperatorAfterDextV3_30 n (z, p)) =
      schurEffectiveSquare38 n z hz (actualSchurCoordinatePotential38 n p)
        (actualSchurEndomorphismToSquareV5_30 n S) := by
    rw [hM, toSq_add38, toSq_comp38, toSq_comp38, toSq_comp38, toSq_comp38, toSq_comp38,
      toSq_comp38, toSq_comp38, toSq_resonant38, toSq_freeResolvent38]
    rfl
  have hRange : ∀ u, resonantSquare n
      (schurEffectiveSquare38 n z hz (actualSchurCoordinatePotential38 n p)
        (actualSchurEndomorphismToSquareV5_30 n S) u) =
      schurEffectiveSquare38 n z hz (actualSchurCoordinatePotential38 n p)
        (actualSchurEndomorphismToSquareV5_30 n S) u := by
    intro u
    unfold schurEffectiveSquare38
    simp only [add_apply, ContinuousLinearMap.comp_apply, map_add,
      resonantSquare_idem38]
  have hdet : actualSchurSecularDet38 n z p =
      resonantDet38 n (z - spectralCenter n)
        (schurEffectiveSquare38 n z hz (actualSchurCoordinatePotential38 n p)
          (actualSchurEndomorphismToSquareV5_30 n S)) := by
    rw [← hA]
    unfold actualSchurSecularDet38 resonantDet38
    simp only [schurCoefficient_eq_toSq38]
  rw [hdet, ← resonantKernel_iff_det38 n _ _ hRange]
  constructor
  · rintro ⟨x, hx0, heq⟩
    exact schurCore_forward38 n z hz _ _ hS1 hS2 x hx0 heq
  · rintro ⟨y, hy0, hPy, hker⟩
    exact schurCore_backward38 n z hz _ _ hS1 y hy0 hPy hker

/-- The same theorem under the source threshold `|n| ≥ C R³`. -/
theorem actualSchur_eigenvalue_iff_secularDet_zero_threshold38V1
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (z : ℂ) (p : ActualSchurEffectiveH1PairV3_30)
    (hz : z ∈ spectralDisk n) (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    (∃ x : freeWeightedDomainPointwise n, x.val ≠ 0 ∧
      z • x.val - freeCoordinateDirac n x - actualSchurCoordinatePotential38 n p x.val = 0) ↔
    actualSchurSecularDet38 n z p = 0 := by
  obtain ⟨hn, hlarge, -, -⟩ := actualSchurCenterThresholdConstant38_consequences R hR n hthr
  exact actualSchur_eigenvalue_iff_secularDet_zero38V1 R hR n hn hlarge z p hz hp₁ hp₂

end NlsGge.Schur
