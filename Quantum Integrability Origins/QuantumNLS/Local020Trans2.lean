import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Mul2
import QuantumNLS.Local020Trans
import QuantumNLS.Local020Entry

/-! LOCAL-020 stage S6b: translation covariance at every index.

`Rel n' n u' u c` records `SmallCompression(n', u') ↔ SmallCompression(n, u)` and `b_{n'}(u') = c · b_n(u)` for the
lower-left entries `bentry` of the polar-normalized reduced matrices.  Chain: boost to index `0`
(`Local020Mul2.phaseBoost_reduced`), periodic rotation at `n = 0` (`Local020Trans.trans_reduced0`), phase, boost back.
Result `trans_reduced`: for every `L`-periodic potential `w` and every real `y`,
`b_n(w(· + y)) = e^{i p_n y} b_n(w)` and `SmallCompression` is equivalent. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open QuantumNLS.LocalSpectral QuantumNLS.Local020Entry QuantumNLS.Local020Mul2

namespace QuantumNLS.Local020Trans2

variable {L κ : ℝ}

def Rel (L κ r : ℝ) (n' n : ℤ) (u' u : ℝ → ℂ) (c : ℂ) : Prop :=
  (SmallCompression L κ u' n' r ↔ SmallCompression L κ u n r) ∧
    ∀ (h' : SmallCompression L κ u' n' r) (hh : SmallCompression L κ u n r),
      bentry (reducedMatrix2 L κ u' n' r h') = c * bentry (reducedMatrix2 L κ u n r hh)

variable {r : ℝ}

theorem Rel.trans {n2 n1 n0 : ℤ} {u2 u1 u0 : ℝ → ℂ} {c1 c0 : ℂ}
    (h1 : Rel L κ r n2 n1 u2 u1 c1) (h0 : Rel L κ r n1 n0 u1 u0 c0) :
    Rel L κ r n2 n0 u2 u0 (c1 * c0) := by
  refine ⟨h1.1.trans h0.1, fun h' hh => ?_⟩
  have hm : SmallCompression L κ u1 n1 r := h1.1.1 h'
  rw [h1.2 h' hm, h0.2 hm hh, mul_assoc]

theorem Rel.symm1 {n' n : ℤ} {u' u : ℝ → ℂ} (h : Rel L κ r n' n u' u 1) : Rel L κ r n n' u u' 1 := by
  refine ⟨h.1.symm, fun hh h' => ?_⟩
  have := h.2 h' hh
  rw [one_mul] at this ⊢
  exact this.symm

theorem Rel.congr {n' n : ℤ} {u' u v' v : ℝ → ℂ} {c : ℂ} (h : Rel L κ r n' n u' u c) (e' : u' = v') (e : u = v) :
    Rel L κ r n' n v' v c := by
  subst e'; subst e; exact h

/-- Boost to index `0`: `b_n(e^{ip_n x} u) = b_0(u)`. -/
theorem rel_boost (hL : 0 < L) (n : ℤ) (u : ℝ → ℂ) :
    Rel L κ r n 0 (upb 0 (pm L n / 2) u) u 1 := by
  obtain ⟨h1, h2⟩ := phaseBoost_reduced (κ := κ) hL 0 n 0 r u
  have e : (0 : ℤ) + n = n := zero_add n
  have key : ∀ m : ℤ, m = 0 + n → Rel L κ r m 0 (upb 0 (pm L n / 2) u) u 1 := by
    intro m hm
    subst hm
    refine ⟨h1, fun h' hh => ?_⟩
    rw [h2 h' hh]
    simp
  exact key n e.symm

/-- Common phase at index `n`. -/
theorem rel_phase (hL : 0 < L) (n : ℤ) (a : ℝ) (u : ℝ → ℂ) :
    Rel L κ r n n (fun x => Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I) * u x) u
      (Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨h1, h2⟩ := phaseBoost_reduced (κ := κ) hL a 0 n r u
  have e : n + 0 = n := add_zero n
  have hu : upb a (pm L 0 / 2) u = fun x => Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I) * u x := by
    funext x
    unfold upb bf
    have : pm L 0 = 0 := Local020Trans.pm_zero L
    rw [this, ← Complex.exp_nat_mul]
    congr 2
    push_cast; ring
  have key : ∀ m : ℤ, m = n + 0 → Rel L κ r m n (upb a (pm L 0 / 2) u) u
      (Complex.exp (((2 * a : ℝ) : ℂ) * Complex.I)) := by
    intro m hm
    subst hm
    exact ⟨h1, h2⟩
  have := key n e.symm
  rwa [hu] at this

theorem rel_trans0 (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (u : ℝ → ℂ) :
    Rel L κ r 0 0 (fun x => u (Local020Trans.Ty L y x)) u 1 := by
  obtain ⟨h1, h2⟩ := Local020Trans.trans_reduced0 (κ := κ) hL hy0 hy1 r u
  exact ⟨h1, fun h' hh => by rw [h2 h' hh, one_mul]⟩

theorem Rel.cc {n' n : ℤ} {u' u : ℝ → ℂ} {c c' : ℂ} (h : Rel L κ r n' n u' u c) (e : c = c') :
    Rel L κ r n' n u' u c' := by subst e; exact h

theorem pm_mul_L (n : ℤ) (hL : 0 < L) : ((pm L n : ℝ) : ℂ) * (L : ℂ) = 2 * Real.pi * n := by
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  unfold pm
  push_cast
  field_simp

theorem exp_neg_pL (n : ℤ) (hL : 0 < L) :
    Complex.exp (-(Complex.I * ((pm L n : ℝ) : ℂ) * (L : ℂ))) = 1 := by
  have : -(Complex.I * ((pm L n : ℝ) : ℂ) * (L : ℂ)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have := pm_mul_L (L := L) n hL
    calc -(Complex.I * ((pm L n : ℝ) : ℂ) * (L : ℂ)) = -(Complex.I * (((pm L n : ℝ) : ℂ) * (L : ℂ))) := by ring
      _ = _ := by rw [this]; push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- **S6b** for `0 ≤ y ≤ L`. -/
theorem trans_reduced_Icc (hL : 0 < L) (n : ℤ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ L) (w : ℝ → ℂ)
    (hw : ∀ x, w (x + L) = w x) :
    Rel L κ r n n (fun x => w (x + y)) w
      (Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ))) := by
  set p : ℝ := pm L n with hp
  set v : ℝ → ℂ := fun x => Complex.exp (-(Complex.I * (p : ℂ) * (x : ℂ))) * w x with hv
  have hvper : ∀ x, v (x + L) = v x := by
    intro x
    simp only [hv, hw]
    congr 1
    have := exp_neg_pL (L := L) n hL
    rw [← hp] at this
    have e : -(Complex.I * (p : ℂ) * (((x + L : ℝ)) : ℂ)) =
        -(Complex.I * (p : ℂ) * (x : ℂ)) + -(Complex.I * (p : ℂ) * (L : ℂ)) := by push_cast; ring
    rw [e, Complex.exp_add, this, mul_one]
  have hbf : ∀ x : ℝ, bf 0 (p / 2) x ^ 2 = Complex.exp (Complex.I * (p : ℂ) * (x : ℂ)) := by
    intro x
    unfold bf
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hwv : w = upb 0 (p / 2) v := by
    funext x
    unfold upb
    rw [hbf, hv]
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    have : Complex.I * (p : ℂ) * (x : ℂ) + -(Complex.I * (p : ℂ) * (x : ℂ)) = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  have hvT : ∀ x, v (x + y) = v (Local020Trans.Ty L y x) := by
    intro x
    unfold Local020Trans.Ty
    split_ifs with h
    · rfl
    · have := hvper (x + y - L)
      rw [show x + y - L + L = x + y by ring] at this
      exact this
  set u' : ℝ → ℂ := fun x => Complex.exp (-(Complex.I * (p : ℂ) * (x : ℂ))) * w (x + y) with hu'
  have hw' : (fun x => w (x + y)) = upb 0 (p / 2) u' := by
    funext x
    unfold upb
    rw [hbf, hu']
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    have : Complex.I * (p : ℂ) * (x : ℂ) + -(Complex.I * (p : ℂ) * (x : ℂ)) = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  have hu'v : u' = fun x => Complex.exp (((2 * (p * y / 2) : ℝ) : ℂ) * Complex.I) *
      (fun x => v (Local020Trans.Ty L y x)) x := by
    funext x
    show u' x = Complex.exp (((2 * (p * y / 2) : ℝ) : ℂ) * Complex.I) * v (Local020Trans.Ty L y x)
    rw [← hvT x]
    simp only [hu', hv]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have R1 : Rel L κ r n 0 (fun x => w (x + y)) u' 1 := by
    rw [hw']; exact rel_boost hL n u'
  have R2 := rel_phase (L := L) (κ := κ) (r := r) hL 0 (p * y / 2) (fun x => v (Local020Trans.Ty L y x))
  rw [← hu'v] at R2
  have R3 := rel_trans0 (L := L) (κ := κ) (r := r) hL hy0 hy1 v
  have R4 : Rel L κ r 0 n v w 1 := by
    have := (rel_boost (κ := κ) (r := r) hL n v).symm1
    rwa [← hwv] at this
  have := R1.trans (R2.trans (R3.trans R4))
  refine this.cc ?_
  simp only [mul_one, one_mul]
  congr 1
  push_cast; ring

/-- **S6b (translation covariance of the lower-left entry).**  Any `L`-periodic potential, any real `y`. -/
theorem trans_reduced (hL : 0 < L) (n : ℤ) (y : ℝ) (w : ℝ → ℂ) (hw : ∀ x, w (x + L) = w x) :
    Rel L κ r n n (fun x => w (x + y)) w
      (Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ))) := by
  set k : ℤ := ⌊y / L⌋ with hk
  set y0 : ℝ := y - k * L with hy0
  have h0 : 0 ≤ y0 := by
    have := Int.floor_le (y / L)
    rw [hy0]; rw [le_div_iff₀ hL] at this; linarith
  have h1 : y0 ≤ L := by
    have := Int.lt_floor_add_one (y / L)
    rw [div_lt_iff₀ hL] at this
    rw [hy0]; nlinarith
  have hper : Function.Periodic w L := hw
  have e1 : (fun x => w (x + y)) = fun x => w (x + y0) := by
    funext x
    have := (hper.int_mul k) (x + y0)
    rw [show x + y0 + (k : ℝ) * L = x + y by rw [hy0]; ring] at this
    exact this
  have h := trans_reduced_Icc (κ := κ) (r := r) hL n h0 h1 w hw
  rw [e1]
  refine h.cc ?_
  have : (y : ℂ) = (y0 : ℂ) + (k : ℂ) * (L : ℂ) := by rw [hy0]; push_cast; ring
  rw [this]
  have hpm := pm_mul_L (L := L) n hL
  rw [mul_add, ← mul_assoc, show Complex.I * ((pm L n : ℝ) : ℂ) * (k : ℂ) * (L : ℂ) =
    Complex.I * (k : ℂ) * (((pm L n : ℝ) : ℂ) * (L : ℂ)) by ring, hpm, Complex.exp_add]
  have : Complex.exp (Complex.I * (k : ℂ) * (2 * Real.pi * n)) = 1 := by
    have : Complex.I * (k : ℂ) * (2 * Real.pi * n) = ((k * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [this, mul_one]

end QuantumNLS.Local020Trans2

#print axioms QuantumNLS.Local020Trans2.trans_reduced
