import Mathlib
import QuantumNLS.Ext006BogoliubovAlg

/-! PROP-023 physical-form interface, stage 1: from the symplecticity of the physical map
`S v = α' v + β' v̄` to the Bogoliubov relations of the inverse pair `(α, β) = (α'†, -β'ᵀ)`.

* `PhysSymplectic A B`: `S = Smap A B` preserves `Im ⟨·,·⟩` on `ℓ²(ℤ)` and is onto (a symplectic
  isomorphism, as the variational flow `S(t,s)` of fluctuations.tex is).
* `invpair_isBogoliubov`: `IsBogoliubov (A†) (-(tpB))` (the relations used by `Ext006QuasifreeWeak`).
* `invpair_identity`: from the Heisenberg relations `X = A u + B w`, `Y = Ā w + B̄ u`
  (`Ā = conj ∘ A ∘ conj`), one gets `u = A† X - Bᵀ Y`, the inverse Bogoliubov matrix
  `[[A†, -Bᵀ],[-B†, Aᵀ]]` applied to `(X, Y)`.
Only the left-inverse part (`ω`-preservation) is used for the identity; surjectivity is used only
for the relation `α†α - βᵀβ̄ = 1` of the inverse pair. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Ext006PhysSymplectic
open QuantumNLS.Ext006BogoliubovAlg

/-- The real-linear map `v ↦ A v + B v̄` (`S v = α v + β v̄` of the source). -/
def Smap (A B : H →L[ℂ] H) (v : H) : H := A v + B (star v)

/-- The symplectic adjoint `w ↦ A† w - conj (B† w)` of `Smap A B`. -/
def Ssharp (A B : H →L[ℂ] H) (w : H) : H :=
  ContinuousLinearMap.adjoint A w - star (ContinuousLinearMap.adjoint B w)

/-- `S v = A v + B v̄` is a symplectic isomorphism of `(ℓ²(ℤ), Im ⟨·,·⟩)`: it preserves the
symplectic form and is onto. -/
structure PhysSymplectic (A B : H →L[ℂ] H) : Prop where
  symp : ∀ v w, (inner ℂ (Smap A B v) (Smap A B w)).im = (inner ℂ v w).im
  surj : Function.Surjective (Smap A B)

lemma inner_star' (a b : H) : inner ℂ (star a) (star b) = conj (inner ℂ a b) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.conj_tsum]
  refine tsum_congr fun i => ?_
  simp [lp.star_apply, RCLike.inner_apply]

/-- Entrywise conjugate `conj ∘ T ∘ conj`. -/
def bar (T : H →L[ℂ] H) : H →L[ℂ] H := tp (ContinuousLinearMap.adjoint T)

lemma bar_apply (T : H →L[ℂ] H) (x : H) : bar T x = star (T (star x)) := by
  simp [bar, tp_apply]

lemma adjoint_bar (T : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (bar T) = bar (ContinuousLinearMap.adjoint T) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [bar_apply, bar_apply]
  calc inner ℂ (star (ContinuousLinearMap.adjoint T (star x))) y
      = inner ℂ (star (ContinuousLinearMap.adjoint T (star x))) (star (star y)) := by rw [star_star]
    _ = conj (inner ℂ (ContinuousLinearMap.adjoint T (star x)) (star y)) := inner_star' _ _
    _ = conj (inner ℂ (star x) (T (star y))) := by rw [ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ (star (star x)) (star (T (star y))) := (inner_star' _ _).symm
    _ = inner ℂ x (star (T (star y))) := by rw [star_star]

lemma adjoint_tp (T : H →L[ℂ] H) : ContinuousLinearMap.adjoint (tp T) = bar T := by
  have : tp T = bar (ContinuousLinearMap.adjoint T) := by
    unfold bar; rw [ContinuousLinearMap.adjoint_adjoint]
  rw [this, adjoint_bar, ContinuousLinearMap.adjoint_adjoint]

lemma tp_tp (T : H →L[ℂ] H) : tp (tp T) = T := by
  ext x : 1
  rw [tp_apply, adjoint_tp, bar_apply, star_star, star_star]

lemma tp_neg (T : H →L[ℂ] H) : tp (-T) = -tp T := by
  ext x : 1
  simp [tp_apply]

lemma omega_adj (A B : H →L[ℂ] H) (v w : H) :
    (inner ℂ (Smap A B v) w).im = (inner ℂ v (Ssharp A B w)).im := by
  have h1 : inner ℂ (A v) w = inner ℂ v (ContinuousLinearMap.adjoint A w) :=
    (ContinuousLinearMap.adjoint_inner_right A v w).symm
  have h2 : inner ℂ (B (star v)) w = inner ℂ (star v) (ContinuousLinearMap.adjoint B w) :=
    (ContinuousLinearMap.adjoint_inner_right B (star v) w).symm
  have h3 : inner ℂ (star v) (ContinuousLinearMap.adjoint B w) =
      conj (inner ℂ v (star (ContinuousLinearMap.adjoint B w))) := by
    have := inner_star' v (star (ContinuousLinearMap.adjoint B w))
    rwa [star_star] at this
  unfold Smap Ssharp
  rw [inner_add_left, inner_sub_right, h1, h2, h3, Complex.add_im, Complex.sub_im,
    Complex.conj_im]
  ring

lemma eq_of_im_inner (z : H) (h : ∀ v, (inner ℂ v z).im = 0) : z = 0 := by
  have h1 := h (Complex.I • z)
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K] at h1
  simp at h1
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at h1
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h1)

lemma F1 {A B : H →L[ℂ] H} (hs : PhysSymplectic A B) (v : H) : Ssharp A B (Smap A B v) = v := by
  have : Ssharp A B (Smap A B v) - v = 0 := by
    apply eq_of_im_inner
    intro v'
    rw [inner_sub_right, Complex.sub_im, ← omega_adj, hs.symp, sub_self]
  exact sub_eq_zero.mp this

lemma F2 {A B : H →L[ℂ] H} (hs : PhysSymplectic A B) (w : H) : Smap A B (Ssharp A B w) = w := by
  obtain ⟨y, rfl⟩ := hs.surj w
  rw [F1 hs]

lemma symp_sharp {A B : H →L[ℂ] H} (hs : PhysSymplectic A B) (w w' : H) :
    (inner ℂ (Ssharp A B w) (Ssharp A B w')).im = (inner ℂ w w').im := by
  have := omega_adj A B (Ssharp A B w) w'
  rw [F2 hs] at this
  exact this.symm

lemma norm_rel (a b : H →L[ℂ] H)
    (h : ∀ v w, (inner ℂ (Smap a b v) (Smap a b w)).im = (inner ℂ v w).im) (x : H) :
    ‖a x‖ ^ 2 = ‖x‖ ^ 2 + ‖b (star x)‖ ^ 2 := by
  have h1 := h x (Complex.I • x)
  have hS : Smap a b (Complex.I • x) = Complex.I • (a x - b (star x)) := by
    simp [Smap, star_smul, sub_eq_add_neg]
  have hS' : Smap a b x = a x + b (star x) := rfl
  rw [hS, hS', inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  rw [inner_add_left, inner_sub_right, inner_sub_right, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at h1
  have hc := inner_re_symm (𝕜 := ℂ) (a x) (b (star x))
  simp at h1
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at h1
  simp only [RCLike.re_to_complex] at hc
  linarith

lemma two_lemma {V : Type*} [AddCommGroup V] [Module ℂ V] (a1 a2 a3 a4 v : V)
    (h1 : a1 + a2 - (a3 + a4) = v)
    (h2 : Complex.I • (a1 - a2) - (-Complex.I) • (a3 - a4) = Complex.I • v) :
    a1 - a4 = v ∧ a2 = a3 := by
  have h2' : (a1 - a2) + (a3 - a4) = v := by
    apply smul_right_injective V Complex.I_ne_zero
    show Complex.I • ((a1 - a2) + (a3 - a4)) = Complex.I • v
    rw [← h2]; module
  have hP : (2:ℂ) • (a1 - a4) = (2:ℂ) • v := by
    calc (2:ℂ) • (a1 - a4) = (a1 + a2 - (a3 + a4)) + ((a1 - a2) + (a3 - a4)) := by module
      _ = v + v := by rw [h1, h2']
      _ = (2:ℂ) • v := by module
  have hQ : (2:ℂ) • a2 = (2:ℂ) • a3 := by
    calc (2:ℂ) • a2 = (a1 + a2 - (a3 + a4)) - ((a1 - a2) + (a3 - a4)) + (2:ℂ) • a3 := by module
      _ = (2:ℂ) • a3 := by rw [h1, h2']; simp
  exact ⟨smul_right_injective V (two_ne_zero) hP, smul_right_injective V (two_ne_zero) hQ⟩

/-- The complex-linear and antilinear parts of `Ssharp ∘ Smap = id`. -/
lemma PQ {A B : H →L[ℂ] H} (hs : PhysSymplectic A B) (v : H) :
    ContinuousLinearMap.adjoint A (A v) -
        star (ContinuousLinearMap.adjoint B (B (star v))) = v ∧
      ContinuousLinearMap.adjoint A (B (star v)) = star (ContinuousLinearMap.adjoint B (A v)) := by
  have h1 := F1 hs v
  have h2 := F1 hs (Complex.I • v)
  have hS : Smap A B (Complex.I • v) = Complex.I • (A v - B (star v)) := by
    simp [Smap, star_smul, sub_eq_add_neg]
  unfold Ssharp at h1 h2
  rw [hS] at h2
  simp only [Smap, map_add, star_add] at h1
  simp only [map_smul, map_sub, star_smul, star_sub, Complex.star_def, Complex.conj_I] at h2
  exact two_lemma _ _ _ _ _ h1 h2

lemma smap_adjoint_eq (A B : H →L[ℂ] H) (w : H) :
    Smap (ContinuousLinearMap.adjoint A) (-(tp B)) w = Ssharp A B w := by
  simp [Smap, Ssharp, tp_apply, sub_eq_add_neg]

/-- **The inverse pair is Bogoliubov.**  If `S = (A, B)` is a symplectic isomorphism then
`(α, β) = (A†, -Bᵀ)` satisfies the Bogoliubov relations. -/
theorem invpair_isBogoliubov {A B : H →L[ℂ] H} (hs : PhysSymplectic A B) :
    IsBogoliubov (ContinuousLinearMap.adjoint A) (-(tp B)) where
  r1 x := by
    rw [ContinuousLinearMap.adjoint_adjoint, map_neg, adjoint_tp]
    have := norm_rel A B hs.symp x
    rw [this, show ((-bar B) x) = -(bar B x) from rfl, norm_neg, bar_apply, norm_star]
  r2 x := by
    apply norm_rel
    intro v w
    rw [smap_adjoint_eq, smap_adjoint_eq]
    exact symp_sharp hs v w
  r3 := by
    ext x : 1
    simp only [ContinuousLinearMap.comp_apply, tp_neg, tp_tp, neg_apply,
      map_neg]
    rw [tp_apply (ContinuousLinearMap.adjoint A) x, tp_apply B]
    simp only [ContinuousLinearMap.adjoint_adjoint, star_star]
    obtain ⟨-, hQ⟩ := PQ hs (star x)
    rw [star_star] at hQ
    rw [hQ]

/-- **The inverse-pair identity.**  If `X = A u + B w` and `Y = Ā w + B̄ u` then
`u = A† X - Bᵀ Y`. -/
theorem invpair_identity {A B : H →L[ℂ] H} (hs : PhysSymplectic A B) {u w X Y : H}
    (hX : X = A u + B w) (hY : Y = star (A (star w)) + star (B (star u))) :
    u = ContinuousLinearMap.adjoint A X - tp B Y := by
  obtain ⟨hP, -⟩ := PQ hs u
  obtain ⟨-, hQ⟩ := PQ hs (star w)
  rw [star_star] at hQ
  subst hX hY
  rw [tp_apply]
  simp only [map_add, star_add, star_star]
  have e : ContinuousLinearMap.adjoint A (A u) + ContinuousLinearMap.adjoint A (B w) -
      (star (ContinuousLinearMap.adjoint B (A (star w))) +
        star (ContinuousLinearMap.adjoint B (B (star u)))) =
      (ContinuousLinearMap.adjoint A (A u) - star (ContinuousLinearMap.adjoint B (B (star u)))) +
      (ContinuousLinearMap.adjoint A (B w) - star (ContinuousLinearMap.adjoint B (A (star w)))) := by
    abel
  rw [e, hP, sub_eq_zero.mpr hQ, add_zero]

end QuantumNLS.Ext006PhysSymplectic

#print axioms QuantumNLS.Ext006PhysSymplectic.invpair_isBogoliubov
#print axioms QuantumNLS.Ext006PhysSymplectic.invpair_identity
