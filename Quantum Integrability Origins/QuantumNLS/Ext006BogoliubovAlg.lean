import Mathlib

/-! PROP-023 / FIN-CORE-BD-02, gap 1 (stage A): Bogoliubov operator algebra on `ℓ²(ℤ)`.

For bounded `α β : ℓ²(ℤ) → ℓ²(ℤ)` satisfying the Bogoliubov (symplectic-isomorphism) relations
`IsBogoliubov`, `α` has a bounded inverse `p` (from `‖α x‖² = ‖x‖² + ‖β x̄‖²` and
`‖α† x‖² = ‖x‖² + ‖β† x‖²`: closed range and dense range) and the kernel `K = p β` is symmetric
(`K_{dc} = K_{cd}`), the matrix form of `α β^T = β α^T`.
`tp T = conj ∘ T† ∘ conj` is the matrix transpose. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006BogoliubovAlg

abbrev H : Type := lp (fun _ : ℤ => ℂ) 2

/-- The matrix transpose `T^T = conj ∘ T^† ∘ conj`. -/
def tp (T : H →L[ℂ] H) : H →L[ℂ] H where
  toFun x := star (ContinuousLinearMap.adjoint T (star x))
  map_add' x y := by simp [star_add]
  map_smul' c x := by
    simp only [star_smul, map_smul, star_star, RingHom.id_apply]
  cont := continuous_star.comp ((ContinuousLinearMap.adjoint T).continuous.comp continuous_star)

lemma tp_apply (T : H →L[ℂ] H) (x : H) :
    tp T x = star (ContinuousLinearMap.adjoint T (star x)) := rfl

lemma tp_comp (S T : H →L[ℂ] H) : tp (S ∘L T) = tp T ∘L tp S := by
  ext x : 1
  simp only [tp_apply, ContinuousLinearMap.comp_apply, star_star, ContinuousLinearMap.adjoint_comp]

lemma adjoint_one_H : ContinuousLinearMap.adjoint (1 : H →L[ℂ] H) = 1 := by
  rw [← ContinuousLinearMap.star_eq_adjoint]; exact star_one _

lemma tp_one : tp (1 : H →L[ℂ] H) = 1 := by
  ext x : 1
  simp [tp_apply, adjoint_one_H]

/-- Matrix entries: `(T^T)_{dc} = T_{cd}`. -/
lemma tp_entry (T : H →L[ℂ] H) (c d : ℤ) :
    (tp T (lp.single 2 c (1 : ℂ))) d = (T (lp.single 2 d (1 : ℂ))) c := by
  rw [tp_apply, lp.star_apply]
  have hs : star (lp.single (E := fun _ : ℤ => ℂ) 2 c (1 : ℂ)) = lp.single 2 c 1 := by
    ext i
    by_cases hi : i = c <;> simp [lp.star_apply, lp.single_apply, hi]
  rw [hs]
  have hc : ∀ (i : ℤ) (f : H), inner ℂ (lp.single 2 i (1 : ℂ)) f = f i := by
    intro i f
    rw [lp.inner_single_left]
    simp
  have h1 := hc d (ContinuousLinearMap.adjoint T (lp.single 2 c (1 : ℂ)))
  have h2 := hc c (T (lp.single 2 d (1 : ℂ)))
  have h3 : inner ℂ (lp.single 2 c (1 : ℂ)) (T (lp.single 2 d (1 : ℂ))) =
      inner ℂ (ContinuousLinearMap.adjoint T (lp.single 2 c (1 : ℂ))) (lp.single 2 d (1 : ℂ)) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
  rw [h2] at h3
  have h4 := congrArg (starRingEnd ℂ) h1
  rw [inner_conj_symm] at h4
  rw [← h3] at h4
  simpa using h4.symm

/-- The Bogoliubov relations: `α α^† - β β^† = 1`, `α^†α - β^T β̄ = 1` (both in norm form), and
`α β^T = β α^T`. -/
structure IsBogoliubov (α β : H →L[ℂ] H) : Prop where
  r1 : ∀ x : H, ‖ContinuousLinearMap.adjoint α x‖ ^ 2 =
    ‖x‖ ^ 2 + ‖ContinuousLinearMap.adjoint β x‖ ^ 2
  r2 : ∀ x : H, ‖α x‖ ^ 2 = ‖x‖ ^ 2 + ‖β (star x)‖ ^ 2
  r3 : α ∘L tp β = β ∘L tp α

/-- `α` is invertible. -/
theorem exists_inverse {α β : H →L[ℂ] H} (h : IsBogoliubov α β) :
    ∃ p : H →L[ℂ] H, p ∘L α = 1 ∧ α ∘L p = 1 := by
  have hlow : ∀ x : H, ‖x‖ ≤ ‖α x‖ := by
    intro x
    have := h.r2 x
    have h0 : ‖x‖ ^ 2 ≤ ‖α x‖ ^ 2 := by nlinarith [sq_nonneg ‖β (star x)‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h0
  have hinj : Function.Injective α := by
    intro x y hxy
    have := hlow (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hanti : AntilipschitzWith 1 α := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    have := hlow (x - y)
    rwa [map_sub] at this
  have hclosed : IsClosed (Set.range α) :=
    hanti.isClosed_range α.uniformContinuous
  have hlow' : ∀ x : H, ‖x‖ ≤ ‖ContinuousLinearMap.adjoint α x‖ := by
    intro x
    have := h.r1 x
    have h0 : ‖x‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint α x‖ ^ 2 := by
      nlinarith [sq_nonneg ‖ContinuousLinearMap.adjoint β x‖]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h0
  have hker : (ContinuousLinearMap.adjoint α : H →ₗ[ℂ] H).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : ContinuousLinearMap.adjoint α x = 0 := hx
    have := hlow' x
    rw [hx', norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hrange : (LinearMap.range (α : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    have h1 := ContinuousLinearMap.orthogonal_range α
    rw [hker] at h1
    exact h1
  have hsurj : LinearMap.range (α : H →ₗ[ℂ] H) = ⊤ := by
    have hc := (Submodule.topologicalClosure_eq_top_iff
      (K := LinearMap.range (α : H →ₗ[ℂ] H))).2 hrange
    have hcl : (LinearMap.range (α : H →ₗ[ℂ] H)).topologicalClosure =
        LinearMap.range (α : H →ₗ[ℂ] H) :=
      IsClosed.submodule_topologicalClosure_eq hclosed
    rw [hcl] at hc
    exact hc
  have hker0 : (α : H →ₗ[ℂ] H).ker = ⊥ := LinearMap.ker_eq_bot.2 hinj
  let e : H ≃L[ℂ] H := ContinuousLinearEquiv.ofBijective α hker0 hsurj
  refine ⟨(e.symm : H →L[ℂ] H), ?_, ?_⟩
  · ext x : 1
    have := e.symm_apply_apply x
    simpa [e, ContinuousLinearEquiv.coe_ofBijective] using this
  · ext x : 1
    have := e.apply_symm_apply x
    simpa [e, ContinuousLinearEquiv.coe_ofBijective] using this

/-- The kernel `K = α^{-1} β`: `α K = β` and `K^T = K`. -/
theorem exists_kernel {α β : H →L[ℂ] H} (h : IsBogoliubov α β) :
    ∃ K : H →L[ℂ] H, (∀ x : H, α (K x) = β x) ∧ tp K = K ∧ Function.Injective α := by
  obtain ⟨p, hpα, hαp⟩ := exists_inverse h
  have hpα' : ∀ x, p (α x) = x := fun x => by
    have := congrArg (fun T : H →L[ℂ] H => T x) hpα
    simpa using this
  have hαp' : ∀ x, α (p x) = x := fun x => by
    have := congrArg (fun T : H →L[ℂ] H => T x) hαp
    simpa using this
  have h1 : tp α ∘L tp p = 1 := by
    rw [← tp_comp, hpα, tp_one]
  have h1' : ∀ x, tp α (tp p x) = x := fun x => by
    have := congrArg (fun T : H →L[ℂ] H => T x) h1
    simpa using this
  refine ⟨p ∘L β, fun x => by simp [hαp'], ?_, fun x y hxy => by
    have := congrArg p hxy
    rwa [hpα', hpα'] at this⟩
  ext x : 1
  rw [tp_comp]
  simp only [ContinuousLinearMap.comp_apply]
  have h3 := congrArg (fun T : H →L[ℂ] H => T (tp p x)) h.r3
  simp only [ContinuousLinearMap.comp_apply, h1'] at h3
  calc tp β (tp p x) = p (α (tp β (tp p x))) := (hpα' _).symm
    _ = p (β x) := by rw [h3]

end QuantumNLS.Ext006BogoliubovAlg
#print axioms QuantumNLS.Ext006BogoliubovAlg.exists_inverse
#print axioms QuantumNLS.Ext006BogoliubovAlg.exists_kernel
