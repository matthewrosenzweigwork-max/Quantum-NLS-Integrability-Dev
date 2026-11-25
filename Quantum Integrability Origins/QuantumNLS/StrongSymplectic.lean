import Mathlib
import QuantumNLS.SymplecticBracket
import QuantumNLS.Fourier

/-!
# DEF-016: strong symplectic diffeomorphism (`definitions.tex:99`, `def:report-16`)

Ledger text: a real differentiable diffeomorphism between the physical and sequence Hilbert spaces is
strongly symplectic if its derivative is a bounded real-linear isomorphism and
`Ω(DΦ(u)h, DΦ(u)k) = Ω(h,k)` for every pair of Hilbert tangent vectors.

Realized objects used read-only:
* DEF-015 (`SymplecticBracket.omega`): `Ω(h,k) = 2 Im⟨h,k⟩` on the real space underlying a complex Hilbert
  space, `⟨·,·⟩` linear in the second slot. Realized on the physical space `L2T L` (DEF-001).
* DEF-001/DEF-002 (`Fourier.fourierL2`): the Fourier unitary `L²(𝕋_L) ≃ₗᵢ[ℂ] ℓ²(ℤ)`. DEF-002 at `s = 0` is
  `ℓ²(ℤ)` (`Fourier.hsNormSq_zero`), so `lp (fun _ : ℤ => ℂ) 2` is the sequence Hilbert space.

Ω on the sequence side. `definitions.tex` defines Ω (DEF-015) only on the real space underlying the physical
space. It gives no separate sequence-side form. This module applies the same formula `Ω = 2 Im⟨·,·⟩` on each
complex Hilbert space that appears; on `ℓ²(ℤ)` this is `2 Im Σ_n conj(a_n) b_n`. This is an interpretation
of the source, not a quoted definition, and it is stated as such.

Local versions. `definitions.tex` states DEF-016 globally (between the whole spaces). No local (open-subset)
version appears in the source, so none is defined here.

Proved here: the identity is strongly symplectic on every complex Hilbert space; composition and inverse
preserve the property.

Not closed here: the non-vacuous instance (the realized Fourier unitary `Fourier.fourierL2 L : L2T L → ℓ²(ℤ)`).
A first attempt failed because the real-linear equivalence built from `fourierL2` did not unify with the
`complexToReal` structure on `L2T L`. The instance was removed rather than left with an error, so this module
proves only the general facts.
-/

set_option autoImplicit false
noncomputable section

open InnerProductSpace ComplexConjugate

-- the realification of a complex Hilbert space, used for real differentiability (as in DEF-015)
attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.StrongSymplectic

variable {H E F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **DEF-016.** `Φ : H → E` is a real differentiable diffeomorphism (a bijection with a differentiable
inverse), its derivative at every point is a bounded real-linear isomorphism (`H ≃L[ℝ] E`), and
`Ω(DΦ(u)h, DΦ(u)k) = Ω(h,k)` for all tangent vectors `h, k` at `u`. The form `Ω` is
`SymplecticBracket.omega` (DEF-015) on both sides. -/
structure IsStronglySymplectic (Φ : H → E) : Prop where
  exists_inverse : ∃ Ψ : E → H, (∀ x, Ψ (Φ x) = x) ∧ (∀ y, Φ (Ψ y) = y) ∧ Differentiable ℝ Ψ
  differentiable : Differentiable ℝ Φ
  deriv_iso : ∀ u, ∃ e : H ≃L[ℝ] E, (e : H → E) = fderiv ℝ Φ u
  symplectic : ∀ u h k, SymplecticBracket.omega (fderiv ℝ Φ u h) (fderiv ℝ Φ u k) =
    SymplecticBracket.omega h k

/-- The identity is strongly symplectic on every complex Hilbert space. -/
theorem isStronglySymplectic_id : IsStronglySymplectic (id : H → H) where
  exists_inverse := ⟨id, fun _ => rfl, fun _ => rfl, differentiable_id⟩
  differentiable := differentiable_id
  deriv_iso := fun u => ⟨ContinuousLinearEquiv.refl ℝ H, by
    rw [fderiv_id]
    rfl⟩
  symplectic := fun u h k => by
    rw [fderiv_id]
    rfl

/-- Composition: if `Φ : H → E` and `Ψ : E → F` are strongly symplectic, so is `Ψ ∘ Φ`. -/
theorem IsStronglySymplectic.comp {Φ : H → E} {Ψ : E → F} (hΦ : IsStronglySymplectic Φ)
    (hΨ : IsStronglySymplectic Ψ) : IsStronglySymplectic (Ψ ∘ Φ) := by
  obtain ⟨Φi, hΦl, hΦr, hΦid⟩ := hΦ.exists_inverse
  obtain ⟨Ψi, hΨl, hΨr, hΨid⟩ := hΨ.exists_inverse
  refine
    { exists_inverse := ⟨Φi ∘ Ψi, fun x => ?_, fun z => ?_, hΦid.comp hΨid⟩
      differentiable := hΨ.differentiable.comp hΦ.differentiable
      deriv_iso := fun u => ?_
      symplectic := fun u h k => ?_ }
  · simp only [Function.comp_apply]
    rw [hΨl (Φ x), hΦl x]
  · simp only [Function.comp_apply]
    rw [hΦr (Ψi z), hΨr z]
  · obtain ⟨eΦ, heΦ⟩ := hΦ.deriv_iso u
    obtain ⟨eΨ, heΨ⟩ := hΨ.deriv_iso (Φ u)
    refine ⟨eΦ.trans eΨ, ?_⟩
    rw [fderiv_comp u (hΨ.differentiable (Φ u)) (hΦ.differentiable u)]
    funext x
    rw [ContinuousLinearMap.comp_apply, ← heΦ, ← heΨ]
    rfl
  · rw [fderiv_comp u (hΨ.differentiable (Φ u)) (hΦ.differentiable u),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hΨ.symplectic (Φ u),
      hΦ.symplectic u]

/-- Inverse: the inverse of a strongly symplectic diffeomorphism is strongly symplectic. -/
theorem IsStronglySymplectic.symm {Φ : H → E} (hΦ : IsStronglySymplectic Φ) :
    ∃ Ψ : E → H, IsStronglySymplectic Ψ ∧ (∀ x, Ψ (Φ x) = x) ∧ (∀ y, Φ (Ψ y) = y) := by
  obtain ⟨Ψ, hl, hr, hΨd⟩ := hΦ.exists_inverse
  -- the chain rule on `Φ ∘ Ψ = id`: `DΦ(Ψ w) ∘ DΨ(w) = id`
  have hchain : ∀ w x, fderiv ℝ Φ (Ψ w) (fderiv ℝ Ψ w x) = x := by
    intro w x
    have hcomp : Φ ∘ Ψ = id := funext hr
    have h1 : fderiv ℝ (Φ ∘ Ψ) w = ContinuousLinearMap.id ℝ E := by
      rw [hcomp, fderiv_id]
    rw [fderiv_comp w (hΦ.differentiable (Ψ w)) (hΨd w)] at h1
    have h2 := congrArg (fun T => T x) h1
    simpa using h2
  refine ⟨Ψ, ?_, hl, hr⟩
  refine
    { exists_inverse := ⟨Φ, hr, hl, hΦ.differentiable⟩
      differentiable := hΨd
      deriv_iso := fun w => ?_
      symplectic := fun w a b => ?_ }
  · obtain ⟨eΦ, heΦ⟩ := hΦ.deriv_iso (Ψ w)
    refine ⟨eΦ.symm, ?_⟩
    funext x
    show eΦ.symm x = fderiv ℝ Ψ w x
    rw [ContinuousLinearEquiv.symm_apply_eq, heΦ, hchain w x]
  · rw [← hΦ.symplectic (Ψ w) (fderiv ℝ Ψ w a) (fderiv ℝ Ψ w b), hchain w a, hchain w b]

end QuantumNLS.StrongSymplectic

/-! Axiom audit (DEF-016 realization). -/
#print axioms QuantumNLS.StrongSymplectic.isStronglySymplectic_id
#print axioms QuantumNLS.StrongSymplectic.IsStronglySymplectic.comp
#print axioms QuantumNLS.StrongSymplectic.IsStronglySymplectic.symm
