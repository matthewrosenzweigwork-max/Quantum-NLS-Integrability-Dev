import NlsGge.Atomic.DM.DM009
import NlsGge.Atomic.LIB.LIB041
import NlsGge.Atomic.LIB.LIB042

/-!
# G1-103 M3(a): the spectral points of the source realization are finite in every bounded set

Pro round 10 (commit 178f84d6), section 8, M3: compact-resolvent discreteness. If `R(z₀)` is the
(compact) resolvent at a resolvent point `z₀`, then `1 + (λ - z₀) R(z₀)` invertible gives a bounded
inverse of `λ - A` (explicit formula `R N`, `N = (1 + (λ - z₀) R)⁻¹`), and the non-invertible
`t = z₀ - λ` of the compact operator `R` in a bounded set are finite
(`NlsGge.DM009Riesz.compact_finite_bounded_nonunit`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace NlsGge.Atomic.G1103Spec
open NlsGge.Schur NlsGge.Atomic.Interval
open NlsGge.Atomic.LIB033 NlsGge.Atomic.LIB038 NlsGge.Atomic.LIB040
open NlsGge.Atomic.LIB041 NlsGge.Atomic.LIB042

/-- A bounded inverse at `lam` from invertibility of `1 + (lam - z₀) R(z₀)`. -/
theorem hasBoundedResolvent_of_isUnit
    (A : SourcePairL2 →ₗ.[ℂ] SourcePairL2) {z₀ : ℂ} (hz₀ : HasBoundedResolvent A z₀) (lam : ℂ)
    (hu : IsUnit ((1 : SourcePairL2 →L[ℂ] SourcePairL2) +
      (lam - z₀) • resolventFamily A z₀)) :
    HasBoundedResolvent A lam := by
  obtain ⟨u, hu'⟩ := hu
  set R := resolventFamily A z₀ with hR
  set M : SourcePairL2 →L[ℂ] SourcePairL2 := 1 + (lam - z₀) • R with hM
  set N : SourcePairL2 →L[ℂ] SourcePairL2 := ((u⁻¹ : (SourcePairL2 →L[ℂ] SourcePairL2)ˣ) :
    SourcePairL2 →L[ℂ] SourcePairL2) with hN
  have hMN : ∀ f, M (N f) = f := by
    intro f
    have h := congrArg (fun L : SourcePairL2 →L[ℂ] SourcePairL2 => L f)
      (show (u : SourcePairL2 →L[ℂ] SourcePairL2) * ((u⁻¹ : (SourcePairL2 →L[ℂ] SourcePairL2)ˣ) :
        SourcePairL2 →L[ℂ] SourcePairL2) = 1 from u.mul_inv)
    rw [hu'] at h
    simpa [hN] using h
  have hNM : ∀ f, N (M f) = f := by
    intro f
    have h := congrArg (fun L : SourcePairL2 →L[ℂ] SourcePairL2 => L f)
      (show ((u⁻¹ : (SourcePairL2 →L[ℂ] SourcePairL2)ˣ) : SourcePairL2 →L[ℂ] SourcePairL2) *
        (u : SourcePairL2 →L[ℂ] SourcePairL2) = 1 from u.inv_mul)
    rw [hu'] at h
    simpa [hN] using h
  have hRspec := resolventFamily_eq A z₀ hz₀
  have hRr : ∀ f : SourcePairL2, ∃ hf : R f ∈ A.domain, z₀ • R f - A ⟨R f, hf⟩ = f := by
    intro f; rw [hR, hRspec]; exact hz₀.choose_spec.1 f
  have hRl : ∀ x : A.domain, R (z₀ • (x : SourcePairL2) - A x) = x := by
    intro x; rw [hR, hRspec]; exact hz₀.choose_spec.2 x
  refine ⟨R.comp N, ?_, ?_⟩
  · intro f
    obtain ⟨hf, hact⟩ := hRr (N f)
    refine ⟨hf, ?_⟩
    change lam • R (N f) - A ⟨R (N f), hf⟩ = f
    have h1 : lam • R (N f) - A ⟨R (N f), hf⟩ =
        (z₀ • R (N f) - A ⟨R (N f), hf⟩) + (lam - z₀) • R (N f) := by module
    rw [h1, hact]
    have h2 := hMN f
    simp only [hM, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply] at h2
    exact h2
  · intro x
    change R (N (lam • (x : SourcePairL2) - A x)) = x
    have h1 : lam • (x : SourcePairL2) - A x =
        M (z₀ • (x : SourcePairL2) - A x) := by
      simp only [hM, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply, hRl]
      module
    rw [h1, hNM, hRl]

/-- Finiteness of the non-resolvent points in every bounded set. -/
theorem zs_spectrum_finite_in_ball (φ : SourcePairL2) (bc : ZSBoundaryCondition) {z₀ : ℂ}
    (hz₀ : HasBoundedResolvent (zsRealization φ bc) z₀) (r : ℝ) :
    {lam : ℂ | ‖lam‖ ≤ r ∧ ¬ HasBoundedResolvent (zsRealization φ bc) lam}.Finite := by
  have hcomp : IsCompactOperator (zsResolventFamily φ bc z₀) := zsResolventFamily_isCompact φ bc z₀
  have hfin := NlsGge.DM009Riesz.compact_finite_bounded_nonunit (zsResolventFamily φ bc z₀)
    hcomp (‖z₀‖ + r)
  refine (hfin.image (fun t : ℂ => z₀ - t)).subset ?_
  rintro lam ⟨hlam, hnot⟩
  refine ⟨z₀ - lam, ⟨?_, ?_⟩, by ring⟩
  · calc ‖z₀ - lam‖ ≤ ‖z₀‖ + ‖lam‖ := norm_sub_le _ _
      _ ≤ ‖z₀‖ + r := by linarith
  · intro hu
    apply hnot
    refine hasBoundedResolvent_of_isUnit (zsRealization φ bc) hz₀ lam ?_
    have : (1 : SourcePairL2 →L[ℂ] SourcePairL2) - (z₀ - lam) • zsResolventFamily φ bc z₀ =
        1 + (lam - z₀) • resolventFamily (zsRealization φ bc) z₀ := by
      have e : lam - z₀ = -(z₀ - lam) := by ring
      rw [show zsResolventFamily φ bc z₀ = resolventFamily (zsRealization φ bc) z₀ from rfl,
        e]
      module
    rw [← this]; exact hu

end NlsGge.Atomic.G1103Spec

end
