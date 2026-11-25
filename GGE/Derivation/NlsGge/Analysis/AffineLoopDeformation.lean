import NlsGge.Analysis.MixedLoopDeformation
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.Ring

set_option autoImplicit false
open Set Metric MeasureTheory
namespace NlsGge.Analysis.AffineLoopDeformation
noncomputable section

def point (a b : ℝ → ℂ) (t θ : ℝ) : ℂ := a θ + (t : ℂ) * b θ

def tangent (a' b' : ℝ → ℂ) (t θ : ℝ) : ℂ := a' θ + (t : ℂ) * b' θ

def pullback (f : ℂ → ℂ) (a b a' b' : ℝ → ℂ) (t θ : ℝ) : ℂ :=
  tangent a' b' t θ * f (point a b t θ)

def primitive (f : ℂ → ℂ) (a b : ℝ → ℂ) (t θ : ℝ) : ℂ :=
  f (point a b t θ) * b θ

def mixed (f : ℂ → ℂ) (a b a' b' : ℝ → ℂ) (t θ : ℝ) : ℂ :=
  b' θ * f (point a b t θ) +
    tangent a' b' t θ * (deriv f (point a b t θ) * b θ)

theorem point_continuous {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun p : ℝ × ℝ => point a b p.1 p.2) :=
  (ha.comp continuous_snd).add
    ((Complex.continuous_ofReal.comp continuous_fst).mul (hb.comp continuous_snd))

theorem point_derivatives {a b a' b' : ℝ → ℂ}
    (ha : ∀ θ, HasDerivAt a (a' θ) θ) (hb : ∀ θ, HasDerivAt b (b' θ) θ)
    (t θ : ℝ) :
    HasDerivAt (fun s : ℝ => point a b s θ) (b θ) t ∧
      HasDerivAt (point a b t) (tangent a' b' t θ) θ := by
  constructor
  · convert (hasDerivAt_const t (a θ)).add
      ((hasDerivAt_id t).ofReal_comp.mul_const (b θ)) using 1
    · rfl
    · simp
  · convert (ha θ).add ((hb θ).const_mul (t : ℂ)) using 1
    · rfl
    · rfl

theorem mixed_derivatives {f : ℂ → ℂ} {a b a' b' : ℝ → ℂ} {t θ : ℝ}
    (ha : ∀ θ, HasDerivAt a (a' θ) θ) (hb : ∀ θ, HasDerivAt b (b' θ) θ)
    (hf : AnalyticAt ℂ f (point a b t θ)) :
    HasDerivAt (fun s : ℝ => pullback f a b a' b' s θ) (mixed f a b a' b' t θ) t ∧
      HasDerivAt (primitive f a b t) (mixed f a b a' b' t θ) θ := by
  obtain ⟨ht, hθ⟩ := point_derivatives ha hb t θ
  have hft := hf.differentiableAt.hasDerivAt.scomp t ht
  have hfθ := hf.differentiableAt.hasDerivAt.scomp θ hθ
  simp only [smul_eq_mul, Function.comp_def] at hft hfθ
  have hc : HasDerivAt (fun s : ℝ => tangent a' b' s θ) (b' θ) t := by
    convert (hasDerivAt_const t (a' θ)).add
      ((hasDerivAt_id t).ofReal_comp.mul_const (b' θ)) using 1
    · rfl
    · simp
  constructor
  · convert hc.mul hft using 1
    · rfl
    · dsimp only [mixed]
      ring
  · convert hfθ.mul (hb θ) using 1
    · rfl
    · dsimp only [mixed]
      ring

theorem regularity {Ω : Set ℂ} {f : ℂ → ℂ} {a b a' b' : ℝ → ℂ} {U V : Set ℝ}
    (hf : AnalyticOnNhd ℂ f Ω) (ha : Continuous a) (hb : Continuous b)
    (ha' : Continuous a') (hb' : Continuous b')
    (hdom : ∀ t ∈ U, ∀ θ ∈ V, point a b t θ ∈ Ω) :
    ContinuousOn (Function.uncurry (pullback f a b a' b')) (U ×ˢ V) ∧
      ContinuousOn (Function.uncurry (mixed f a b a' b')) (U ×ˢ V) := by
  have hz := point_continuous ha hb
  have hF : ContinuousOn (fun p : ℝ × ℝ => f (point a b p.1 p.2)) (U ×ˢ V) :=
    hf.continuousOn.comp hz.continuousOn (fun p hp => hdom p.1 hp.1 p.2 hp.2)
  have hF' : ContinuousOn (fun p : ℝ × ℝ => deriv f (point a b p.1 p.2)) (U ×ˢ V) :=
    hf.deriv.continuousOn.comp hz.continuousOn (fun p hp => hdom p.1 hp.1 p.2 hp.2)
  have ht : Continuous (fun p : ℝ × ℝ => tangent a' b' p.1 p.2) :=
    point_continuous ha' hb'
  have hH := ht.continuousOn.mul hF
  have hD := ((hb'.comp continuous_snd).continuousOn.mul hF).add
    (ht.continuousOn.mul (hF'.mul (hb.comp continuous_snd).continuousOn))
  exact ⟨hH, hD⟩

theorem affine_closed_loop_integral_eq {Ω : Set ℂ} {f : ℂ → ℂ}
    {a b a' b' : ℝ → ℂ} (hΩ : IsOpen Ω) (hf : AnalyticOnNhd ℂ f Ω)
    (ha : ∀ θ, HasDerivAt a (a' θ) θ) (hb : ∀ θ, HasDerivAt b (b' θ) θ)
    (ha' : Continuous a') (hb' : Continuous b')
    (haend : a (2 * Real.pi) = a 0) (hbend : b (2 * Real.pi) = b 0)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), point a b t θ ∈ Ω) :
    IntervalIntegrable (pullback f a b a' b' 0) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (pullback f a b a' b' 1) volume 0 (2 * Real.pi) ∧
      (∫ θ in (0 : ℝ)..2 * Real.pi, pullback f a b a' b' 0 θ) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, pullback f a b a' b' 1 θ := by
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun θ => (ha θ).continuousAt)
  have hbc : Continuous b := continuous_iff_continuousAt.mpr (fun θ => (hb θ).continuousAt)
  obtain ⟨U, V, hU, _, htU, hθV, hUV⟩ :=
    generalized_tube_lemma (s := Icc (0 : ℝ) 1) isCompact_Icc
      (t := Icc (0 : ℝ) (2 * Real.pi)) isCompact_Icc
      (hΩ.preimage (point_continuous hac hbc))
      (by rintro ⟨t, θ⟩ ⟨ht, hθ⟩; exact hdom t ht θ hθ)
  have hmap : ∀ t ∈ U, ∀ θ ∈ V, point a b t θ ∈ Ω :=
    fun t ht θ hθ => hUV (show (t, θ) ∈ U ×ˢ V from ⟨ht, hθ⟩)
  have hr := regularity hf hac hbc ha' hb' hmap
  apply NlsGge.Analysis.MixedLoopDeformation.integral_eq_of_mixed_derivative hU htU hθV hr.1 hr.2
  · intro t ht θ hθ
    exact (mixed_derivatives ha hb (hf _ (hmap t ht θ hθ))).1
  · intro t ht θ hθ
    exact (mixed_derivatives ha hb (hf _ (hmap t ht θ hθ))).2
  · intro t _
    simp only [primitive, point, haend, hbend]

end
end NlsGge.Analysis.AffineLoopDeformation
