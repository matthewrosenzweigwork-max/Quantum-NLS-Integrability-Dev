import NlsGge.Hierarchy.RiccatiPeriodicSolutionAsymptotic38
import NlsGge.Sobolev.PeriodicBridge
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # R3c piece P1a: resolvent core (transpose resolvent, commutation with `∂`, one-step expansion)

Shared definitions of the R3c pieces, and the first-order calculus of the resolvent
`R g = resolv38 η g = (∂ + 2η)⁻¹ g` on 1-periodic functions and of its transpose
`Rt g = (−∂ + 2η)⁻¹ g` (defined by reflection). -/

/-- transpose resolvent, by reflection -/
def resolvT38 (η : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ := resolv38 η (fun y => g (-y)) (-x)

/-- bilinear pairing (no conjugation) on `[0,1]` -/
def pair38 (f g : ℝ → ℂ) : ℂ := ∫ x in (0:ℝ)..1, f x * g x

/-- squared `L²(0,1)` norm -/
def l2sq38 (f : ℝ → ℂ) : ℝ := ∫ x in (0:ℝ)..1, ‖f x‖ ^ 2

/-- standing regularity: continuous, 1-periodic, with continuous periodic derivative `f'` -/
structure PerC1_38 (f f' : ℝ → ℂ) : Prop where
  cont : Continuous f
  cont' : Continuous f'
  per : Function.Periodic f 1
  per' : Function.Periodic f' 1
  deriv : ∀ x, HasDerivAt f (f' x) x

/-! ## Reflection -/

theorem periodic_comp_neg38 {g : ℝ → ℂ} (hp : Function.Periodic g 1) :
    Function.Periodic (fun y => g (-y)) 1 := by
  intro y
  have := hp (-(y + 1))
  simp only [neg_add_rev] at this
  have h2 : -(y + 1) + 1 = -y := by ring
  have h3 : -(y + 1) = -y + -1 := by ring
  show g (-(y + 1)) = g (-y)
  rw [h3]
  have := hp (-y + -1)
  rw [show -y + -1 + 1 = -y by ring] at this
  exact this.symm

theorem resolv38_hasDerivAt_periodic38 {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) (x : ℝ) :
    HasDerivAt (resolv38 η g) (-(2 * (η : ℂ)) * resolv38 η g x + g x) x := by
  obtain ⟨x₀, hx₀⟩ := periodic_norm_attains38 hg hp
  exact resolv38_hasDerivAt hη hg hx₀ x

theorem resolvT38_hasDerivAt {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) (x : ℝ) :
    HasDerivAt (resolvT38 η g) (2 * (η : ℂ) * resolvT38 η g x - g x) x := by
  have hgc : Continuous (fun y => g (-y)) := hg.comp continuous_neg
  have h1 := resolv38_hasDerivAt_periodic38 hη hgc (periodic_comp_neg38 hp) (-x)
  have h2 : HasDerivAt (fun y : ℝ => -y) (-1) x := by simpa using (hasDerivAt_neg x)
  have h3 := h1.scomp x h2
  unfold resolvT38
  refine h3.congr_deriv ?_
  simp only [neg_neg, neg_smul, one_smul]
  ring

theorem resolvT38_periodic {η : ℝ} {g : ℝ → ℂ} (hp : Function.Periodic g 1) :
    Function.Periodic (resolvT38 η g) 1 := by
  intro x
  have h := resolv38_periodic (η := η) (periodic_comp_neg38 hp) (-x - 1)
  unfold resolvT38
  rw [show -(x + 1) = -x - 1 by ring]
  rw [show -x - 1 + 1 = -x by ring] at h
  exact h.symm

theorem resolvT38_bound {η : ℝ} (hη : 0 < η) {g : ℝ → ℂ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (x : ℝ) : ‖resolvT38 η g x‖ ≤ B / (2 * η) :=
  resolv38_bound hη (hg.comp continuous_neg) (fun y => hB (-y)) (-x)

/-! ## Commutation with `∂` -/

theorem resolv38_of_deriv38 {η : ℝ} (hη : 0 < η) {g g' : ℝ → ℂ} (h : PerC1_38 g g') (x : ℝ) :
    resolv38 η g' x = -(2 * (η : ℂ)) * resolv38 η g x + g x := by
  set D : ℝ → ℂ := fun y => resolv38 η g' y - (-(2 * (η : ℂ)) * resolv38 η g y + g y) with hD
  have hd1 := resolv38_hasDerivAt_periodic38 hη h.cont' h.per'
  have hd2 := resolv38_hasDerivAt_periodic38 hη h.cont h.per
  have hdD : ∀ y, HasDerivAt D (-(2 * (η : ℂ)) * D y) y := by
    intro y
    have h3 := ((hd2 y).const_mul (-(2 * (η : ℂ)))).add (h.deriv y)
    have h4 := (hd1 y).sub h3
    convert h4 using 1
    simp only [hD]
    ring
  have hpD : Function.Periodic D 1 := by
    intro y
    simp only [hD]
    rw [resolv38_periodic h.per' y, resolv38_periodic h.per y, h.per y]
  have := periodic_ode_zero hη hdD hpD x
  simp only [hD] at this
  exact sub_eq_zero.mp this

theorem PerC1_38.comp_neg {g g' : ℝ → ℂ} (h : PerC1_38 g g') :
    PerC1_38 (fun y => g (-y)) (fun y => -g' (-y)) where
  cont := h.cont.comp continuous_neg
  cont' := (h.cont'.comp continuous_neg).neg
  per := periodic_comp_neg38 h.per
  per' := by
    intro y
    show -g' (-(y + 1)) = -g' (-y)
    rw [show -(y + 1) = -y + -1 by ring]
    have h2 := h.per' (-y + -1)
    rw [show -y + -1 + 1 = -y by ring] at h2
    rw [← h2]
  deriv := by
    intro x
    have h2 : HasDerivAt (fun y : ℝ => -y) (-1) x := by simpa using (hasDerivAt_neg x)
    have h3 := (h.deriv (-x)).scomp x h2
    refine h3.congr_deriv ?_
    simp only [neg_smul, one_smul]

theorem resolv38_neg38 (η : ℝ) (g : ℝ → ℂ) (x : ℝ) :
    resolv38 η (fun y => -g y) x = -resolv38 η g x := by
  unfold resolv38 resInt38
  simp only [smul_neg, integral_neg]

theorem resolvT38_of_deriv38 {η : ℝ} (hη : 0 < η) {g g' : ℝ → ℂ} (h : PerC1_38 g g') (x : ℝ) :
    resolvT38 η g' x = 2 * (η : ℂ) * resolvT38 η g x - g x := by
  have h1 := resolv38_of_deriv38 hη h.comp_neg (-x)
  rw [resolv38_neg38 η (fun y => g' (-y)) (-x)] at h1
  unfold resolvT38
  rw [neg_neg] at h1
  have : resolv38 η (fun y => g' (-y)) (-x) = -(-(2 * (η : ℂ)) * resolv38 η (fun y => g (-y)) (-x)
      + g x) := by
    rw [← h1]; ring
  rw [this]; ring

/-- L4 (one-step expansion). -/
theorem resolv38_expand38 {η : ℝ} (hη : 0 < η) {g g' : ℝ → ℂ} (h : PerC1_38 g g') (x : ℝ) :
    resolv38 η g x = g x / (2 * η) - resolv38 η g' x / (2 * η) := by
  have h1 := resolv38_of_deriv38 hη h x
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  rw [h1]
  field_simp
  ring

theorem resolvT38_expand38 {η : ℝ} (hη : 0 < η) {g g' : ℝ → ℂ} (h : PerC1_38 g g') (x : ℝ) :
    resolvT38 η g x = g x / (2 * η) + resolvT38 η g' x / (2 * η) := by
  have h1 := resolvT38_of_deriv38 hη h x
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  rw [h1]
  field_simp
  ring

/-! ## `PerC1_38` is preserved by the resolvents -/

theorem perC1_resolv38 {η : ℝ} (hη : 0 < η) {g g' : ℝ → ℂ} (h : PerC1_38 g g') :
    PerC1_38 (resolv38 η g) (resolv38 η g') where
  cont := continuous_iff_continuousAt.mpr fun x =>
    (resolv38_hasDerivAt_periodic38 hη h.cont h.per x).continuousAt
  cont' := continuous_iff_continuousAt.mpr fun x =>
    (resolv38_hasDerivAt_periodic38 hη h.cont' h.per' x).continuousAt
  per := resolv38_periodic h.per
  per' := resolv38_periodic h.per'
  deriv := fun x => by
    rw [resolv38_of_deriv38 hη h x]
    exact resolv38_hasDerivAt_periodic38 hη h.cont h.per x

theorem perC1_resolvT38 {η : ℝ} (hη : 0 < η) {g g' : ℝ → ℂ} (h : PerC1_38 g g') :
    PerC1_38 (resolvT38 η g) (resolvT38 η g') where
  cont := continuous_iff_continuousAt.mpr fun x =>
    (resolvT38_hasDerivAt hη h.cont h.per x).continuousAt
  cont' := continuous_iff_continuousAt.mpr fun x =>
    (resolvT38_hasDerivAt hη h.cont' h.per' x).continuousAt
  per := resolvT38_periodic h.per
  per' := resolvT38_periodic h.per'
  deriv := fun x => by
    rw [resolvT38_of_deriv38 hη h x]
    exact resolvT38_hasDerivAt hη h.cont h.per x

/-! ## Planes and algebra of `PerC1_38` -/

theorem perC1_plane38 (N : ℕ) (z : FourierPlane N) :
    PerC1_38 (planeReal N z) (planeReal N (derivativePlane N z)) where
  cont := (contDiff_planeReal N z).continuous
  cont' := (contDiff_planeReal N (derivativePlane N z)).continuous
  per := planeReal_periodic N z
  per' := planeReal_periodic N (derivativePlane N z)
  deriv := hasDerivAt_planeReal N z

theorem PerC1_38.star {f f' : ℝ → ℂ} (h : PerC1_38 f f') :
    PerC1_38 (fun y => star (f y)) (fun y => star (f' y)) where
  cont := h.cont.star
  cont' := h.cont'.star
  per := fun y => by simp only [h.per y]
  per' := fun y => by simp only [h.per' y]
  deriv := fun x => (h.deriv x).star

theorem PerC1_38.neg {f f' : ℝ → ℂ} (h : PerC1_38 f f') :
    PerC1_38 (fun y => -f y) (fun y => -f' y) where
  cont := h.cont.neg
  cont' := h.cont'.neg
  per := fun y => by simp only [h.per y]
  per' := fun y => by simp only [h.per' y]
  deriv := fun x => (h.deriv x).neg

theorem PerC1_38.add {f f' g g' : ℝ → ℂ} (hf : PerC1_38 f f') (hg : PerC1_38 g g') :
    PerC1_38 (fun y => f y + g y) (fun y => f' y + g' y) where
  cont := hf.cont.add hg.cont
  cont' := hf.cont'.add hg.cont'
  per := fun y => by simp only [hf.per y, hg.per y]
  per' := fun y => by simp only [hf.per' y, hg.per' y]
  deriv := fun x => (hf.deriv x).add (hg.deriv x)

theorem PerC1_38.sub {f f' g g' : ℝ → ℂ} (hf : PerC1_38 f f') (hg : PerC1_38 g g') :
    PerC1_38 (fun y => f y - g y) (fun y => f' y - g' y) where
  cont := hf.cont.sub hg.cont
  cont' := hf.cont'.sub hg.cont'
  per := fun y => by simp only [hf.per y, hg.per y]
  per' := fun y => by simp only [hf.per' y, hg.per' y]
  deriv := fun x => (hf.deriv x).sub (hg.deriv x)

/-- Leibniz rule. -/
theorem PerC1_38.mul {f f' g g' : ℝ → ℂ} (hf : PerC1_38 f f') (hg : PerC1_38 g g') :
    PerC1_38 (fun y => f y * g y) (fun y => f' y * g y + f y * g' y) where
  cont := hf.cont.mul hg.cont
  cont' := (hf.cont'.mul hg.cont).add (hf.cont.mul hg.cont')
  per := fun y => by simp only [hf.per y, hg.per y]
  per' := fun y => by simp only [hf.per' y, hg.per' y, hf.per y, hg.per y]
  deriv := fun x => (hf.deriv x).mul (hg.deriv x)

theorem PerC1_38.const_mul {f f' : ℝ → ℂ} (c : ℂ) (hf : PerC1_38 f f') :
    PerC1_38 (fun y => c * f y) (fun y => c * f' y) where
  cont := continuous_const.mul hf.cont
  cont' := continuous_const.mul hf.cont'
  per := fun y => by simp only [hf.per y]
  per' := fun y => by simp only [hf.per' y]
  deriv := fun x => (hf.deriv x).const_mul c

theorem PerC1_38.mul_const {f f' : ℝ → ℂ} (c : ℂ) (hf : PerC1_38 f f') :
    PerC1_38 (fun y => f y * c) (fun y => f' y * c) where
  cont := hf.cont.mul continuous_const
  cont' := hf.cont'.mul continuous_const
  per := fun y => by simp only [hf.per y]
  per' := fun y => by simp only [hf.per' y]
  deriv := fun x => (hf.deriv x).mul_const c

theorem PerC1_38.pow_two {f f' : ℝ → ℂ} (hf : PerC1_38 f f') :
    PerC1_38 (fun y => f y ^ 2) (fun y => 2 * f y * f' y) where
  cont := hf.cont.pow 2
  cont' := (continuous_const.mul hf.cont).mul hf.cont'
  per := fun y => by simp only [hf.per y]
  per' := fun y => by simp only [hf.per' y, hf.per y]
  deriv := fun x => by
    have := (hf.deriv x).pow 2
    convert this using 1
    simp

end NlsGge.SpectralFoundations
end
