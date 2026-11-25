import Mathlib
import QuantumNLS.ResetNormalizationUniqueness

/-!
# LOCAL-022 interface bindings: physical reflection-conjugation and the ball convention

Source: `source/chapters/local/local_covariance.tex` lines 219 ff, `thm:reset-normalization-uniqueness`
(`\ReportID{LOCAL-022}`).  Imports the frozen `ResetNormalizationUniqueness` (sha256 a0abd4d2...) read-only
and closes the bindings Terra r100 flagged:

## (a) The physical reflection-conjugation map (constructed, not abstract)
`Cphys L : L²(𝕋_L) →ₗᵢ[ℝ] L²(𝕋_L)`, `C_phys u = \overline{u(-·)}`, built as `star ∘ reflectR`, where
`reflectR = Lp.compMeasurePreservingₗᵢ ℝ (x ↦ -x) (negMP L)` (the negation on `AddCircle L` preserves the
mass-`L` Haar measure) and `star` is the pointwise conjugation on `Lp ℂ 2`.  Proved: `coeFn_Cphys`
(`C_phys u = conj ∘ u ∘ neg` a.e.), `Cphys_Cphys` (involution), `norm_Cphys` (isometry; it is conjugate-linear,
i.e. an `ℝ`-linear isometry), and `fourier_Cphys`: `𝓕(C_phys u)_n = conj(𝓕(u)_n)`, via the proved
`Fourier.coeff_conj_reflect`.  `reset_normalization_uniqueness_phys` restates the uniqueness theorem with
`C := C_phys` and **no abstract-`C` hypothesis**.

## (c) The ball convention
The source's "the same full `L²` ball onto the same sequence ball" is read as *equal radius `r`*, the only
reading compatible with `‖𝓕u‖ = ‖u‖`: `fourierL2_image_ball` (`𝓕` maps `B_r(L²)` onto `B_r(ℓ²)`) and
`isStronglySymplecticOn_fourier` (the reference chart `𝓕` is canonical for that pair).  The local reading of
"canonical" (`IsStronglySymplecticOn`, DEF-016 restricted to open sets) is justified by
`IsStronglySymplecticOn.of_global`: a *global* strongly symplectic map (DEF-016 as printed) that preserves
the norm (the chart identity `∑|w_n(u)|² = ‖u‖²` of `core/coordinate_conventions.tex`) is canonical on the
ball of every radius.  `reset_normalization_uniqueness_global` then needs no ball at all: two global
DEF-016 charts, norm-preserving, analytic, with equal squared moduli, derivative `𝓕` at zero and
`C_phys`-intertwining, coincide everywhere.

## (b) The only remaining binding (not attempted, pending DEF-014)
The indexed masses `q_n` are an abstract family `q : ℤ → L² → ℝ` (only `q_n(0) = 0` and
`‖Φ_i(u)_n‖² = q_n(u)` are used).  Pinning `q_n(u)` to the mass `M_{κ,u}((b_{n-1},b_n))` of the scalar
spectral measure needs DEF-014, which is not realized in this repository.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open InnerProductSpace ComplexConjugate Filter Topology
open scoped ENNReal

set_option autoImplicit false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.ResetNormalizationUniqueness

section Phys

open MeasureTheory AddCircle

variable (L : ℝ) [Fact (0 < L)]

/-- Negation `x ↦ -x` on `𝕋_L` preserves the Haar (Lebesgue, mass `L`) measure. -/
theorem negMP : MeasurePreserving (fun x : AddCircle L => -x) (volume : Measure (AddCircle L))
    (volume : Measure (AddCircle L)) :=
  Measure.measurePreserving_neg _

/-- The reflection `u ↦ u(-·)` on `L²(𝕋_L)` (`ℝ`-linear isometry). -/
def reflectR : Lp ℂ 2 (volume : Measure (AddCircle L)) →ₗᵢ[ℝ] Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : AddCircle L => -x) (negMP L)

lemma coeFn_reflectR (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ⇑(reflectR L u) =ᵐ[volume] fun x => u (-x) :=
  Lp.coeFn_compMeasurePreserving u (negMP L)

lemma coeFn_cj (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ⇑(star u) =ᵐ[volume] fun x => conj (u x) := by
  filter_upwards [Lp.coeFn_star u] with x hx
  rw [hx]; rfl

lemma norm_cj (u : Lp ℂ 2 (volume : Measure (AddCircle L))) : ‖star u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  exact (eLpNorm_congr_ae (Lp.coeFn_star u)).trans eLpNorm_star

/-- **The physical reflection-conjugation** `C_phys u = \overline{u(-·)}` on `L²(𝕋_L)`: a conjugate-linear
isometric map (an `ℝ`-linear isometry), built as `star ∘ (u ↦ u ∘ neg)` with `Lp.compMeasurePreserving`
and the pointwise `Lp` `star`. -/
def Cphys : Lp ℂ 2 (volume : Measure (AddCircle L)) →ₗᵢ[ℝ] Lp ℂ 2 (volume : Measure (AddCircle L)) where
  toFun u := star (reflectR L u)
  map_add' a b := by
    apply Lp.ext
    rw [map_add]
    filter_upwards [Lp.coeFn_star (reflectR L a + reflectR L b), Lp.coeFn_add (reflectR L a) (reflectR L b),
      Lp.coeFn_add (star (reflectR L a)) (star (reflectR L b)), Lp.coeFn_star (reflectR L a),
      Lp.coeFn_star (reflectR L b)] with x h1 h2 h3 h4 h5
    simp only [h1, h3, h4, h5, Pi.star_apply, h2, Pi.add_apply, star_add]
  map_smul' r a := by
    apply Lp.ext
    rw [map_smul]
    filter_upwards [Lp.coeFn_star (r • reflectR L a), Lp.coeFn_smul r (reflectR L a),
      Lp.coeFn_smul r (star (reflectR L a)), Lp.coeFn_star (reflectR L a)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h3, h4, Pi.star_apply, h2, Pi.smul_apply, star_smul, star_trivial]
  norm_map' u := by
    show ‖star (reflectR L u)‖ = ‖u‖
    rw [norm_cj, LinearIsometry.norm_map]

/-- `C_phys u = \overline{u(-x)}` almost everywhere. -/
theorem coeFn_Cphys (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ⇑(Cphys L u) =ᵐ[volume] fun x => conj ((u : AddCircle L → ℂ) (-x)) := by
  filter_upwards [coeFn_cj L (reflectR L u), coeFn_reflectR L u] with x h1 h2
  show ⇑(star (reflectR L u)) x = _
  rw [h1, h2]

/-- `C_phys` is an involution. -/
theorem Cphys_Cphys (u : Lp ℂ 2 (volume : Measure (AddCircle L))) : Cphys L (Cphys L u) = u := by
  apply Lp.ext
  have h2 := (negMP L).quasiMeasurePreserving.ae_eq_comp (coeFn_Cphys L u)
  filter_upwards [coeFn_Cphys L (Cphys L u), h2] with x h1 h3
  rw [h1]
  simp only [Function.comp] at h3
  rw [h3]
  simp

/-- `C_phys` is a norm isometry. -/
theorem norm_Cphys (u : Lp ℂ 2 (volume : Measure (AddCircle L))) : ‖Cphys L u‖ = ‖u‖ :=
  LinearIsometry.norm_map _ u

/-- **`𝓕(C_phys u)_n = conj(𝓕(u)_n)`** (the Fourier-side characterization used in
`reset_normalization_uniqueness`, now *proved* for the physical `C_phys`). -/
theorem fourier_Cphys (u : Lp ℂ 2 (volume : Measure (AddCircle L))) (n : ℤ) :
    QuantumNLS.Fourier.fourierL2 L (Cphys L u) n = conj (QuantumNLS.Fourier.fourierL2 L u n) :=
  fourier_reflConj L (fun u => Cphys L u) (coeFn_Cphys L) u n


/-- **The ball convention.**  The Fourier unitary `𝓕` carries the open `L²(𝕋_L)` ball of radius `r` *onto* the
open `ℓ²(ℤ)` ball of the same radius `r`: "the same full `L²` ball onto the same sequence ball" is the
equal-radius reading, which is the only one compatible with `‖𝓕u‖ = ‖u‖`. -/
theorem fourierL2_image_ball (r : ℝ) :
    (QuantumNLS.Fourier.fourierL2 L) '' Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r =
      Metric.ball (0 : S2 ℤ) r := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_ball_zero_iff] at hu ⊢
    rwa [LinearIsometryEquiv.norm_map]
  · intro ha
    refine ⟨(QuantumNLS.Fourier.fourierL2 L).symm a, ?_, LinearIsometryEquiv.apply_symm_apply _ a⟩
    rw [mem_ball_zero_iff] at ha ⊢
    rwa [LinearIsometryEquiv.norm_map]

/-- The reference chart `𝓕` is itself canonical in the local sense on every equal-radius pair of balls. -/
theorem isStronglySymplecticOn_fourier (r : ℝ) :
    IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) (QuantumNLS.Fourier.fourierL2 L) :=
  isStronglySymplecticOn_isometry _
    (fun u hu => by
      rw [mem_ball_zero_iff] at hu ⊢; rwa [LinearIsometryEquiv.norm_map])
    (fun a ha => by
      rw [mem_ball_zero_iff] at ha ⊢; rwa [LinearIsometryEquiv.norm_map])

/-- **Local reading justified.**  A *global* strongly symplectic map (DEF-016 as printed) which preserves the
norm (the chart identity `∑|w_n(u)|² = ‖u‖²` of `core/coordinate_conventions.tex`) is canonical in the
local sense on the full ball of every radius `r`, onto the ball of the same radius. -/
theorem IsStronglySymplecticOn.of_global {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {Φ : H → E}
    (h : QuantumNLS.StrongSymplectic.IsStronglySymplectic Φ) (hn : ∀ u, ‖Φ u‖ = ‖u‖) (r : ℝ) :
    IsStronglySymplecticOn (Metric.ball (0 : H) r) (Metric.ball (0 : E) r) Φ := by
  obtain ⟨Ψ, hl, hr, hd⟩ := h.exists_inverse
  refine ⟨fun u hu => ?_, ⟨Ψ, fun y hy => ?_, fun x _ => hl x, fun y _ => hr y, fun y _ => hd y⟩,
    fun u _ => h.differentiable u, fun u _ => h.deriv_iso u, fun u _ => h.symplectic u⟩
  · rw [mem_ball_zero_iff] at hu ⊢; rwa [hn]
  · rw [mem_ball_zero_iff] at hy ⊢
    have := hn (Ψ y)
    rw [hr y] at this
    rw [← this]; exact hy

/-- **LOCAL-022 uniqueness, with the physical reflection-conjugation `C_phys`** (no abstract-`C`
hypothesis).  Two real-analytic canonical maps (local DEF-016) from the *same* full `L²(𝕋_L)` ball of
radius `r` onto the *same* `ℓ²(ℤ)` ball of radius `r` (equal radius: `fourierL2_image_ball`), with squared
moduli `q_n`, derivative `𝓕` at zero, intertwining `u ↦ \overline{u(-x)}` (`C_phys`) with
componentwise conjugation, are equal.  The only abstract binding left is `q` (DEF-014 not realized). -/
theorem reset_normalization_uniqueness_phys {r : ℝ} (hr : 0 < r)
    (q : ℤ → Lp ℂ 2 (volume : Measure (AddCircle L)) → ℝ) (hq0 : ∀ n, q n 0 = 0)
    (Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ)
    (hΦ₁ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₁)
    (hΦ₂ : IsStronglySymplecticOn (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₂)
    (han₁ : AnalyticOnNhd ℝ Φ₁ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (han₂ : AnalyticOnNhd ℝ Φ₂ (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (hm₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₁ u n‖ ^ 2 = q n u)
    (hm₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, ∀ n,
      ‖Φ₂ u n‖ ^ 2 = q n u)
    (hD₁ : ∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hD₂ : ∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hc₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ (Cphys L u) = star (Φ₁ u))
    (hc₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₂ (Cphys L u) = star (Φ₂ u)) :
    ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r, Φ₁ u = Φ₂ u :=
  reset_normalization_uniqueness L hr q hq0 (fun u => Cphys L u) (fourier_Cphys L) Φ₁ Φ₂ hΦ₁ hΦ₂
    han₁ han₂ hm₁ hm₂ hD₁ hD₂ hc₁ hc₂

/-- **Global form, with no ball convention at all.**  Two *global* strongly symplectic (DEF-016 as
printed) real-analytic norm-preserving charts `L²(𝕋_L) → ℓ²(ℤ)` with the same squared moduli, derivative
`𝓕` at zero and `C_phys`-conjugation intertwining are equal everywhere. -/
theorem reset_normalization_uniqueness_global
    (q : ℤ → Lp ℂ 2 (volume : Measure (AddCircle L)) → ℝ) (hq0 : ∀ n, q n 0 = 0)
    (Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ)
    (hΦ₁ : QuantumNLS.StrongSymplectic.IsStronglySymplectic Φ₁)
    (hΦ₂ : QuantumNLS.StrongSymplectic.IsStronglySymplectic Φ₂)
    (hn₁ : ∀ u, ‖Φ₁ u‖ = ‖u‖) (hn₂ : ∀ u, ‖Φ₂ u‖ = ‖u‖)
    (han₁ : AnalyticOnNhd ℝ Φ₁ Set.univ) (han₂ : AnalyticOnNhd ℝ Φ₂ Set.univ)
    (hm₁ : ∀ u n, ‖Φ₁ u n‖ ^ 2 = q n u) (hm₂ : ∀ u n, ‖Φ₂ u n‖ ^ 2 = q n u)
    (hD₁ : ∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hD₂ : ∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hc₁ : ∀ u, Φ₁ (Cphys L u) = star (Φ₁ u)) (hc₂ : ∀ u, Φ₂ (Cphys L u) = star (Φ₂ u)) :
    ∀ u, Φ₁ u = Φ₂ u := by
  intro u
  have hr : 0 < ‖u‖ + 1 := by positivity
  exact reset_normalization_uniqueness_phys L hr q hq0 Φ₁ Φ₂
    (IsStronglySymplecticOn.of_global hΦ₁ hn₁ _) (IsStronglySymplecticOn.of_global hΦ₂ hn₂ _)
    (han₁.mono (Set.subset_univ _)) (han₂.mono (Set.subset_univ _)) (fun u _ n => hm₁ u n)
    (fun u _ n => hm₂ u n) hD₁ hD₂ (fun u _ => hc₁ u) (fun u _ => hc₂ u) u
    (by rw [mem_ball_zero_iff]; linarith)

end Phys

end QuantumNLS.ResetNormalizationUniqueness

#print axioms QuantumNLS.ResetNormalizationUniqueness.negMP
#print axioms QuantumNLS.ResetNormalizationUniqueness.Cphys
#print axioms QuantumNLS.ResetNormalizationUniqueness.coeFn_Cphys
#print axioms QuantumNLS.ResetNormalizationUniqueness.Cphys_Cphys
#print axioms QuantumNLS.ResetNormalizationUniqueness.norm_Cphys
#print axioms QuantumNLS.ResetNormalizationUniqueness.fourier_Cphys
#print axioms QuantumNLS.ResetNormalizationUniqueness.fourierL2_image_ball
#print axioms QuantumNLS.ResetNormalizationUniqueness.isStronglySymplecticOn_fourier
#print axioms QuantumNLS.ResetNormalizationUniqueness.IsStronglySymplecticOn.of_global
#print axioms QuantumNLS.ResetNormalizationUniqueness.reset_normalization_uniqueness_phys
#print axioms QuantumNLS.ResetNormalizationUniqueness.reset_normalization_uniqueness_global
