import NlsGge.Spectral.ActualOddProjectionAndParityReconstructionV4
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

abbrev ActualScalarParityPair :=
  PiLp 2 (fun p : Fin 2 => scalarParity (p.val : ℤ))

def actualEvenParityProjection (f : SpectralScalarL2) : scalarParity (0 : ℤ) :=
  ⟨(2 : ℂ)⁻¹ • (f + halfTranslation f), actualEvenHalfTranslationProjection_mem f⟩

def actualOddParityProjection (f : SpectralScalarL2) : scalarParity (1 : ℤ) :=
  ⟨(2 : ℂ)⁻¹ • (f - halfTranslation f), actualOddHalfTranslationProjection_mem f⟩

def actualScalarParityProjectionPair (f : SpectralScalarL2) : ActualScalarParityPair :=
  WithLp.toLp 2 (fun p =>
    Fin.cases
      (actualEvenParityProjection f)
      (fun q => Fin.cases (actualOddParityProjection f) (fun r => Fin.elim0 r) q)
      p)

def actualScalarParityReconstruction (x : ActualScalarParityPair) : SpectralScalarL2 :=
  (x ⟨0, by norm_num⟩ : SpectralScalarL2) +
    (x ⟨1, by norm_num⟩ : SpectralScalarL2)

theorem actualEvenParityProjection_eq_self (x : scalarParity (0 : ℤ)) :
    actualEvenParityProjection (x : SpectralScalarL2) = x := by
  apply Subtype.ext
  have hx0 := (mem_scalarParity (0 : ℤ) (x : SpectralScalarL2)).mp x.property
  have hx : halfTranslation (x : SpectralScalarL2) = (x : SpectralScalarL2) := by
    simpa [spectralSign] using hx0
  change (2 : ℂ)⁻¹ • ((x : SpectralScalarL2) + halfTranslation x) = x
  rw [hx]
  module

theorem actualOddParityProjection_eq_zero_of_even (x : scalarParity (0 : ℤ)) :
    actualOddParityProjection (x : SpectralScalarL2) = 0 := by
  apply Subtype.ext
  have hx0 := (mem_scalarParity (0 : ℤ) (x : SpectralScalarL2)).mp x.property
  have hx : halfTranslation (x : SpectralScalarL2) = (x : SpectralScalarL2) := by
    simpa [spectralSign] using hx0
  change (2 : ℂ)⁻¹ • ((x : SpectralScalarL2) - halfTranslation x) = 0
  rw [hx]
  module

theorem actualEvenParityProjection_eq_zero_of_odd (x : scalarParity (1 : ℤ)) :
    actualEvenParityProjection (x : SpectralScalarL2) = 0 := by
  apply Subtype.ext
  have hx1 := (mem_scalarParity (1 : ℤ) (x : SpectralScalarL2)).mp x.property
  have hx : halfTranslation (x : SpectralScalarL2) = -(x : SpectralScalarL2) := by
    simpa [spectralSign] using hx1
  change (2 : ℂ)⁻¹ • ((x : SpectralScalarL2) + halfTranslation x) = 0
  rw [hx]
  module

theorem actualOddParityProjection_eq_self (x : scalarParity (1 : ℤ)) :
    actualOddParityProjection (x : SpectralScalarL2) = x := by
  apply Subtype.ext
  have hx1 := (mem_scalarParity (1 : ℤ) (x : SpectralScalarL2)).mp x.property
  have hx : halfTranslation (x : SpectralScalarL2) = -(x : SpectralScalarL2) := by
    simpa [spectralSign] using hx1
  change (2 : ℂ)⁻¹ • ((x : SpectralScalarL2) - halfTranslation x) = x
  rw [hx]
  module

def actualScalarParityProjectionLinearEquiv :
    SpectralScalarL2 ≃ₗ[ℂ] ActualScalarParityPair where
  toFun := actualScalarParityProjectionPair
  invFun := actualScalarParityReconstruction
  left_inv f := by
    change (actualEvenParityProjection f : SpectralScalarL2) +
      (actualOddParityProjection f : SpectralScalarL2) = f
    exact actualEvenOddHalfTranslationProjection_add f
  right_inv x := by
    apply PiLp.ext
    intro p
    refine Fin.cases ?_ ?_ p
    · change actualEvenParityProjection (actualScalarParityReconstruction x) =
        x ⟨0, by norm_num⟩
      apply Subtype.ext
      let e : scalarParity (0 : ℤ) := x ⟨0, by norm_num⟩
      let o : scalarParity (1 : ℤ) := x ⟨1, by norm_num⟩
      have he0 := (mem_scalarParity (0 : ℤ) (e : SpectralScalarL2)).mp e.property
      have he : halfTranslation (e : SpectralScalarL2) = e := by
        simpa [spectralSign] using he0
      have ho1 := (mem_scalarParity (1 : ℤ) (o : SpectralScalarL2)).mp o.property
      have ho : halfTranslation (o : SpectralScalarL2) = -o := by
        simpa [spectralSign] using ho1
      change (2 : ℂ)⁻¹ •
        (((e : SpectralScalarL2) + (o : SpectralScalarL2)) +
          halfTranslation ((e : SpectralScalarL2) + (o : SpectralScalarL2))) = e
      rw [map_add, he, ho]
      module
    · intro q
      refine Fin.cases ?_ (fun r => Fin.elim0 r) q
      apply Subtype.ext
      let e : scalarParity (0 : ℤ) := x ⟨0, by norm_num⟩
      let o : scalarParity (1 : ℤ) := x ⟨1, by norm_num⟩
      have he0 := (mem_scalarParity (0 : ℤ) (e : SpectralScalarL2)).mp e.property
      have he : halfTranslation (e : SpectralScalarL2) = e := by
        simpa [spectralSign] using he0
      have ho1 := (mem_scalarParity (1 : ℤ) (o : SpectralScalarL2)).mp o.property
      have ho : halfTranslation (o : SpectralScalarL2) = -o := by
        simpa [spectralSign] using ho1
      change (2 : ℂ)⁻¹ •
        (((e : SpectralScalarL2) + (o : SpectralScalarL2)) -
          halfTranslation ((e : SpectralScalarL2) + (o : SpectralScalarL2))) = o
      rw [map_add, he, ho]
      module
  map_add' f g := by
    apply PiLp.ext
    intro p
    refine Fin.cases ?_ ?_ p
    · change (actualScalarParityProjectionPair (f + g)).ofLp 0 =
        (actualScalarParityProjectionPair f + actualScalarParityProjectionPair g).ofLp 0
      simp only [WithLp.ofLp_add, actualScalarParityProjectionPair, WithLp.ofLp_toLp]
      apply Subtype.ext
      change (2 : ℂ)⁻¹ • ((f + g) + halfTranslation (f + g)) =
        (2 : ℂ)⁻¹ • (f + halfTranslation f) + (2 : ℂ)⁻¹ • (g + halfTranslation g)
      rw [map_add]
      module
    · intro q
      refine Fin.cases ?_ (fun r => Fin.elim0 r) q
      change (actualScalarParityProjectionPair (f + g)).ofLp 1 =
        (actualScalarParityProjectionPair f + actualScalarParityProjectionPair g).ofLp 1
      simp only [WithLp.ofLp_add, actualScalarParityProjectionPair, WithLp.ofLp_toLp]
      apply Subtype.ext
      change (2 : ℂ)⁻¹ • ((f + g) - halfTranslation (f + g)) =
        (2 : ℂ)⁻¹ • (f - halfTranslation f) + (2 : ℂ)⁻¹ • (g - halfTranslation g)
      rw [map_add]
      module
  map_smul' a f := by
    apply PiLp.ext
    intro p
    refine Fin.cases ?_ ?_ p
    · change (actualScalarParityProjectionPair (a • f)).ofLp 0 =
        (a • actualScalarParityProjectionPair f).ofLp 0
      simp only [WithLp.ofLp_smul, actualScalarParityProjectionPair,
        WithLp.ofLp_toLp, RingHom.id_apply]
      apply Subtype.ext
      change (2 : ℂ)⁻¹ • ((a • f) + halfTranslation (a • f)) =
        a • ((2 : ℂ)⁻¹ • (f + halfTranslation f))
      rw [map_smul]
      module
    · intro q
      refine Fin.cases ?_ (fun r => Fin.elim0 r) q
      change (actualScalarParityProjectionPair (a • f)).ofLp 1 =
        (a • actualScalarParityProjectionPair f).ofLp 1
      simp only [WithLp.ofLp_smul, actualScalarParityProjectionPair,
        WithLp.ofLp_toLp, RingHom.id_apply]
      apply Subtype.ext
      change (2 : ℂ)⁻¹ • ((a • f) - halfTranslation (a • f)) =
        a • ((2 : ℂ)⁻¹ • (f - halfTranslation f))
      rw [map_smul]
      module

end NlsGge.Schur

end
