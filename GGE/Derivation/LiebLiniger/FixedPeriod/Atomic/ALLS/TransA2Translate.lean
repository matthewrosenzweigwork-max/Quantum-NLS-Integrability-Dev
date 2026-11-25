import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Birkhoff.S01Translation38
import NlsGge.Birkhoff.S01Equivariance38c

/-! # Track A, step A2: translation equivariance of the actual Birkhoff map and its inverse

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

For the actual period-one Birkhoff map `physicalBirkhoff` (the X-006/G6 selection, `= actualPhi`)
and its actual inverse `physicalInverseBirkhoff`, spatial translation `u ↦ u(· + a)` acts on
Birkhoff coordinates by the diagonal phases `e^{-2π i n a}`:

* `physicalBirkhoff_translate`: `Φ_n(u(· + a)) = e^{-2π i n a} Φ_n(u)` for every real `a`, every
  `u ∈ L²(ℝ/ℤ)` and every mode `n` (no support or regularity hypothesis);
* `physicalInverseBirkhoff_translate`: if `w_n = e^{-2π i n a} z_n` for all `n`, then
  `Ψ(w) = Ψ(z)(· + a)`.

Route: the existing rotation equivariance of the sequence map `T = Φ ∘ 𝓕⁻¹`
(`BirkhoffTop38.T_rotSeq38`, v2 `D:eq:equivariance`, momentum route) instantiated with the actual
analytic and canonical providers, plus the Fourier identity `fourierSeq38_translate38`
(`𝓕(u(· + a)) = S_{-2πa} 𝓕u`, reflected convention `(𝓕u)_n = -û(-n)`).
The inverse laws are the actual fields `left_inv`/`right_inv` of `actualBirkhoffTop38` on `h⁰`. -/

set_option autoImplicit false
noncomputable section

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common

namespace NlsGge.ALLS.TransA

/-- The coordinates of the actual Birkhoff map are the sequence map `T` on the reflected
Fourier sequence. -/
theorem physicalBirkhoff_coe_eq_T (u : PhysicalL2) :
    (physicalBirkhoff u : ℤ → ℂ) = actualBirkhoffTop38.T (fourierSeq38 u) := by
  funext n
  exact (actualBirkhoffTop38_Phi u n).symm

/-- The rotation equivariance of the actual sequence map `T` on `h⁰`. -/
theorem actualT_rotSeq (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) (θ : ℝ) :
    actualBirkhoffTop38.T (rotSeq38 θ x) = rotSeq38 θ (actualBirkhoffTop38.T x) :=
  actualBirkhoffTop38.T_rotSeq38 (actualBirkhoffAnalytic38.mono (Set.subset_univ _))
    actualBirkhoffCanonical38 x hx θ

/-- The rotation equivariance of the actual inverse sequence map `Tinv` on `h⁰`. -/
theorem actualTinv_rotSeq (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 0) (θ : ℝ) :
    actualBirkhoffTop38.Tinv (rotSeq38 θ z) = rotSeq38 θ (actualBirkhoffTop38.Tinv z) :=
  actualBirkhoffTop38.Tinv_rotSeq38 (actualBirkhoffAnalytic38.mono (Set.subset_univ _))
    actualBirkhoffCanonical38 z hz θ

/-- The phase of `rotSeq38 (-(2πa))` is `e^{-2π i n a}`. -/
theorem rotPhase38_neg_two_pi_mul (a : ℝ) (n : ℤ) :
    rotPhase38 (-(2 * Real.pi * a)) n =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (a : ℂ))) := by
  unfold rotPhase38
  congr 1
  push_cast
  ring

/-- **A2, forward map.**  `Φ_n(u(· + a)) = e^{-2π i n a} Φ_n(u)` for all real `a`, all
`u ∈ L²(ℝ/ℤ)` and all `n ∈ ℤ`. -/
theorem physicalBirkhoff_translate (a : ℝ) (u : PhysicalL2) (n : ℤ) :
    (physicalBirkhoff (translateL2_38 a u) : ℤ → ℂ) n =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (a : ℂ))) *
        (physicalBirkhoff u : ℤ → ℂ) n := by
  rw [physicalBirkhoff_coe_eq_T, physicalBirkhoff_coe_eq_T, fourierSeq38_translate38,
    actualT_rotSeq _ (fourierSeq38_mem_zero u), rotSeq38_apply, rotPhase38_neg_two_pi_mul]

/-- Every `ℓ²` element is in `h⁰`. -/
theorem l2z_mem_seqSobolev38_zero (z : NlsGge.GK38.Lib.L2Z) :
    (z : ℤ → ℂ) ∈ seqSobolev38 0 :=
  (mem_seqSobolev38_zero_iff _).2 (lp.memℓp z)

/-- On `ℓ²`, the actual inverse is `Tinv` read through the reflected Fourier transform. -/
theorem fourierSeq38_physicalInverseBirkhoff (z : NlsGge.GK38.Lib.L2Z) :
    fourierSeq38 (physicalInverseBirkhoff z) = actualBirkhoffTop38.Tinv (z : ℤ → ℂ) := by
  have hz := l2z_mem_seqSobolev38_zero z
  show fourierSeq38 (physicalInverseBirkhoff z) = actualTinv38 (z : ℤ → ℂ)
  rw [actualTinv38_of_mem _ hz]
  rfl

/-- Right inverse law of the actual pair on `ℓ²`: `Φ(Ψ z) = z`. -/
theorem physicalBirkhoff_physicalInverseBirkhoff (z : NlsGge.GK38.Lib.L2Z) :
    physicalBirkhoff (physicalInverseBirkhoff z) = z := by
  apply lp.ext
  rw [physicalBirkhoff_coe_eq_T, fourierSeq38_physicalInverseBirkhoff]
  exact actualBirkhoffTop38.right_inv _ (l2z_mem_seqSobolev38_zero z)

/-- Left inverse law of the actual pair on `L²`: `Ψ(Φ u) = u`. -/
theorem physicalInverseBirkhoff_physicalBirkhoff (u : PhysicalL2) :
    physicalInverseBirkhoff (physicalBirkhoff u) = u := by
  apply fourierSeq38_injective
  rw [fourierSeq38_physicalInverseBirkhoff, physicalBirkhoff_coe_eq_T]
  exact actualBirkhoffTop38.left_inv _ (fourierSeq38_mem_zero u)

/-- **A2, inverse map.**  If `w_n = e^{-2π i n a} z_n` for every `n`, then
`Ψ(w) = Ψ(z)(· + a)`. -/
theorem physicalInverseBirkhoff_translate (a : ℝ) (z w : NlsGge.GK38.Lib.L2Z)
    (hw : ∀ n : ℤ, (w : ℤ → ℂ) n =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (a : ℂ))) * (z : ℤ → ℂ) n) :
    physicalInverseBirkhoff w = translateL2_38 a (physicalInverseBirkhoff z) := by
  have key : physicalBirkhoff (translateL2_38 a (physicalInverseBirkhoff z)) = w := by
    apply lp.ext
    funext n
    rw [physicalBirkhoff_translate, physicalBirkhoff_physicalInverseBirkhoff, hw n]
  rw [← key, physicalInverseBirkhoff_physicalBirkhoff]

end NlsGge.ALLS.TransA
