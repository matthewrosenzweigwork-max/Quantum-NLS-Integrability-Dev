import NlsGge.GK38.PairPotential

/-!
# F2 (part 1): the free solution, the potential coefficient and the Volterra operator

Source: Grébert-Kappeler book, Chapter I, section 1 (equation `(1.2)` and the proof of Theorem 1.1).
The fundamental solution `M(t, λ, φ)` of `L(φ)M = λM`, `M(0) = Id`, is the solution of the integral
equation
`M(t) = E_λ(t) + ∫₀ᵗ E_λ(t-s) Φ̃(s) M(s) ds`, `E_λ(t) = diag(e^{-iλt}, e^{iλt})`,
`Φ̃ = [[0, iφ₁],[-iφ₂, 0]]`.  The operator
`(𝒱 N)(t) = ∫₀ᵗ E_λ(t-s) Φ̃(s) N(s) ds` is defined on `C([0,1], M₂(ℂ))`.

## Convention (binding instruction from the F1 review, finding N2)

`volterra`, `monodromyPair`, `fundPair` are defined through F1's representatives
`potRepFst38 φ`, `potRepSnd38 φ` (equivalently `zsCoeffPot38`, see `zsCoeffPot38_eq`): the
potential coefficient is `potCoeff38 φ s = [[0, i potRepFst38 φ s],[-i potRepSnd38 φ s, 0]]`.
The `L¹` size is F1's `potL1Norm38 φ = ∫₀¹ (|φ₁| + |φ₂|)`.

## Instance remark (why the operator is built on `Fin 2 → Fin 2 → ℂ`)

`Matrix` is not reducible, so the metric topology of any norm on `Matrix` is not found to agree with
the product topology `Matrix` carries by default, at instance transparency.  Consequently
`NormedAddCommGroup C(Icc, Matrix ..)` (and `IntervalIntegrable` for matrix-valued functions) is not
synthesized.  The bounded operator is therefore built on `PairCont38 = C(Icc, Fin 2 → Fin 2 → ℂ)`,
with the sup norm; `volterra` is the same term at the type `C(Icc, Matrix ..) →L[ℂ] C(Icc, Matrix ..)`
(definitional equality, no cast).  All integrals are integrals of the scalar entries
(`(..) i j`), as in F1.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-- The `2 × 2` complex matrices. -/
abbrev PairMat38 : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- Continuous matrix functions on `[0,1]`, as continuous maps into `Fin 2 → Fin 2 → ℂ` (the same
type as `C(Icc, Matrix ..)` up to unfolding `Matrix`, but with the sup-norm instances available). -/
abbrev PairCont38 : Type := C(Set.Icc (0 : ℝ) 1, Fin 2 → Fin 2 → ℂ)

/-! ### The free solution `E_z(t) = diag(e^{-izt}, e^{izt})` -/

/-- `E_z(t) = diag(e^{-izt}, e^{izt}) = e^{-zRt}` on the whole real line. -/
def freeE (z : ℂ) (t : ℝ) : PairMat38 :=
  !![Complex.exp (-(Complex.I * z * t)), 0; 0, Complex.exp (Complex.I * z * t)]

/-- `freeE` is the repository's free fundamental solution. -/
theorem freeE_eq (z : ℂ) (t : ℝ) :
    freeE z t = NlsGge.SpectralFoundations.freeZsFundamentalComplex z t :=
  (freeZsFundamentalComplex_entries z t).symm

theorem freeE_zero (z : ℂ) : freeE z 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [freeE]

theorem freeE_add (z : ℂ) (a b : ℝ) : freeE z (a + b) = freeE z a * freeE z b := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [freeE, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add] <;> ring_nf

theorem continuous_freeE (z : ℂ) : Continuous (freeE z) := by
  unfold freeE
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem norm_freeE_entry_le (z : ℂ) (t : ℝ) (i j : Fin 2) :
    ‖freeE z t i j‖ ≤ Real.exp (|z.im| * |t|) := by
  have h1 : z.im * t ≤ |z.im| * |t| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : -(z.im * t) ≤ |z.im| * |t| := by rw [← abs_mul]; exact neg_le_abs _
  fin_cases i <;> fin_cases j <;> simp [freeE, Complex.norm_exp] <;>
    first | positivity | exact h1 | exact h2

/-- `E_z(t)` as a continuous function on `[0,1]` (book `E_λ`). -/
def freeFund (z : ℂ) : C(Set.Icc (0 : ℝ) 1, Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨fun t => freeE z t, (continuous_freeE z).comp continuous_subtype_val⟩

@[simp] theorem freeFund_apply (z : ℂ) (t : Set.Icc (0 : ℝ) 1) : freeFund z t = freeE z t := rfl

/-! ### The potential coefficient `Φ̃ = [[0, iφ₁],[-iφ₂, 0]]` -/

/-- `Φ̃(s) = [[0, iφ₁(s)],[-iφ₂(s), 0]] = RΦ(s)` for the representatives of F1. -/
def potCoeff38 (φ : PotPair) (s : ℝ) : PairMat38 :=
  !![0, Complex.I * potRepFst38 φ s; -(Complex.I * potRepSnd38 φ s), 0]

/-- The scalar size `|φ₁(s)| + |φ₂(s)|` of the representatives; `potL1Norm38 φ = ∫₀¹ potW38 φ`. -/
def potW38 (φ : PotPair) (s : ℝ) : ℝ := ‖potRepFst38 φ s‖ + ‖potRepSnd38 φ s‖

theorem potW38_nonneg (φ : PotPair) (s : ℝ) : 0 ≤ potW38 φ s := by
  unfold potW38; positivity

theorem potL1Norm38_eq_integral (φ : PotPair) :
    potL1Norm38 φ = ∫ s in (0 : ℝ)..1, potW38 φ s := rfl

/-- The coefficient of `zsCoeffPot38` is `-zR + Φ̃` (book `(1.2)`). -/
theorem zsCoeffPot38_eq (φ : PotPair) (z : ℂ) (t : ℝ) :
    zsCoeffPot38 φ z t = !![-(Complex.I * z), 0; 0, Complex.I * z] + potCoeff38 φ t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zsCoeffPot38, zsCoeffPair, potCoeff38]

theorem norm_potCoeff38_entry_le (φ : PotPair) (s : ℝ) (i j : Fin 2) :
    ‖potCoeff38 φ s i j‖ ≤ potW38 φ s := by
  have h1 := norm_nonneg (potRepFst38 φ s)
  have h2 := norm_nonneg (potRepSnd38 φ s)
  fin_cases i <;> fin_cases j <;> simp [potCoeff38, potW38] <;> linarith

theorem intervalIntegrable_potW38 (φ : PotPair) : IntervalIntegrable (potW38 φ) volume 0 1 :=
  (intervalIntegrable_norm_coverRep38_one φ.1).add (intervalIntegrable_norm_coverRep38_one φ.2)

theorem intervalIntegrable_potCoeff38_entry (φ : PotPair) (i j : Fin 2) :
    IntervalIntegrable (fun s => potCoeff38 φ s i j) volume 0 1 := by
  fin_cases i <;> fin_cases j <;> simp only [potCoeff38]
  · exact intervalIntegrable_const
  · simpa [potRepFst38] using (intervalIntegrable_coverRep38_one φ.1).const_mul Complex.I
  · simpa [potRepSnd38] using (intervalIntegrable_coverRep38_one φ.2).const_mul (-Complex.I)
  · exact intervalIntegrable_const

/-! ### The extension of `N` to `ℝ` and the integrand -/

/-- The constant-on-the-ends extension of `N : C([0,1], ·)` to `ℝ`. -/
def ext38 (N : PairCont38) : ℝ → PairMat38 := Set.IccExtend zero_le_one N

theorem continuous_ext38 (N : PairCont38) : Continuous (ext38 N) := N.continuous.Icc_extend'

theorem ext38_of_mem (N : PairCont38) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ext38 N s = N ⟨s, hs⟩ := Set.IccExtend_of_mem _ _ hs

theorem norm_ext38_entry_le (N : PairCont38) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖ext38 N s i j‖ ≤ ‖N‖ := by
  rw [ext38_of_mem N hs]
  exact (norm_le_pi_norm (N ⟨s, hs⟩ i) j).trans
    ((norm_le_pi_norm (N ⟨s, hs⟩) i).trans (N.norm_coe_le_norm ⟨s, hs⟩))

end

end NlsGge.GK38
