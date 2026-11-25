import QuantumNLS.CollisionIdentification
import QuantumNLS.ContactDistribution

/-!
# `contact:eq:distdomain` (R-98129FE7), literal real-space form

Source: PR11 `3b1f701a`, `A01.tex:41-46`.  Consumes the frozen `CollisionIdentification ffd608f4`
(literal product trace on `dyij`, smooth restriction agreement, `smoothH1`) and the frozen
`ContactDistribution 3d808cda` (variational-to-test-class domain characterization).

Nothing is assumed: the smooth symmetric test class is shown to lie in `H¹_sym` here, and the
Fourier-defined contact form `q` is rewritten, for such tests, as the real-space integral pairing
`Σ_j ∫ conj(∂_jφ) ∂_jψ + 2c Σ_{i<j} ∫ conj(φ|_{x_i=x_j}) (T_ijψ) dy_ij`, with the exact
coefficient `2c` and the coordinate measure `dy_ij` of `CollisionIdentification.dyij`.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory QuantumNLS.Energy QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.Fourier
  QuantumNLS.ContactOperator QuantumNLS.ContactDistribution QuantumNLS.CollisionIdentification

namespace QuantumNLS.ContactDistributionFull

section Inclusion
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The class of a smooth symmetric periodic function is permutation invariant. -/
theorem physPerm_smoothClass {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hs : SymmFun φ)
    (σ : Equiv.Perm (Fin N)) :
    physPerm σ (smoothClass (L := L) hφ.smooth.continuous) =
      smoothClass (L := L) hφ.smooth.continuous := by
  refine Lp.ext ?_
  have h1 := coeFn_physPerm σ (smoothClass (L := L) hφ.smooth.continuous)
  have h2 : (smoothClass (L := L) hφ.smooth.continuous : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      liftK (L := L) φ := (memLp_liftK hφ.smooth.continuous).coeFn_toLp
  have h3 := (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hx3' : (smoothClass (L := L) hφ.smooth.continuous : (Fin N → AddCircle L) → ℂ) (coordPerm σ x) =
      liftK (L := L) φ (coordPerm σ x) := hx3
  rw [hx1, hx3', hx2]
  unfold liftK
  have := hs σ (fun i => rep (x i))
  simpa [coordPerm_apply] using this

/-- **Actual smooth symmetric test `H¹` inclusion:** every smooth, lattice-periodic, symmetric
test function belongs to `H¹_sym(𝕋_L^N)`. -/
theorem smoothH1_mem_sym {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hs : SymmFun φ) :
    smoothH1 hφ ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) := by
  rw [PhysH1.mem_sym_iff]
  intro σ
  rw [smoothH1_val]
  exact physPerm_smoothClass hφ hs σ

/-- The `H¹_sym` element of a smooth symmetric test function. -/
def smoothVSym {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hs : SymmFun φ) : VSym L N :=
  ⟨smoothH1 hφ, smoothH1_mem_sym hφ hs⟩

theorem smoothVSym_mem_testClass {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hs : SymmFun φ) :
    smoothVSym hφ hs ∈ testClass L N :=
  ⟨φ, hφ, hs, smoothH1_val hφ⟩

theorem testClass_iff (v : VSym L N) :
    v ∈ testClass L N ↔ ∃ (φ : (Fin N → ℝ) → ℂ) (hφ : IsTorusTest L φ) (hs : SymmFun φ),
      v = smoothVSym hφ hs := by
  constructor
  · rintro ⟨φ, hφ, hs, hv⟩
    refine ⟨φ, hφ, hs, ?_⟩
    apply Subtype.ext
    apply PhysH1.val_injective (L := L) (k := N)
    rw [smoothVSym, show ((⟨smoothH1 hφ, _⟩ : VSym L N).1).val = (smoothH1 hφ).val from rfl,
      smoothH1_val]
    exact hv
  · rintro ⟨φ, hφ, hs, rfl⟩
    exact smoothVSym_mem_testClass hφ hs

end Inclusion


section Pairing
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `⟪a,b⟫_{L²}` as the literal integral `∫ conj(A) · b`, for any representative `A` of `a`. -/
theorem inner_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a b : Lp ℂ 2 μ) (A : α → ℂ) (hA : (a : α → ℂ) =ᵐ[μ] A) :
    ⟪a, b⟫_ℂ = ∫ x, conj (A x) * (b : α → ℂ) x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hA] with x hx
  rw [hx]
  simp [mul_comm]

/-- The gradient `gradientCLM j x` is the (unique) weak partial derivative of `x` in `L²`. -/
theorem gradientCLM_hasWeakPartial (j : Fin N) (x : PhysH1 L N) :
    HasWeakPartial j x.val (gradientCLM j x) := by
  obtain ⟨G, hG⟩ := (mem_range_physH1_iff x.val).1 ⟨x, rfl⟩ j
  rwa [gradientCLM_eq_of_weak j x G hG]

/-- **Real-space kinetic pairing** `Σ_j ∫ conj(∂_jφ) · ∂_jψ dx` of a smooth test function `φ`
against the weak gradient of `ψ`. -/
def kinPairing {φ : (Fin N → ℝ) → ℂ} (_hφ : IsTorusTest L φ) (ψ : PhysH1 L N) : ℂ :=
  ∑ j : Fin N, ∫ y, conj (liftK (L := L) (pderiv j φ) y) * (gradientCLM j ψ : _ → ℂ) y
    ∂(torusPiMeasure L N)

/-- **Real-space contact pairing** `2c Σ_{i<j} ∫ conj(φ|_{x_i=x_j}) · T_ijψ dy_ij`
with the exact coefficient `2c` and the coordinate measure `dy_ij`. -/
def contactPairing (c : ℝ) {φ : (Fin N → ℝ) → ℂ} (_hφ : IsTorusTest L φ) (ψ : PhysH1 L N) : ℂ :=
  ((2 * c : ℝ) : ℂ) * ∑ p : ContactForm.Pair N,
    ∫ y, conj (liftK (L := L) φ (diagPoint p.1.1 p.1.2 y.1 y.2)) *
      (productTrace p.1.1 p.1.2 (ne_of_lt p.2) ψ : _ → ℂ) y ∂(dyij (L := L) p.1.1 p.1.2)

theorem gradient_smooth {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (j : Fin N) :
    gradientCLM j (smoothH1 hφ) =
      (memLp_liftK (continuous_pderiv hφ j)).toLp (liftK (L := L) (pderiv j φ)) := by
  apply gradientCLM_eq_of_weak
  rw [smoothH1_val]
  exact smooth_hasWeakPartial hφ j

theorem inner_gradient_smooth {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (j : Fin N)
    (ψ : PhysH1 L N) :
    ⟪gradientCLM j (smoothH1 hφ), gradientCLM j ψ⟫_ℂ =
      ∫ y, conj (liftK (L := L) (pderiv j φ) y) * (gradientCLM j ψ : _ → ℂ) y
        ∂(torusPiMeasure L N) := by
  apply inner_eq_integral
  rw [gradient_smooth hφ j]
  exact (memLp_liftK (continuous_pderiv hφ j)).coeFn_toLp

theorem inner_productTrace_smooth {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (i j : Fin N)
    (hij : i ≠ j) (ψ : PhysH1 L N) :
    ⟪productTrace i j hij (smoothH1 hφ), productTrace i j hij ψ⟫_ℂ =
      ∫ y, conj (liftK (L := L) φ (diagPoint i j y.1 y.2)) *
        (productTrace i j hij ψ : _ → ℂ) y ∂(dyij (L := L) i j) :=
  inner_eq_integral _ _ _ (productTrace_smooth i j hij hφ)

/-- **The Fourier-defined contact form, on a smooth test function, is the real-space
kinetic + contact integral pairing** (exact `2c`, coordinate measure `dy_ij`). -/
theorem q_smooth_eq_pairings (c : ℝ) {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ)
    (ψ : PhysH1 L N) :
    ContactForm.q c (smoothH1 hφ) ψ = kinPairing hφ ψ + contactPairing c hφ ψ := by
  rw [q_eq_physical_pairings, kinPairing, contactPairing]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => inner_gradient_smooth hφ j ψ
  · congr 1
    exact Finset.sum_congr rfl fun p _ => inner_productTrace_smooth hφ _ _ _ ψ

theorem inner_smooth_rhs {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hs : SymmFun φ)
    (f : SymL2 L N) :
    ⟪(valSym (smoothVSym hφ hs) : SymL2 L N), f⟫_ℂ =
      ∫ y, conj (liftK (L := L) φ y) * ((f : L2TN L N) : _ → ℂ) y ∂(torusPiMeasure L N) := by
  have h : ⟪(valSym (smoothVSym hφ hs) : SymL2 L N), f⟫_ℂ =
      ⟪(smoothVSym hφ hs).1.val, (f : L2TN L N)⟫_ℂ := rfl
  rw [h]
  apply inner_eq_integral
  rw [show (smoothVSym hφ hs).1.val = smoothClass (L := L) hφ.smooth.continuous from smoothH1_val hφ]
  exact (memLp_liftK hφ.smooth.continuous).coeFn_toLp

end Pairing

section Main
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- **`contact:eq:distdomain` (R-98129FE7), literal form.**
`ψ ∈ D(H_{N,c}^{(L)})` with `H ψ = f` iff `ψ ∈ H¹_sym` and, for every smooth, lattice-periodic,
permutation-symmetric test function `φ`,
`Σ_j ∫ conj(∂_jφ) ∂_jψ + 2c Σ_{i<j} ∫ conj(φ|_{x_i=x_j}) T_ijψ dy_ij = ∫ conj(φ) f`
(the distribution `-Δψ + 2cΣ δ_L(x_i-x_j) T_ijψ` is represented by `f`). -/
theorem contact_distdomain {c : ℝ} (hc : 0 ≤ c) (ψ f : SymL2 L N) :
    (∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) ↔
      ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
        ∀ (φ : (Fin N → ℝ) → ℂ) (hφ : IsTorusTest L φ), SymmFun φ →
          kinPairing hφ x.1 + contactPairing c hφ x.1 =
            ∫ y, conj (liftK (L := L) φ y) * ((f : L2TN L N) : _ → ℂ) y ∂(torusPiMeasure L N) := by
  rw [mem_domain_iff_smooth_tests hc ψ f]
  refine exists_congr fun x => and_congr_right fun _ => ?_
  constructor
  · intro h φ hφ hs
    have := h (smoothVSym hφ hs) (smoothVSym_mem_testClass hφ hs)
    rw [← inner_smooth_rhs hφ hs f, ← this]
    exact (q_smooth_eq_pairings c hφ x.1).symm
  · intro h v hv
    obtain ⟨φ, hφ, hs, rfl⟩ := (testClass_iff v).1 hv
    rw [inner_smooth_rhs hφ hs f]
    exact (q_smooth_eq_pairings c hφ x.1).trans (h φ hφ hs)

/-- The same statement with the distributional gradient given as an arbitrary weak partial
family `G` (unique by `gradientCLM_eq_of_weak`). -/
theorem contact_distdomain_weak {c : ℝ} (hc : 0 ≤ c) (ψ f : SymL2 L N) :
    (∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) ↔
      ∃ (x : VSym L N) (G : Fin N → L2TN L N), (valSym x : SymL2 L N) = ψ ∧
        (∀ j, HasWeakPartial j x.1.val (G j)) ∧
        ∀ (φ : (Fin N → ℝ) → ℂ) (hφ : IsTorusTest L φ), SymmFun φ →
          (∑ j : Fin N, ∫ y, conj (liftK (L := L) (pderiv j φ) y) * (G j : _ → ℂ) y
              ∂(torusPiMeasure L N)) + contactPairing c hφ x.1 =
            ∫ y, conj (liftK (L := L) φ y) * ((f : L2TN L N) : _ → ℂ) y ∂(torusPiMeasure L N) := by
  rw [contact_distdomain hc ψ f]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, fun j => gradientCLM j x.1, hx, fun j => gradientCLM_hasWeakPartial j x.1, h⟩
  · rintro ⟨x, G, hx, hG, h⟩
    refine ⟨x, hx, fun φ hφ hs => ?_⟩
    have hGj : ∀ j, G j = gradientCLM j x.1 := fun j => (gradientCLM_eq_of_weak j x.1 _ (hG j)).symm
    have := h φ hφ hs
    simp only [hGj] at this
    exact this

end Main

end QuantumNLS.ContactDistributionFull
