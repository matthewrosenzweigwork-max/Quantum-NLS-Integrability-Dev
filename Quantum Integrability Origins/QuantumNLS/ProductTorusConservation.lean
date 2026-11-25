import QuantumNLS.ProductTorusGenerator

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T2a: conservation along the bounded-angle flows

Source: `chapters/global/product_torus.tex`, proof, "Bounded angle generators and complete flows", second paragraph:
"Along every local solution of `X_θ`, all `I_j` are consequently constant. Its trajectory lies in the compact fibre
`𝓘⁻¹({𝓘(u)})`. ... The same argument proves conservation of mass by summing the conserved nonnegative coordinates;
no formal differentiation of an unproved infinite sum is used."

For `𝓘 : H → ℓ¹` with Fréchet derivative `D𝓘` and the involution hypothesis (`ProductTorusGenerator.Involutive`):
* `conserved`: on every local solution `α' = X_θ(α)` on an interval, `𝓘(α s) = 𝓘(α t)` (all coordinates at once:
  `d/dt 𝓘(α t) = D𝓘(α t) X_θ(α t) = 0` by `DI_X_zero`, and a function with zero right derivative on an interval is
  constant);
* `mem_fibre`: the trajectory lies in the fibre `𝓘⁻¹{𝓘(α s)}`;
* `mass_conserved`: with source hypothesis 1 (`Σ_n I_n(u) = ‖u‖²`), `‖α t‖ = ‖α s‖`;
* `speed_le`: `‖α'(t)‖ ≤ ‖θ‖_∞ ‖D𝓘(α t)‖/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology Set
open scoped InnerProductSpace

noncomputable section

namespace QuantumNLS.ProductTorusConservation

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- `𝓘` is constant from the left end of a closed subinterval. -/
theorem conserved_le (hI : ∀ u, HasFDerivAt I (DI u) u) (hinv : Involutive DI) (θ : Linf) {α : ℝ → E} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (X DI θ (α t)) t) {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hst : s ≤ t) : I (α t) = I (α s) := by
  have hsub : Icc s t ⊆ Ioo a b := fun r hr => ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  have hder : ∀ r ∈ Ioo a b, HasDerivAt (fun r => I (α r)) 0 r := by
    intro r hr
    have h := (hI (α r)).comp_hasDerivAt r (hα r hr)
    rwa [DI_X_zero hinv θ (α r)] at h
  have hcont : ContinuousOn (fun r => I (α r)) (Icc s t) := fun r hr =>
    (hder r (hsub hr)).continuousAt.continuousWithinAt
  have h := constant_of_has_deriv_right_zero hcont (fun r hr =>
    (hder r (hsub (Ico_subset_Icc_self hr))).hasDerivWithinAt)
  exact h t ⟨hst, le_rfl⟩

/-- **Conservation of every action along a local solution** of `α' = X_θ(α)`. -/
theorem conserved (hI : ∀ u, HasFDerivAt I (DI u) u) (hinv : Involutive DI) (θ : Linf) {α : ℝ → E} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (X DI θ (α t)) t) {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    I (α t) = I (α s) := by
  rcases le_total s t with hst | hts
  · exact conserved_le hI hinv θ hα hs ht hst
  · exact (conserved_le hI hinv θ hα ht hs hts).symm

/-- **The trajectory lies in the fibre** `𝓘⁻¹{𝓘(α s)}`. -/
theorem mem_fibre (hI : ∀ u, HasFDerivAt I (DI u) u) (hinv : Involutive DI) (θ : Linf) {α : ℝ → E} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (X DI θ (α t)) t) {s : ℝ} (hs : s ∈ Ioo a b) :
    ∀ t ∈ Ioo a b, α t ∈ I ⁻¹' {I (α s)} := fun _t ht => conserved hI hinv θ hα hs ht

/-- **Mass conservation** (source hypothesis 1, `Σ_n I_n(u) = ‖u‖²`), by summing the conserved coordinates. -/
theorem mass_conserved (hI : ∀ u, HasFDerivAt I (DI u) u) (hinv : Involutive DI)
    (hmass : ∀ u, ∑' n, (I u : ℤ → ℝ) n = ‖u‖ ^ 2) (θ : Linf) {α : ℝ → E} {a b : ℝ}
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (X DI θ (α t)) t) {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    ‖α t‖ = ‖α s‖ := by
  have h := conserved hI hinv θ hα hs ht
  have h2 : ‖α t‖ ^ 2 = ‖α s‖ ^ 2 := by rw [← hmass, ← hmass, h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The speed bound `‖α'(t)‖ ≤ ‖θ‖_∞ ‖D𝓘(α t)‖/2`. -/
theorem speed_le (θ : Linf) (u : E) : ‖X DI θ u‖ ≤ ‖θ‖ * ‖DI u‖ / 2 := norm_X_le θ u

end QuantumNLS.ProductTorusConservation

#print axioms QuantumNLS.ProductTorusConservation.conserved
#print axioms QuantumNLS.ProductTorusConservation.mem_fibre
#print axioms QuantumNLS.ProductTorusConservation.mass_conserved
