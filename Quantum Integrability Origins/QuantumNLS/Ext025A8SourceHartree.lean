import QuantumNLS.Ext025A8HartreeFlow
import QuantumNLS.GenericUAdjoint

/-! PROP-001 on the actual symmetric-sector kernel carrier. The source
zero extension and first-slot contraction are explicit. The local ODE and
mass conservation are conclusions. Global gluing is separate. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Ext025A8
open TensorCarrier TensorPlacements
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

def sourceHartreeField (A : ∀ n : ℕ, SymSector ℂ H (n + 1) →L[ℂ] SymSector ℂ H (n + 1)) :
    H → H := hartreeField (fun n => extendSymKernel (A n))

omit [CompleteSpace H] in
theorem source_rank_summable
    (A : ∀ n : ℕ, SymSector ℂ H (n + 1) →L[ℂ] SymSector ℂ H (n + 1))
    {a : ℝ} (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n))) :
    Summable (fun n => (n + 1 : ℕ) * ‖extendSymKernel (A n)‖ * Real.exp (a * n)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro n
  gcongr
  exact norm_extendSymKernel_le (A n)

theorem source_kernel_selfAdjoint {n : ℕ}
    (A : SymSector ℂ H (n + 1) →L[ℂ] SymSector ℂ H (n + 1))
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (extendSymKernel A) := by
  change (extendSymKernel A).adjoint = extendSymKernel A
  rw [GenericUAdjoint.adjoint_extendSymKernel, show A.adjoint = A from hA]

/-- Source Picard binding, with rank n+1 and the printed zero extension.
The equation is exactly -i sum_r r A_r^u u with first-slot contraction. -/
theorem prop001_source_local
    (A : ∀ n : ℕ, SymSector ℂ H (n + 1) →L[ℂ] SymSector ℂ H (n + 1))
    {a : ℝ} (ha : 0 < a)
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n))) :
    ∃ S > (1 : ℝ), ∃ δ > (0 : ℝ), ∀ u : H, ‖u‖ ≤ 1 → ∀ b : ℝ,
      ∃ α : ℝ → H, Continuous α ∧ α b = u ∧
        (∀ t, α t ∈ closedBall (0 : H) S) ∧
        (∀ t ∈ Ioo (b - δ) (b + δ), HasDerivAt α (sourceHartreeField A (α t)) t) :=
  prop001_local_application (fun n => extendSymKernel (A n)) ha (source_rank_summable A hs)

theorem hartree_mass_on_interval (A : ∀ n : ℕ,
    HilbertTensorPower ℂ H (n + 1) →L[ℂ] HilbertTensorPower ℂ H (n + 1))
    (hA : ∀ n, IsSelfAdjoint (A n)) {α : ℝ → H} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt α (hartreeField A (α t)) t)
    (hs : ∀ t ∈ Ioo a b, Summable (fun n => hartreeTerm A n (α t))) :
    ∀ t ∈ Ioo a b, ‖α t‖ = ‖α t₀‖ := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hn (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun s => ‖α s‖ ^ 2) 0 t := by
    have hz := hartreeField_orthogonal A hA (hs t ht)
    convert (hd t ht).norm_sq using 1
    rw [real_inner_eq_re_inner ℂ, RCLike.re_to_complex, hz, mul_zero]
  intro t ht
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun s hs => (hn s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hn s hs).deriv) ht ht₀
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- The source selfadjointness gives mass conservation for every constructed
local trajectory staying in a ball with the proved rank majorant. -/
theorem prop001_source_mass
    (A : ∀ n : ℕ, SymSector ℂ H (n + 1) →L[ℂ] SymSector ℂ H (n + 1))
    (hA : ∀ n, IsSelfAdjoint (A n)) {α : ℝ → H} {a b t₀ S : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hS : 0 ≤ S)
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖extendSymKernel (A n)‖ * S ^ (2 * n + 1)))
    (hm : ∀ t ∈ Ioo a b, ‖α t‖ ≤ S)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt α (sourceHartreeField A (α t)) t) :
    ∀ t ∈ Ioo a b, ‖α t‖ = ‖α t₀‖ :=
  hartree_mass_on_interval (fun n => extendSymKernel (A n))
    (fun n => source_kernel_selfAdjoint (A n) (hA n)) ht₀ hd
    (fun t ht => hartree_series_summable _ hS hs (hm t ht))
end QuantumNLS.Ext025A8

#print axioms QuantumNLS.Ext025A8.sourceHartreeField
#print axioms QuantumNLS.Ext025A8.source_rank_summable
#print axioms QuantumNLS.Ext025A8.source_kernel_selfAdjoint
#print axioms QuantumNLS.Ext025A8.prop001_source_local
#print axioms QuantumNLS.Ext025A8.hartree_mass_on_interval
#print axioms QuantumNLS.Ext025A8.prop001_source_mass
