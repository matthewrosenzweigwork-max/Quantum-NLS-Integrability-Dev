import QuantumNLS.RootMassInvolutionBatchR9
import QuantumNLS.RootMassPlane
import QuantumNLS.RayPeriodUpgrade

/-! LOCAL-016 support: the actual indexed Hamiltonian field, its first
integrals, and stationary points. No flow or period is an input. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology InnerProductSpace
namespace QuantumNLS.IndexedFieldR27b
open PhysicalTensor (L2T)
open SymplecticBracket RootMassInvolutionR8
attribute [local instance] InnerProductSpace.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

theorem analytic_hamField {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {F : H → ℝ} {u : H}
    (hF : AnalyticAt ℝ F u) : AnalyticAt ℝ (hamField F) u := by
  let A : (H →L[ℝ] ℝ) →L[ℝ] H :=
    (toDual ℝ H).symm.toLinearIsometry.toContinuousLinearMap
  have ha := (A.analyticAt _).comp hF.fderiv
  exact (ha.const_smul (c := (2 : ℝ)⁻¹)).const_smul (c := -Complex.I)

theorem hamField_zero_of_isLocalMin {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {F : H → ℝ} {u : H}
    (hu : IsLocalMin F u) : hamField F u = 0 := by
  unfold hamField SymplecticBracket.gradient
  rw [hu.fderiv_eq_zero]
  simp only [map_zero,smul_zero]

abbrev field (hκ : 0 < κ) (n : ℤ) : L2T L → L2T L :=
  hamField (mass hκ n)

theorem analytic_field (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    AnalyticAt ℝ (field hκ n) u := by
  exact analytic_hamField (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u)

theorem field_zero_of_mass_zero (hκ : 0 < κ) (n : ℤ) (u : L2T L)
    (hu : mass hκ n u = 0) : field hκ n u = 0 := by
  apply hamField_zero_of_isLocalMin
  apply Filter.Eventually.of_forall
  intro v
  rw [hu]
  exact (PhysicalSourceFinal.sourceFacts hκ v).masses.2 n

theorem field_zero (hκ : 0 < κ) (n : ℤ) : field (L := L) hκ n 0 = 0 := by
  apply field_zero_of_mass_zero
  change (PhysicalQuantumMeasure.measure hκ (0 : L2T L) _).toReal = 0
  simp

theorem field_plane (hκ : 0 < κ) (n j : ℤ) (hjn : j ≠ n) (c : ℂ) :
    field hκ n (c • Fourier.modeLp L j) = 0 := by
  apply field_zero_of_mass_zero
  simpa [mass,Ne.symm hjn] using RootMassPlane.masses_plane hκ c j n

theorem derivative_mass (hκ : 0 < κ) (n j : ℤ) {γ : ℝ → L2T L} {t : ℝ}
    (hγ : HasDerivAt γ (field hκ n (γ t)) t) :
    HasDerivAt (fun s => mass hκ j (γ s)) 0 t := by
  have h := (DEF014MassAnalytic.analyticAt_physical_coordinate hκ j (γ t)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hγ
  exact h.congr_deriv (RootMassInvolutionR9.indexed_pair_bracket hκ (γ t) j n)

theorem derivative_norm_sq (hκ : 0 < κ) (n : ℤ) {γ : ℝ → L2T L} {t : ℝ}
    (hγ : HasDerivAt γ (field hκ n (γ t)) t) :
    HasDerivAt (fun s => ‖γ s‖^2) 0 t := by
  have hd : DifferentiableAt ℝ (fun u : L2T L => ‖u‖^2) (γ t) :=
    (hasStrictFDerivAt_norm_sq (γ t)).hasFDerivAt.differentiableAt
  have h := hd.hasFDerivAt.comp_hasDerivAt t hγ
  have hb : pbR (fun u : L2T L => ‖u‖^2) (mass hκ n) (γ t) = 0 := by
    rw [pbR_swap,mass_bracket_total_mass,neg_zero]
  exact h.congr_deriv hb

theorem conservation_on (hκ : 0 < κ) (n : ℤ) {γ : ℝ → L2T L}
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (field hκ n (γ t)) t) :
    ∀ t ∈ Ioo a b,
      RootIndexedMasses.masses hκ (γ t) = RootIndexedMasses.masses hκ (γ t₀) ∧
      ‖γ t‖ = ‖γ t₀‖ := by
  have hc (j : ℤ) : ∀ t ∈ Ioo a b, mass hκ j (γ t) = mass hκ j (γ t₀) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs => (derivative_mass hκ n j (hγ s hs)).differentiableAt.differentiableWithinAt)
      (fun s hs => (derivative_mass hκ n j (hγ s hs)).deriv) ht ht₀
  have hn : ∀ t ∈ Ioo a b, ‖γ t‖^2 = ‖γ t₀‖^2 := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
      (fun s hs => (derivative_norm_sq hκ n (hγ s hs)).differentiableAt.differentiableWithinAt)
      (fun s hs => (derivative_norm_sq hκ n (hγ s hs)).deriv) ht ht₀
  intro t ht
  refine ⟨?_,(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hn t ht)⟩
  apply Subtype.ext
  apply lp.ext
  funext j
  exact hc j t ht

end QuantumNLS.IndexedFieldR27b
#print axioms QuantumNLS.IndexedFieldR27b.analytic_field
#print axioms QuantumNLS.IndexedFieldR27b.field_plane
#print axioms QuantumNLS.IndexedFieldR27b.conservation_on
