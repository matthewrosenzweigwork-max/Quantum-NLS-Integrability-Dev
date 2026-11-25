import QuantumNLS.RootScalarUniqueR28

/-! Properness descends the actual total-variation continuity to the realized ell1 set.
The topology of the domain is the inherited ell1 topology. The target continuity
is stated explicitly using the Jordan total-variation distance, not the weak topology. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootScalarContinuityR28
open PhysicalTensor (L2T)
open RootScalarUniqueR28
open TotalVariation (tvNorm)
variable {L κ : ℝ} [Fact (0 < L)]

def realized (hκ : 0 < κ) : Set ActionTorus.PosL1 := Set.range (RootIndexedMasses.masses (L := L) hκ)

def realizedPoint (hκ : 0 < κ) (u : L2T L) : realized (L := L) hκ :=
  ⟨RootIndexedMasses.masses hκ u,mem_range_self u⟩

def realizer (hκ : 0 < κ) (a : realized (L := L) hκ) : L2T L := a.property.choose

lemma realizer_spec (hκ : 0 < κ) (a : realized (L := L) hκ) :
    RootIndexedMasses.masses hκ (realizer hκ a) = a.val := a.property.choose_spec

def scalarLaw (hκ : 0 < κ) (a : realized (L := L) hκ) : FiniteMeasure ℝ :=
  ⟨PhysicalQuantumMeasure.measure hκ (realizer hκ a),inferInstance⟩

lemma scalarLaw_eq (hκ : 0 < κ) (a : realized (L := L) hκ) (u : L2T L)
    (hu : RootIndexedMasses.masses hκ u = a.val) :
    (scalarLaw hκ a : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u :=
  uniqueness hκ ((realizer_spec hκ a).trans hu.symm)

lemma scalarLaw_realizedPoint (hκ : 0 < κ) (u : L2T L) :
    (scalarLaw hκ (realizedPoint hκ u) : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u :=
  scalarLaw_eq hκ _ u rfl

lemma tv_physical (hκ : 0 < κ) (u0 : L2T L) :
    Tendsto (fun u : L2T L => tvNorm (PhysicalQuantumMeasure.measure hκ u)
      (PhysicalQuantumMeasure.measure hκ u0)) (𝓝 u0) (𝓝 0) := by
  have hh := (D05TotalVariation.tv_continuousAt hκ u0).comp
    ((show Continuous (fun u : L2T L => (κ,u)) by fun_prop).tendsto u0)
  convert hh using 1
  funext u
  simp only [Function.comp_apply,PhysicalL2Normalization.measure_eq_Mmeas]

lemma scalarLaw_tv_continuous (hκ : 0 < κ) (a : realized (L := L) hκ) :
    Tendsto (fun b : realized (L := L) hκ => tvNorm
      (scalarLaw hκ b : Measure ℝ) (scalarLaw hκ a : Measure ℝ)) (𝓝 a) (𝓝 0) := by
  have hp : IsProperMap (RootIndexedMasses.masses (L := L) hκ) :=
    isProperMap_iff_isCompact_preimage.mpr
      ⟨DEF014Continuity.continuous_physical_masses hκ,
        fun _ hK => RootMassProperR27.compact_preimage hκ hK⟩
  apply tendsto_def.mpr
  intro S hS
  have H : ∀ u0 ∈ (RootIndexedMasses.masses (L := L) hκ) ⁻¹' {a.val},
      ∀ᶠ u in 𝓝 u0, tvNorm (PhysicalQuantumMeasure.measure hκ u)
        (scalarLaw hκ a : Measure ℝ) ∈ S := by
    intro u0 hu0
    have he := scalarLaw_eq hκ a u0 hu0
    have he' : ∀ u : L2T L, tvNorm (PhysicalQuantumMeasure.measure hκ u) (scalarLaw hκ a : Measure ℝ) =
        tvNorm (PhysicalQuantumMeasure.measure hκ u) (PhysicalQuantumMeasure.measure hκ u0) := by
      intro u
      exact D05TotalVariation.tvNorm_congr he
    have hlocal := (tv_physical hκ u0).eventually (p := fun t : ENNReal => t ∈ S) hS
    filter_upwards [hlocal] with u hu
    exact (he' u).symm ▸ hu
  have hh := hp.isClosedMap.eventually_nhds_fiber a.val H
  have hv := continuous_subtype_val.tendsto a
  filter_upwards [hv.eventually hh] with b hb
  exact hb (realizer hκ b) (realizer_spec hκ b)

end QuantumNLS.RootScalarContinuityR28
