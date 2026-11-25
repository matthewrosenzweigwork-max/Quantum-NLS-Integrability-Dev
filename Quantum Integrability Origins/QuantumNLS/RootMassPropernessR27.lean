import QuantumNLS.RootMassProperR27

/-!
R-0191D778, `thm:root-mass-properness`,
`source-text/chapters/foundations/ROOT_mass_properness.tex:10-30`.
Physical L2 and physical Fourier coefficients use the volume-normalized
orthonormal Fourier transform; p_n=2πn/L. The square of m=‖u‖² is ‖u‖⁴.
The positive ell1 carrier has precisely the inherited ell1 norm topology.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootMassPropernessR27
open PhysicalTensor (L2T)
open ActionTorus RootWeightedCellsR26 RootMassSpectralR27 RootMassBoundR27
variable {L κ : ℝ} [Fact (0 < L)]

/-- The complete printed Fourier-tail bound, continuity, properness, compact
fibres and closed realization set, with only the printed ambient L,κ>0. -/
theorem root_mass_properness (hκ : 0 < κ) :
    (∀ (u : L2T L) (Y : ℝ),
      max 1 (max (Real.log 3/L) (16*κ*‖u‖^2)) ≤ Y →
      fourierTail Y u ≤
        4*(∑' n : ℤ,min 1 (momentum L n^2/Y^2)*(RootIndexedMasses.masses (L := L) hκ u).1 n)+
          4*κ*‖u‖^4/(L*Y^2)+8*κ*‖u‖^4/Y) ∧
    Continuous (RootIndexedMasses.masses (L := L) hκ) ∧
    (∀ K : Set PosL1,IsCompact K → IsCompact ((RootIndexedMasses.masses (L := L) hκ) ⁻¹' K)) ∧
    (∀ a : PosL1,IsCompact ((RootIndexedMasses.masses (L := L) hκ) ⁻¹' {a})) ∧
    IsClosed (Set.range (RootIndexedMasses.masses (L := L) hκ)) := by
  have hc : Continuous (RootIndexedMasses.masses (L := L) hκ) :=
    DEF014Continuity.continuous_physical_masses hκ
  have hp : IsProperMap (RootIndexedMasses.masses (L := L) hκ) :=
    isProperMap_iff_isCompact_preimage.mpr ⟨hc,fun _ hK => RootMassProperR27.compact_preimage (L := L) hκ hK⟩
  exact ⟨fun u _ hY => fourier_tail_bound hκ u hY,hc,
    fun _ hK => hp.isCompact_preimage hK,fun _ => hp.isCompact_preimage isCompact_singleton,hp.isClosed_range⟩

end QuantumNLS.RootMassPropernessR27
#print axioms QuantumNLS.RootMassPropernessR27.root_mass_properness
