import QuantumNLS.RootWeightedPlaneR26

/-!
R-A8F7B7B0, `thm:root-weighted-masses`,
`source-text/chapters/foundations/ROOT_occupation_energy.tex:40-68`.

The ambient assumptions are the printed torus length L>0 and repulsive
coupling κ>0. The input is an arbitrary physical L2 class. The momentum
map is p_n=2πn/L on each printed open spectral cell, proved below;
its chosen values at separators do not affect the integrals.
`displacement` is the printed D, and ‖u‖^4 is m^2 for m=‖u‖^2.
The H1 qualifier is inside the conclusion, exactly as in the source.
`weakDerivative` is an actual physical weak derivative (`derivative_spec`),
whose squared norm is the kinetic term (`norm_derivative`). The torus
character `fourier k` is the printed exp(i p_k x), in its periodic form.
No converse H1 assertion from finite spectral second moment is made.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
namespace QuantumNLS.RootWeightedMassesR26
open PhysicalTensor (L2T)
open RootWeightedCellsR26 RootWeightedMomentsR26 RootWeightedIdentitiesR26
open RootWeightedPhysicalR26 RootWeightedFirstR26 RootWeightedPlaneR26
open ProductEnergyPreparation (OneH1)
variable {L κ : ℝ} [Fact (0 < L)]

theorem momentum_on_cell (hκ : 0 < κ) (u : L2T L) (n : ℤ) {x : ℝ}
    (hx : x ∈ Ioo (RootIndexedPhase.separator hκ u (n-1)) (RootIndexedPhase.separator hκ u n)) :
    cellMomentum hκ u x = momentum L n := by
  have h1 := ((PhysicalSourceFinal.sourceFacts hκ u).phase.separator_lt_iff x (n-1)).mp hx.1
  have h2 := ((PhysicalSourceFinal.sourceFacts hκ u).phase.lt_separator_iff x n).mp hx.2
  change (((n-1 : ℤ) : ℝ)+1/2)*Real.pi < RootIndexedPhase.theta hκ u x at h1
  change RootIndexedPhase.theta hκ u x < ((n : ℝ)+1/2)*Real.pi at h2
  unfold cellMomentum
  congr 1
  unfold cellIndex
  apply Int.floor_eq_iff.mpr
  have hdiv := (div_lt_iff₀ Real.pi_pos).mpr h2
  have hdiv' := (lt_div_iff₀ Real.pi_pos).mpr h1
  push_cast at hdiv'
  constructor <;> linarith

/-- The complete printed weighted-mass theorem on the actual quantum-derived
measure, physical indexed masses and physical weak H1 derivative. -/
theorem root_weighted_masses (hκ : 0 < κ) (u : L2T L) :
    Integrable (fun x => (x-cellMomentum hκ u x)^2) (PhysicalQuantumMeasure.measure hκ u) ∧
    0 ≤ displacement hκ u ∧ displacement hκ u ≤ κ*‖u‖^4/L ∧
    (Integrable (fun x : ℝ => x^2) (PhysicalQuantumMeasure.measure hκ u) ↔
      Summable (fun n : ℤ => momentum L n^2*(RootIndexedMasses.masses hκ u).1 n)) ∧
    ∀ hH : OneH1 u,
      Summable (fun n : ℤ => |momentum L n*(RootIndexedMasses.masses hκ u).1 n|) ∧
      Summable (fun n : ℤ => |momentum L n^2*(RootIndexedMasses.masses hκ u).1 n|) ∧
      ⟪u,-Complex.I • weakDerivative u hH⟫_ℂ =
        ((∑' n : ℤ,momentum L n*(RootIndexedMasses.masses hκ u).1 n : ℝ) : ℂ) ∧
      ‖weakDerivative u hH‖^2+κ*ChargeEnergy.quartic (u : AddCircle L → ℂ) =
        (∑' n : ℤ,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) +
          2*κ*‖u‖^4/L-displacement hκ u ∧
      κ*‖u‖^4/L ≤ ‖weakDerivative u hH‖^2+κ*ChargeEnergy.quartic (u : AddCircle L → ℂ) -
        (∑' n : ℤ,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) ∧
      ‖weakDerivative u hH‖^2+κ*ChargeEnergy.quartic (u : AddCircle L → ℂ) -
        (∑' n : ℤ,momentum L n^2*(RootIndexedMasses.masses hκ u).1 n) ≤ 2*κ*‖u‖^4/L ∧
      (u ≠ 0 → ∀ k : ℤ,
        (∀ n : ℤ,(RootIndexedMasses.masses hκ u).1 n = if n=k then ‖u‖^2 else 0) ↔
          ∃ a : ℂ,(u : AddCircle L → ℂ) =ᵐ[volume] fun x => a*_root_.fourier k x) := by
  obtain ⟨hd0,hd1⟩ := displacement_bound hκ u
  refine ⟨integrable_displacement hκ u,hd0,hd1,second_moment_equivalence hκ u,fun hH => ?_⟩
  obtain ⟨hx,_⟩ := physical_second hκ u hH
  obtain ⟨hs1,hp⟩ := spectral_momentum hκ u hx
  obtain ⟨hs2,hE,hlo,hhi⟩ := energy_identity hκ u hH
  have hP : fourierMomentum u = ∑' n : ℤ,momentum L n*(RootIndexedMasses.masses hκ u).1 n :=
    (physical_first_moment hκ u hH).symm.trans hp
  have hinner := (momentum_inner u hH).symm.trans (congrArg Complex.ofReal hP)
  have he : ‖weakDerivative u hH‖^2+κ*ChargeEnergy.quartic (u : AddCircle L → ℂ) =
      ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ) := by
    rw [norm_derivative]
    rfl
  exact ⟨hs1,hs2.abs,hinner,he.trans hE,by rwa [he],by rwa [he],
    fun _ k => single_index_iff_plane hκ u hH k⟩

end QuantumNLS.RootWeightedMassesR26

#print axioms QuantumNLS.RootWeightedMassesR26.root_weighted_masses
