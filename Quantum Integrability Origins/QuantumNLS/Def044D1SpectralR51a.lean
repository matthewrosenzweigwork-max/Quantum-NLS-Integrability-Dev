import QuantumNLS.D1Def043
import QuantumNLS.BoundedBetheTransfer
import QuantumNLS.EmpiricalRapidity
import QuantumNLS.PhysicalQuantumMeasure

/-!
DEF-044 clause (1), under owner decision D1. These are interface requirements,
not an assertion that all physical requirements have been discharged.
The basis, original product Born law, rapidities, maximal charges and transfer
are the existing physical objects. No freely chosen cut set occurs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace
namespace QuantumNLS.Def044D1SpectralR51a
open PhysicalTensor BetheLabels BetheCoefficientTransform BetheSpectralCharges
open NormalizedTransfer
variable {L κ : ℝ} [Fact (0 < L)]

abbrev basis (hκ : 0 < κ) (N : ℕ) : BetheBasis L (N+1) :=
  UnconditionalBetheBasis.meanField_physicalBasis L (N+1) (by omega) hκ

/-- Original product law on the complete array space, with no conditioning. -/
def originalLaw (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    Measure (MArr (N+1)) := EmpiricalRapidity.bornMeasure (basis (L := L) hκ N) u hu

instance originalLaw_probability (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    IsProbabilityMeasure (originalLaw hκ u hu N) := by
  unfold originalLaw
  infer_instance

/-- Actual receiver/donor independent rapidities at the microscopic coupling κ/(N+1). -/
def root (N : ℕ) (m : MArr (N+1)) (j : Fin (N+1)) : ℝ :=
  rapidity L (N+1) (κ/(N+1)) m j

def tailFraction (N : ℕ) (R : ℝ) (m : MArr (N+1)) : ℝ :=
  (∑ j : Fin (N+1), if R < |root (L := L) (κ := κ) N m j| then (1 : ℝ) else 0)/(N+1)

def empiricalG (N : ℕ) (m : MArr (N+1)) (z : ℂ) : ℂ :=
  ((N+1 : ℕ) : ℂ)⁻¹ * ∑ j : Fin (N+1), (z-(root (L := L) (κ := κ) N m j : ℂ))⁻¹

def scalarG (μ : Measure ℝ) (z : ℂ) : ℂ := EmpiricalRapidity.cauchyTransform μ z

def multiplier (μ : Measure ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.I * κ * scalarG μ z)

def discriminant (μ : Measure ℝ) (z : ℂ) : ℂ :=
  multiplier (κ := κ) μ z - Complex.exp (Complex.I * L * z)/multiplier (κ := κ) μ z

/-- The four sides of the positively oriented window rectangle (orientation
is used by contour integration; separation is a pointwise boundary condition). -/
def rectangle (a h : ℝ) : Set ℂ :=
  {z | (z.re = -a ∨ z.re = a) ∧ -h ≤ z.im ∧ z.im ≤ h} ∪
  {z | (z.im = -h ∨ z.im = h) ∧ -a ≤ z.re ∧ z.re ≤ a}

def highCut (l : ℕ) : ℝ := (2*(l : ℝ)+1)*Real.pi/L

/-- The exact quantum hypotheses at every positive particle number, including
the actual finite falling-factorial coefficients and the entire factorial bound. -/
structure QuantumRequirements (hκ : 0 < κ) : Prop where
  entire : ∀ N, Differentiable ℂ (normalizedTransfer L κ (N+1))
  diagonal : ∀ N z m, normalizedTransfer L κ (N+1) z (basis (L := L) hκ N m) =
    NormalityBridge.eigen (L := L) κ hκ (by omega : 0 < N+1) m z • basis (L := L) hκ N m
  exact_eigenvalue : ∀ N m z,
    (∀ j, z ≠ (root (L := L) (κ := κ) N m j : ℂ)) →
    NormalityBridge.eigen (L := L) κ hκ (by omega : 0 < N+1) m z =
      TransferSeparation.sFun L (κ/(N+1)) (root (L := L) (κ := κ) N m) z
  normal : ∀ N z, Commute (normalizedTransfer L κ (N+1) z).adjoint
    (normalizedTransfer L κ (N+1) z)
  commute : ∀ N z w, Commute (normalizedTransfer L κ (N+1) z)
    (normalizedTransfer L κ (N+1) w)
  commute_adjoint : ∀ N z w, Commute (normalizedTransfer L κ (N+1) z)
    (normalizedTransfer L κ (N+1) w).adjoint
  expansion : ∀ N z, normalizedTransfer L κ (N+1) z =
    (1 + Complex.exp (Complex.I*z*L)) • ContinuousLinearMap.id ℂ _ +
      ∑ j : Fin (N+1), (((κ^(j.val+1) : ℝ)*HighMomentsRank.fallR (N+1) (j.val+1) : ℝ) : ℂ) •
        KernelDefinition.genericU_N_r (N+1) (j.val+1) j.2 (orderedKernel L (j.val+1) z)
  factorial_kernel : ∀ m : ℕ, 0 < m → ∀ z : ℂ,
    κ^m * ‖orderedKernel L m z‖ ≤
      2*Real.exp (L*|z.im|)*(κ*L)^m/Real.sqrt ((2*m).factorial : ℝ)

/-- Positive tails, mean-square Cauchy estimate and large-cut geometry, at a
fixed profile. The constants are uniform in particle number and all displayed
spectral variables; the profile itself stays fixed. D1 applies to EVERY regular
cut, including cuts outside this particular high-cut sequence. -/
structure ScalarRequirements (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) where
  indexed : D1Def043.D1ScalarMeasure L κ
  physical_measure : indexed.μ = PhysicalQuantumMeasure.measure hκ u
  absolute_moments : ∀ p : ℕ, Integrable (fun q : ℝ => |q|^p) indexed.μ
  R0 : ℝ
  R0_positive : 0 < R0
  positive_tail : ∀ p : ℕ, 0 < p → ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
    ∀ N : ℕ, ∀ R : ℝ, R0 ≤ R →
      (∫ m, tailFraction (L := L) (κ := κ) N R m ∂originalLaw hκ u hu N) ≤
        C/R^(2*p) + D/(((N+1 : ℕ) : ℝ)*R)
  eta0 : ℝ
  eta0_positive : 0 < eta0
  cauchy_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ x y : ℝ, eta0 ≤ y →
    (∫ m, ‖empiricalG (L := L) (κ := κ) N m (x+y*Complex.I) -
      scalarG indexed.μ (x+y*Complex.I)‖^2 ∂originalLaw hκ u hu N) ≤
        C/(((N+1 : ℕ) : ℝ)*y^2)
  height : ℝ
  height_gt_eta0 : eta0 < height
  high_geometry : ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧ ∃ l0 : ℕ,
    ∀ l : ℕ, l0 ≤ l →
      D1Def043.regularCut L κ indexed.μ (highCut (L := L) l) ∧
      D1Def043.regularCut L κ indexed.μ (-highCut (L := L) l) ∧
      (∀ q ∈ indexed.μ.support,
        delta ≤ |q-highCut (L := L) l| ∧ delta ≤ |q+highCut (L := L) l|) ∧
      (∀ z ∈ rectangle (highCut (L := L) l) height,
        c ≤ ‖discriminant (L := L) (κ := κ) indexed.μ z‖)

/-- Clause (1) uses this exact scalar measure with its quantum requirements. -/
structure SpectralInterface (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) where
  quantum : QuantumRequirements (L := L) hκ
  scalar : ScalarRequirements hκ u hu

/-- D1 supplies a unique bracketing integer and both separations at each cut;
there is no hidden restriction to a selected set or to the high-cut sequence. -/
theorem every_d1_cut {hκ : 0 < κ} {u : L2T L} {hu : ‖u‖ = 1}
    (S : ScalarRequirements hκ u hu) (x : ℝ)
    (hx : D1Def043.regularCut L κ S.indexed.μ x) :
    ∃! a : ℤ, (2*Real.pi*a < IndexedScalarMeasure.exteriorForce L κ S.indexed.μ x ∧
      IndexedScalarMeasure.exteriorForce L κ S.indexed.μ x < 2*Real.pi*(a+1)) ∧
      (∀ᵐ t ∂S.indexed.μ, t < x → IndexedScalarMeasure.indexLabel L κ S.indexed.reG t ≤ a) ∧
      (∀ᵐ t ∂S.indexed.μ, x < t → (a : ℝ)+1 ≤ IndexedScalarMeasure.indexLabel L κ S.indexed.reG t) := by
  obtain ⟨a, ha, huniq⟩ := D1Def043.regular_unique_index hx
  refine ⟨a, ⟨ha, S.indexed.separation x hx a ha.1 ha.2⟩, ?_⟩
  intro b hb
  exact huniq b hb.1

/-- DEF-008 retains the actual maximal spectral domain, rather than an
intersection of separately chosen operator domains. -/
theorem actual_charge_domain (hκ : 0 < κ) (N r : ℕ) (ψ : HN L (N+1)) :
    ψ ∈ (charge (basis (L := L) hκ N) (κ/(N+1)) r).domain ↔
      Summable (fun m => |eigenvalue L (N+1) (κ/(N+1)) r m|^2 *
        ‖(basis (L := L) hκ N).repr ψ m‖^2) := by
  simpa only [BetheSpectralCharges.charge, BetheSpectralCharges.multiplier, HilbertBasis.repr_apply_apply] using
    mem_domain (basis (L := L) hκ N) (eigenvalue L (N+1) (κ/(N+1)) r) ψ

/-- DEF-007's resolution is onto the complete coefficient space. -/
theorem full_resolution (hκ : 0 < κ) (N : ℕ) :
    Function.Surjective (coefficientTransform (basis (L := L) hκ N)) :=
  coefficientTransform_surjective _

end QuantumNLS.Def044D1SpectralR51a
#print axioms QuantumNLS.Def044D1SpectralR51a.every_d1_cut
#print axioms QuantumNLS.Def044D1SpectralR51a.actual_charge_domain
#print axioms QuantumNLS.Def044D1SpectralR51a.full_resolution

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def044D1SpectralR51a." ||
        n.toString.startsWith "_private.QuantumNLS.Def044D1SpectralR51a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round51 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
