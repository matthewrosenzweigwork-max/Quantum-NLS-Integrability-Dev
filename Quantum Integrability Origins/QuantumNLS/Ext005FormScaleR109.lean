import QuantumNLS.Ext005Spectral
import QuantumNLS.Ext005MomentEnergyR108
import Mathlib.Analysis.InnerProductSpace.Dual

/-! R109: the complete physical number-moment form scale, in square-root
coordinates. A coordinate vector u represents A^(-1/2)u in physical Fock
space. This avoids putting the ambient (incomplete) subspace norm on Q(A).
No evolution equation, chain rule or uniqueness conclusion is assumed here. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace Topology
namespace QuantumNLS.Ext005FormScaleR109
open Ext025B3PhysicalSectors Ext005Moments Ext005Spectral
open Ext005MomentEnergyR108 BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

/-- Q((Num+1)^j), represented by its square-root coordinates. -/
abbrev FormSpace (_j : ℕ) := Fock L

theorem formSpace_complete (j : ℕ) : CompleteSpace (FormSpace (L := L) j) :=
  inferInstance

theorem rootWeight_one_le (j n : ℕ) : 1 ≤ Real.sqrt (momentWeight j n) :=
  Real.one_le_sqrt.mpr (momentWeight_one_le j n)

/-- The bounded inclusion of the complete form space into the pivot space. -/
def embedding (j : ℕ) : FormSpace (L := L) j →L[ℂ] Fock L :=
  inverse (fun n => Real.sqrt (momentWeight j n)) (rootWeight_one_le j)

@[simp] theorem embedding_apply (j : ℕ) (u : FormSpace (L := L) j) (n : ℕ) :
    embedding j u n = (((Real.sqrt (momentWeight j n))⁻¹ : ℝ) : ℂ) • u n := rfl

theorem embedding_mem (j : ℕ) (u : FormSpace (L := L) j) :
    embedding j u ∈ momentDomain (L := L) j :=
  inverse_mem _ (rootWeight_one_le j) u

/-- The root map is onto, including its maximal domain. -/
theorem root_embedding (j : ℕ) (u : FormSpace (L := L) j) :
    momentRoot j ⟨embedding j u, embedding_mem j u⟩ = u :=
  multiplier_inverse _ (rootWeight_one_le j) u

theorem embedding_root (j : ℕ) (x : momentDomain (L := L) j) :
    embedding j (momentRoot j x) = x.val := by
  apply Subtype.ext
  funext n
  change (((Real.sqrt (momentWeight j n))⁻¹ : ℝ) : ℂ) •
    ((Real.sqrt (momentWeight j n) : ℂ) • x.val n) = x.val n
  rw [smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by linarith [rootWeight_one_le j n]), Complex.ofReal_one, one_smul]

/-- This algebraic equivalence identifies the form norm with the complete
coordinate Hilbert norm; it does not assert continuity for the ambient norm
on the unbounded operator domain. -/
def rootEquiv (j : ℕ) : momentDomain (L := L) j ≃ₗ[ℂ] FormSpace (L := L) j :=
  { (momentRoot (L := L) j).toFun with
    invFun := fun u => ⟨embedding j u, embedding_mem j u⟩
    left_inv := fun x => Subtype.ext (embedding_root j x)
    right_inv := root_embedding j }

theorem embedding_injective (j : ℕ) : Function.Injective (embedding (L := L) j) := by
  intro u v h
  have h' : (⟨embedding j u, embedding_mem j u⟩ : momentDomain (L := L) j) =
      ⟨embedding j v, embedding_mem j v⟩ := Subtype.ext h
  have := congrArg (momentRoot j) h'
  exact (root_embedding j u).symm.trans (this.trans (root_embedding j v))

theorem range_embedding (j : ℕ) :
    Set.range (embedding (L := L) j) = (momentDomain (L := L) j : Set (Fock L)) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact embedding_mem j u
  · intro hx
    exact ⟨momentRoot j ⟨x, hx⟩, embedding_root j ⟨x, hx⟩⟩

theorem embedding_norm_le (j : ℕ) (u : FormSpace (L := L) j) :
    ‖embedding j u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  rw [embedding_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have h := inverse_bound _ (rootWeight_one_le j) n
  nlinarith [norm_nonneg (u n)]

/-- The form norm squared is exactly the physical number-moment series. -/
theorem energy_embedding (j : ℕ) (u : FormSpace (L := L) j) :
    energy j (embedding j u) = ‖u‖ ^ 2 := by
  exact (energy_eq_root j ⟨embedding j u, embedding_mem j u⟩).trans
    (congrArg (fun z : Fock L => ‖z‖ ^ 2) (root_embedding j u))

theorem embedding_symmetric (j : ℕ) (u v : Fock L) :
    ⟪embedding j u, v⟫_ℂ = ⟪u, embedding j v⟫_ℂ :=
  boundedMultiplier_symmetric _ (inverse_bound _ (rootWeight_one_le j)) u v

/-- Finite physical sectors prove density in the pivot norm. -/
theorem embedding_denseRange (j : ℕ) : DenseRange (embedding (L := L) j) := by
  intro x
  have hs := (projection_hasSum L x).tendsto_sum_nat
  apply isClosed_closure.mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro N
  apply subset_closure
  rw [range_embedding]
  exact Submodule.sum_mem _ (fun n _ => sector_mem_momentDomain j n x)

/-- Riesz coordinates for the antidual: f acts on v by <v,f>.
Every bounded conjugate-linear functional is represented in these coordinates. -/
abbrev Antidual (_j : ℕ) := Fock L

def pairing (j : ℕ) (v : FormSpace (L := L) j) (f : Antidual (L := L) j) : ℂ :=
  ⟪v, f⟫_ℂ

theorem pairing_bound (j : ℕ) (v : FormSpace (L := L) j)
    (f : Antidual (L := L) j) : ‖pairing j v f‖ ≤ ‖v‖ * ‖f‖ :=
  norm_inner_le_norm v f

/-- The coordinate antidual is the full continuous antidual, not a selected
class of test functionals. This is the complex Riesz representation theorem
with the conjugation appropriate to an inner product linear on the right. -/
theorem antidual_representation (j : ℕ)
    (f : FormSpace (L := L) j →L⋆[ℂ] ℂ) :
    ∃! u : Antidual (L := L) j, ∀ v, pairing j v u = f v := by
  let g : StrongDual ℂ (Fock L) :=
    { toFun := fun v => star (f v)
      map_add' := fun v w => by simp
      map_smul' := fun c v => by simp
      cont := continuous_star.comp f.continuous }
  let u : Fock L := (InnerProductSpace.toDual ℂ (Fock L)).symm g
  have hu (v : Fock L) : pairing j v u = f v := by
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (y := g) (x := v)
    change ⟪u, v⟫_ℂ = star (f v) at h
    change ⟪v, u⟫_ℂ = f v
    rw [← inner_conj_symm, h]
    exact star_star (f v)
  refine ⟨u, hu, ?_⟩
  intro w hw
  apply ext_inner_left ℂ
  intro v
  exact (hw v).trans (hu v).symm

/-- H embeds in Q(A)* by the same inverse-root multiplier. -/
def pivotToAntidual (j : ℕ) : Fock L →L[ℂ] Antidual (L := L) j := embedding j

theorem pivot_pairing (j : ℕ) (v : FormSpace (L := L) j) (h : Fock L) :
    pairing j v (pivotToAntidual j h) = ⟪embedding j v, h⟫_ℂ :=
  (embedding_symmetric j v h).symm

theorem pivotToAntidual_injective (j : ℕ) :
    Function.Injective (pivotToAntidual (L := L) j) := embedding_injective j

/-- D3's essential form bound is precisely an a.e. bounded coordinate lift.
This is an equivalence of conditions, not a bound for any solution. -/
theorem energyBounded_iff_coordinates (j : ℕ) (I : Set ℝ) (x : ℝ → Fock L) :
    EnergyBounded j I x ↔ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ t ∂MeasureTheory.volume.restrict I,
        ∃ u : FormSpace (L := L) j, embedding j u = x t ∧ ‖u‖ ^ 2 ≤ C := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, h.mono ?_⟩
    intro t ht
    refine ⟨momentRoot j ⟨x t, ht.1⟩, embedding_root j ⟨x t, ht.1⟩, ?_⟩
    exact (energy_eq_root j ⟨x t, ht.1⟩).symm.le.trans ht.2
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, h.mono ?_⟩
    rintro t ⟨u, hu, hb⟩
    rw [← hu]
    exact ⟨embedding_mem j u, (energy_embedding j u).le.trans hb⟩

end QuantumNLS.Ext005FormScaleR109

#print axioms QuantumNLS.Ext005FormScaleR109.rootEquiv
#print axioms QuantumNLS.Ext005FormScaleR109.embedding_denseRange
#print axioms QuantumNLS.Ext005FormScaleR109.antidual_representation
#print axioms QuantumNLS.Ext005FormScaleR109.energyBounded_iff_coordinates

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005FormScaleR109." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005FormScaleR109." then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
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
  Lean.logInfo m!"R109 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
