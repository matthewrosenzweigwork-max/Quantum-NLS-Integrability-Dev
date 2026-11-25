import QuantumNLS.Ext025B7JointResolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import QuantumNLS.Ext025B8BorelLaws
import QuantumNLS.Ext025B7SpectralCompression
import QuantumNLS.Ext025B8EnergyCompression
import Mathlib.MeasureTheory.Integral.Lebesgue.Add


/-! GP-08, R-2E4C2F4E: arbitrary real diagonal operators on an independent
Hilbert basis, including the actual occupation basis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Topology Function
open scoped InnerProductSpace BigOperators ENNReal LinearPMap
namespace QuantumNLS.Ext025B9Diagonal
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local instance : DecidableEq ι := Classical.decEq ι
/-- The exact maximal domain; square summability is imposed only AFTER
multiplying by the full symbol, permitting cancellations in combinations. -/
def domain (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) : Submodule ℂ (E) where
  carrier := {ψ | Memℓp (fun m => (ev m : ℂ) * b.repr ψ m) 2}
  zero_mem' := by
    change Memℓp (fun m => (ev m : ℂ) * b.repr 0 m) 2
    convert (zero_memℓp : Memℓp (0 : ι → ℂ) 2) using 1
    funext m
    simp
  add_mem' := by
    intro ψ φ hψ hφ
    change Memℓp (fun m => (ev m : ℂ) * b.repr (ψ + φ) m) 2
    rw [b.repr.map_add]
    convert hψ.add hφ using 1
    funext m
    change (ev m : ℂ) * (b.repr ψ m + b.repr φ m) = _
    exact mul_add _ _ _
  smul_mem' := by
    intro a ψ hψ
    change Memℓp (fun m => (ev m : ℂ) * b.repr (a • ψ) m) 2
    simpa only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] using hψ.const_mul a

/-- Literal weighted-square domain criterion. Summable nonnegative terms
means that the nonnegative series is finite, rather than Lean's default
value for a divergent real tsum. -/
theorem mem_domain (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) (ψ : E) :
    ψ ∈ domain b ev ↔ Summable (fun m => |ev m| ^ 2 * ‖⟪b m, ψ⟫_ℂ‖ ^ 2) := by
  change Memℓp _ 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, HilbertBasis.repr_apply_apply]

/-- A partial linear operator with precisely the maximal domain. -/
def multiplier (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) : E →ₗ.[ℂ] E where
  domain := domain b ev
  toFun :=
    { toFun := fun ψ => b.repr.symm ⟨fun m => (ev m : ℂ) * b.repr ψ.val m, ψ.property⟩
      map_add' := by
        intro ψ φ
        apply b.repr.injective
        rw [b.repr.map_add, LinearIsometryEquiv.apply_symm_apply,
          LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
        ext m
        change (ev m : ℂ) * b.repr (ψ.val + φ.val) m =
          (ev m : ℂ) * b.repr ψ.val m + (ev m : ℂ) * b.repr φ.val m
        rw [b.repr.map_add]
        exact mul_add _ _ _
      map_smul' := by
        intro a ψ
        apply b.repr.injective
        ext m
        simp [mul_left_comm] }

theorem multiplier_coord (b : HilbertBasis ι ℂ E) (ev : ι → ℝ)
    (ψ : (multiplier b ev).domain) (m : ι) :
    ⟪b m, multiplier b ev ψ⟫_ℂ = (ev m : ℂ) * ⟪b m, (ψ : E)⟫_ℂ := by
  rw [← HilbertBasis.repr_apply_apply]
  change b.repr (b.repr.symm _) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (ev m : ℂ) * b.repr ψ.val m = _
  rw [HilbertBasis.repr_apply_apply]

/-- Existence and uniqueness of the vector with multiplied coordinates
characterizes domain membership in both directions. -/
theorem maximal (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) (ψ : E) :
    ψ ∈ (multiplier b ev).domain ↔
      ∃! φ : E, ∀ m, ⟪b m, φ⟫_ℂ = (ev m : ℂ) * ⟪b m, ψ⟫_ℂ := by
  constructor
  · intro h
    refine ⟨multiplier b ev ⟨ψ, h⟩, fun m => multiplier_coord b ev ⟨ψ,h⟩ m, ?_⟩
    intro φ hφ
    apply b.repr.injective
    ext m
    simpa only [HilbertBasis.repr_apply_apply] using (hφ m).trans (multiplier_coord b ev ⟨ψ,h⟩ m).symm
  · rintro ⟨φ, hφ, _⟩
    change Memℓp _ 2
    have heq : (fun m => (ev m : ℂ) * b.repr ψ m) = (fun m => b.repr φ m) := by
      funext m
      simpa only [HilbertBasis.repr_apply_apply] using (hφ m).symm
    rw [heq]
    exact lp.memℓp _

theorem basis_mem_domain (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) (m : ι) :
    b m ∈ (multiplier b ev).domain := by
  apply (maximal b ev (b m)).mpr
  refine ⟨(ev m : ℂ) • b m, ?_, ?_⟩
  · intro k
    simp only [inner_smul_right]
    by_cases h : k = m
    · subst k; rfl
    · rw [b.orthonormal.inner_eq_zero h]
      simp
  · intro φ hφ
    apply b.repr.injective
    ext k
    simp only [HilbertBasis.repr_apply_apply]
    rw [hφ k, inner_smul_right]
    by_cases h : k = m
    · subst k; rfl
    · rw [b.orthonormal.inner_eq_zero h]; simp

theorem multiplier_basis (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) (m : ι) :
    multiplier b ev ⟨b m, basis_mem_domain b ev m⟩ = (ev m : ℂ) • b m := by
  apply b.repr.injective
  ext k
  simp only [HilbertBasis.repr_apply_apply]
  rw [multiplier_coord, inner_smul_right]
  by_cases h : k = m
  · subst k; rfl
  · rw [b.orthonormal.inner_eq_zero h]; simp

theorem domain_dense (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) :
    (multiplier b ev).domain.topologicalClosure = ⊤ := by
  apply top_unique
  rw [← b.dense_span]
  exact Submodule.topologicalClosure_mono (Submodule.span_le.mpr (by
    rintro _ ⟨m, rfl⟩; exact basis_mem_domain b ev m))

theorem constant_domain (b : HilbertBasis ι ℂ E) (a : ℝ) :
    (multiplier b (fun _ => a)).domain = ⊤ := by
  apply top_unique
  intro ψ _
  exact (lp.memℓp (b.repr ψ)).const_mul (a : ℂ)

theorem constant_apply (b : HilbertBasis ι ℂ E) (a : ℝ) (ψ : E)
    (h : ψ ∈ (multiplier b (fun _ => a)).domain) :
    multiplier b (fun _ => a) ⟨ψ,h⟩ = (a : ℂ) • ψ := by
  apply b.repr.injective
  ext m
  simpa only [HilbertBasis.repr_apply_apply, inner_smul_right] using multiplier_coord b (fun _ => a) ⟨ψ,h⟩ m

/-- Real maximal multipliers are symmetric on their full domains. -/
theorem multiplier_formalAdjoint (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) :
    (multiplier b ev).IsFormalAdjoint (multiplier b ev) := by
  intro x y
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro m
  have hx := multiplier_coord b ev x m
  have hy := multiplier_coord b ev y m
  simp only [← HilbertBasis.repr_apply_apply] at hx hy
  rw [hx, hy]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

variable [CompleteSpace E]

/-- Self-adjointness, including equality of the maximal adjoint domain.
Testing the adjoint on each basis vector forces the entire multiplied
coordinate array to lie in l2; no lower bound on the real symbol is used. -/
theorem multiplier_selfAdjoint (b : HilbertBasis ι ℂ E) (ev : ι → ℝ) :
    IsSelfAdjoint (multiplier b ev) := by
  have hd : Dense ((multiplier b ev).domain : Set (E)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact domain_dense b ev
  have hle : multiplier b ev ≤ (multiplier b ev)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd (multiplier_formalAdjoint b ev)
  have hdom : (multiplier b ev)†.domain ≤ (multiplier b ev).domain := by
    intro y hy
    let z := (multiplier b ev)† ⟨y, hy⟩
    have he (m : ι) : b.repr z m = (ev m : ℂ) * b.repr y m := by
      have h := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩
        ⟨b m, basis_mem_domain b ev m⟩
      rw [multiplier_basis, inner_smul_right] at h
      have hh := congrArg (starRingEnd ℂ) h
      simpa only [map_mul, inner_conj_symm, Complex.conj_ofReal,
        HilbertBasis.repr_apply_apply] using hh
    change Memℓp (fun m => (ev m : ℂ) * b.repr y m) 2
    simpa only [← he] using lp.memℓp (b.repr z)
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

end QuantumNLS.Ext025B9Diagonal


/-! GP-08 application R-2E4C2F4E: construct the common-domain Hilbert
space as a closed graph subspace and identify the literal source norm.
No complete graph carrier is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Topology Function
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025B9JointGraph
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels BoundedBetheTransfer
open Ext025B6GraphCore
variable {L : ℝ} [Fact (0 < L)] {N d : ℕ}

abbrev GraphAmbient (L : ℝ) [Fact (0 < L)] (N d : ℕ) :=
  PiLp 2 (fun _ : Option (Fin d) => HN L N)

def pairMap (j : Fin d) : GraphAmbient L N d →L[ℂ] (HN L N × HN L N) :=
  (PiLp.proj 2 (fun _ : Option (Fin d) => HN L N) none).prod
    (PiLp.proj 2 (fun _ : Option (Fin d) => HN L N) (some j))

/-- A closed subspace of the finite Hilbert direct sum. -/
def graphSpace (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    Submodule ℂ (GraphAmbient L N d) :=
  ⨅ j, (multiplier b (a j)).graph.comap (pairMap j).toLinearMap

theorem mem_graphSpace (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (v : GraphAmbient L N d) : v ∈ graphSpace b a ↔
      ∀ j, ∃ h : v none ∈ (multiplier b (a j)).domain,
        multiplier b (a j) ⟨v none,h⟩ = v (some j) := by
  simp only [graphSpace,Submodule.mem_iInf,Submodule.mem_comap,LinearPMap.mem_graph_iff]
  constructor
  · intro h j
    obtain ⟨u,hu,he⟩ := h j
    change u.val = v none at hu
    change multiplier b (a j) u = v (some j) at he
    refine ⟨hu ▸ u.property,?_⟩
    have heq : (⟨v none,hu ▸ u.property⟩ : (multiplier b (a j)).domain) = u :=
      Subtype.ext hu.symm
    rw [heq]
    exact he
  · intro h j
    obtain ⟨hu,he⟩ := h j
    exact ⟨⟨v none,hu⟩,rfl,he⟩

theorem graphSpace_closed (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    IsClosed (graphSpace b a : Set (GraphAmbient L N d)) := by
  have he : (graphSpace b a : Set (GraphAmbient L N d)) =
      ⋂ j, (pairMap j) ⁻¹' ((multiplier b (a j)).graph : Set (HN L N × HN L N)) := by
    ext v
    simp [graphSpace]
  rw [he]
  exact isClosed_iInter fun j =>
    (BetheChargeResolution.multiplier_selfAdjoint b (a j)).isClosed.preimage (pairMap j).continuous

instance graph_complete (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    CompleteSpace (graphSpace b a) := (graphSpace_closed b a).isComplete.completeSpace_coe

/-- The ambient evaluation is injective, since every other component is
forced by the closed operator graph. -/
def inclusion (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) : graphSpace b a →L[ℂ] HN L N :=
  (PiLp.proj 2 (fun _ : Option (Fin d) => HN L N) none).comp (graphSpace b a).subtypeL

theorem inclusion_injective (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    Injective (inclusion b a) := by
  intro u v huv
  apply Subtype.ext
  apply PiLp.ext
  intro i
  cases i with
  | none => exact huv
  | some j =>
    obtain ⟨hu,heu⟩ := (mem_graphSpace b a u.val).mp u.property j
    obtain ⟨hv,hev⟩ := (mem_graphSpace b a v.val).mp v.property j
    change u.val none = v.val none at huv
    rw [← heu,← hev]
    congr 1
    exact Subtype.ext huv

/-- Every vector in the intersection has its canonical graph lift. -/
def lift (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) (x : HN L N)
    (hx : ∀ j, x ∈ (multiplier b (a j)).domain) : graphSpace b a :=
  ⟨WithLp.toLp 2 (fun i => match i with
    | none => x
    | some j => multiplier b (a j) ⟨x,hx j⟩),
    (mem_graphSpace b a _).mpr (fun j => ⟨hx j,rfl⟩)⟩

theorem inclusion_lift (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (x : HN L N) (hx : ∀ j, x ∈ (multiplier b (a j)).domain) :
    inclusion b a (lift b a x hx) = x := rfl

/-- The range is exactly the common domain, in both directions. -/
theorem inclusion_range (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) :
    Set.range (inclusion b a) = {x | ∀ j, x ∈ (multiplier b (a j)).domain} := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩ j
    exact ((mem_graphSpace b a v.val).mp v.property j).choose
  · intro hx
    exact ⟨lift b a x hx,rfl⟩

/-- The Hilbert norm is literally the source joint graph norm. -/
theorem norm_sq (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (x : HN L N) (hx : ∀ j, x ∈ (multiplier b (a j)).domain) :
    ‖lift b a x hx‖^2 = ‖x‖^2+∑ j, ‖multiplier b (a j) ⟨x,hx j⟩‖^2 := by
  change ‖(lift b a x hx).val‖^2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp [lift,Fintype.sum_option]

/-- Parseval identifies this norm with the full, literal graph weight. -/
theorem norm_sq_density (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (x : HN L N) (hx : ∀ j, x ∈ (multiplier b (a j)).domain) :
    ‖lift b a x hx‖^2 = ∑' m, (1+∑ j, |a j m|^2)*‖b.repr x m‖^2 := by
  rw [norm_sq]
  have hj (j : Fin d) : ‖multiplier b (a j) ⟨x,hx j⟩‖^2 =
      ∑' m, |a j m|^2*‖b.repr x m‖^2 := by
    rw [← b.repr.norm_map,Energy.norm_sq_eq_tsum]
    apply tsum_congr
    intro m
    simp only [HilbertBasis.repr_apply_apply,multiplier_coord,norm_mul,mul_pow,
      Complex.norm_real,Real.norm_eq_abs]
  have hs (j : Fin d) : Summable (fun m => |a j m|^2*‖b.repr x m‖^2) := by
    simpa only [HilbertBasis.repr_apply_apply] using (mem_domain b (a j) x).mp (hx j)
  rw [← b.repr.norm_map,Energy.norm_sq_eq_tsum]
  simp_rw [hj]
  rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => hs j),
    ← (Energy.summable_sq (b.repr x)).tsum_add (summable_sum (fun j _ => hs j))]
  exact tsum_congr fun m => (density_eq b a x m)

/-- The inherited GP-13 tail estimate now converges in the constructed
complete graph Hilbert space itself. -/
theorem finite_core (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (x : HN L N) (hx : ∀ j, x ∈ (multiplier b (a j)).domain) :
    Tendsto (fun F : Finset (MArr N) => lift b a (projection b (F : Set (MArr N)) x)
      (fun j => projection_mem b (a j) (F : Set (MArr N)) x (hx j))) atTop
      (𝓝 (lift b a x hx)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he (F : Finset (MArr N)) :
      ‖lift b a (projection b (F : Set (MArr N)) x)
        (fun j => projection_mem b (a j) (F : Set (MArr N)) x (hx j)) - lift b a x hx‖^2 =
        error b a x hx (F : Set (MArr N)) := by
    change ‖(_ : GraphAmbient L N d)‖^2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    rw [Fintype.sum_option]
    change ‖projection b (F : Set (MArr N)) x-x‖^2 +
      ∑ j, ‖multiplier b (a j) ⟨projection b (F : Set (MArr N)) x,
        projection_mem b (a j) (F : Set (MArr N)) x (hx j)⟩ -
          multiplier b (a j) ⟨x,hx j⟩‖^2 = _
    unfold error
    congr 1
    · rw [norm_sub_rev]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [norm_sub_rev]
  have ht := (graph_core_net b a x hx).congr' (.of_forall fun F => (he F).symm)
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using hr

end QuantumNLS.Ext025B9JointGraph


/-! GP-08 application R-2E4C2F4E: full conjugation to the independently
constructed normalized occupation basis, including exact maximal domains.
No pointwise eigenrelation or conjugacy conclusion is a premise. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Topology Function
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.Ext025B9Occupation
open BetheSpectralCharges BetheCoefficientTransform PhysicalTensor BetheLabels
variable {L : ℝ} [Fact (0 < L)] {N d : ℕ}

/-- The actual occupation basis reindexed by the source Bethe labels. -/
def basis (N : ℕ) : HilbertBasis (MArr N) ℂ (OccupationUnitary.Boson N) :=
  reindexBasis (marrArr N).symm (OccupationUnitary.occupationBasis N)

theorem basis_coord (y : OccupationUnitary.Boson N) (m : MArr N) :
    (basis N).repr y m = OccupationUnitary.U4 N y (marrArr N m) := by
  simp only [basis,HilbertBasis.repr_apply_apply,reindexBasis_apply,Equiv.symm_symm,
    OccupationUnitary.U4,HilbertBasis.repr_apply_apply]

theorem transform_coord (b : BetheBasis L N) (x : HN L N) :
    (basis N).repr (fockTransform b x) = b.repr x := by
  ext m
  rw [basis_coord,fockTransform_coord,HilbertBasis.repr_apply_apply]

/-- Independent maximal multiplication on the occupation sector. -/
def occupationOperator (a : MArr N → ℝ) :
    OccupationUnitary.Boson N →ₗ.[ℂ] OccupationUnitary.Boson N :=
  Ext025B9Diagonal.multiplier (basis N) a

theorem occupation_selfAdjoint (a : MArr N → ℝ) : IsSelfAdjoint (occupationOperator a) :=
  Ext025B9Diagonal.multiplier_selfAdjoint (basis N) a

/-- Exact conjugacy of domains, for each whole symbol separately. -/
theorem domain_iff (b : BetheBasis L N) (a : MArr N → ℝ) (x : HN L N) :
    fockTransform b x ∈ (occupationOperator a).domain ↔ x ∈ (multiplier b a).domain := by
  change Memℓp (fun m => (a m : ℂ)*(basis N).repr (fockTransform b x) m) 2 ↔
    Memℓp (fun m => (a m : ℂ)*b.repr x m) 2
  rw [transform_coord]

/-- The conjugate has exactly the same multiplied coefficients and value. -/
theorem conjugacy (b : BetheBasis L N) (a : MArr N → ℝ) (x : HN L N)
    (hx : x ∈ (multiplier b a).domain) :
    occupationOperator a ⟨fockTransform b x,(domain_iff b a x).mpr hx⟩ =
      fockTransform b (multiplier b a ⟨x,hx⟩) := by
  apply (basis N).repr.injective
  ext m
  rw [transform_coord]
  have ho := Ext025B9Diagonal.multiplier_coord (basis N) a
    ⟨fockTransform b x,(domain_iff b a x).mpr hx⟩ m
  simp only [← HilbertBasis.repr_apply_apply,transform_coord] at ho
  have hp := multiplier_coord b a ⟨x,hx⟩ m
  simp only [← HilbertBasis.repr_apply_apply] at hp
  exact ho.trans hp.symm

/-- Both input and output coordinates characterize graph membership;
this states the operator equality without suppressing either domain. -/
theorem graph_conjugacy (b : BetheBasis L N) (a : MArr N → ℝ) (x y : HN L N) :
    (fockTransform b x,fockTransform b y) ∈ (occupationOperator a).graph ↔
      (x,y) ∈ (multiplier b a).graph := by
  simp only [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u,hu,hy⟩
    have hx : x ∈ (multiplier b a).domain := (domain_iff b a x).mp (hu ▸ u.property)
    refine ⟨⟨x,hx⟩,rfl,?_⟩
    apply (fockTransform b).injective
    rw [← conjugacy b a x hx]
    exact (congrArg (occupationOperator a) (Subtype.ext hu)).symm.trans hy
  · rintro ⟨u,hu,hy⟩
    subst x
    exact ⟨⟨fockTransform b u.val,(domain_iff b a u.val).mpr u.property⟩,rfl,
      (conjugacy b a u.val u.property).trans (congrArg (fockTransform b) hy)⟩

/-- Finite common domains are transported exactly as well. This does not
replace a maximal summed-symbol domain by an intersection. -/
theorem common_domain_iff (b : BetheBasis L N) (a : Fin d → MArr N → ℝ) (x : HN L N) :
    (∀ j, fockTransform b x ∈ (occupationOperator (a j)).domain) ↔
      ∀ j, x ∈ (multiplier b (a j)).domain := by
  simp only [domain_iff]

/-- Every real joint symbol, including cancelling sums, retains its own
square-integrability domain under the occupation conjugacy. -/
theorem joint_symbol_domain (b : BetheBasis L N) (a : Fin d → MArr N → ℝ)
    (f : (Fin d → ℝ) → ℝ) (x : HN L N) :
    fockTransform b x ∈ (occupationOperator (fun m => f (Ext025B7JointResolution.tuple a m))).domain ↔
      (∫⁻ t, ENNReal.ofReal (|f t|^2) ∂Ext025B7JointResolution.jointMeasure b a x) ≠ ⊤ :=
  (domain_iff b _ x).trans (Ext025B7JointResolution.joint_domain_iff b a f x)

/-- The occupation conjugacy instantiated at the proved physical Bethe
basis, with no supplied continuity or completeness conclusion. -/
theorem physical_conjugacy (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (hN : 0 < N) (a : MArr N → ℝ) (x : HN L N)
    (hx : x ∈ (multiplier (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) a).domain) :
    occupationOperator a ⟨fockTransform (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) x,
      (domain_iff _ a x).mpr hx⟩ =
      fockTransform (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
        (multiplier (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) a ⟨x,hx⟩) :=
  conjugacy _ a x hx

/-- Completeness is derived for the actual physical common charge domain. -/
theorem physical_graph_complete (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ)
    (hN : 0 < N) (a : Fin d → MArr N → ℝ) :
    CompleteSpace (Ext025B9JointGraph.graphSpace
      (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) a) := inferInstance

end QuantumNLS.Ext025B9Occupation


/-! GP-08: the arbitrary-PVM Borel vector integral assembled into a
linear operator on exactly the maximal scalar-square-integral domain.
A global spectral representation of a physical Hamiltonian is not an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B9MaximalIntegral
open BetheChargeResolution Ext025B6PVM Ext025B8BorelCalculus Ext025B7PVMForms
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

/-- The parallelogram estimate supplies domain addition without assuming
linearity of the still-unassembled vector integral. -/
theorem scalarMeasure_add_le (x y : E) :
    scalarMeasure P (x+y) ≤ (2 : ℝ≥0∞) • scalarMeasure P x + (2 : ℝ≥0∞) • scalarMeasure P y := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    scalarMeasure_apply P _ s hs,map_add]
  have h : ‖P.toFun s x+P.toFun s y‖^2 ≤ 2*‖P.toFun s x‖^2+2*‖P.toFun s y‖^2 := by
    have hn := norm_add_le (P.toFun s x) (P.toFun s y)
    have hsq := sq_nonneg (‖P.toFun s x‖-‖P.toFun s y‖)
    nlinarith [norm_nonneg (P.toFun s x+P.toFun s y)]
  calc
    _ ≤ ENNReal.ofReal (2*‖P.toFun s x‖^2+2*‖P.toFun s y‖^2) := ENNReal.ofReal_le_ofReal h
    _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]; norm_num

theorem energy_add_le (w : ℝ → ℝ≥0∞) (x y : E) :
    energy P w (x+y) ≤ 2*energy P w x+2*energy P w y := by
  have h := lintegral_mono' (scalarMeasure_add_le P x y) (le_refl w)
  simpa only [energy,lintegral_add_measure,lintegral_smul_measure,smul_eq_mul] using h

/-- The exact domain, with no intersection of separate summand domains. -/
def domain (f : ℝ → ℂ) : Submodule ℂ E where
  carrier := {x | energy P (fun t => ENNReal.ofReal (‖f t‖^2)) x ≠ ⊤}
  zero_mem' := by
    have hz : scalarMeasure P (0 : E) = 0 := by
      apply Measure.ext
      intro s hs
      rw [scalarMeasure_apply P 0 s hs]
      simp
    simp [energy,hz]
  add_mem' := by
    intro x y hx hy
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hx,
        ENNReal.mul_ne_top (by norm_num) hy⟩) (energy_add_le P _ x y)
  smul_mem' := by
    intro c x hx
    let B : E →L[ℂ] E := c • ContinuousLinearMap.id ℂ E
    have hB : Commutes P B := by
      intro s hs
      apply ContinuousLinearMap.ext
      intro y
      change c • P.toFun s y = P.toFun s (c • y)
      exact (map_smul _ _ _).symm
    exact bounded_form_domain P B hB _ x hx

/-- Membership is precisely square integrability against the vector's
own scalar spectral measure. -/
theorem mem_domain (f : ℝ → ℂ) (hf : Measurable f) (x : E) :
    x ∈ domain P f ↔ MemLp f 2 (scalarMeasure P x) :=
  (square_domain_iff P f hf x).symm

/-- Unbounded spectral integration, now a partial linear operator. -/
def operator (f : ℝ → ℂ) (hf : Measurable f) : E →ₗ.[ℂ] E where
  domain := domain P f
  toFun :=
    { toFun := fun x => vectorIntegral P f x.val ((mem_domain P f hf x.val).mp x.property)
      map_add' := by
        intro x y
        have hx := approx_integral P f hf x.val ((mem_domain P f hf x.val).mp x.property)
        have hy := approx_integral P f hf y.val ((mem_domain P f hf y.val).mp y.property)
        exact tendsto_nhds_unique
          (approx_integral P f hf (x+y).val ((mem_domain P f hf (x+y).val).mp (x+y).property))
          (by simpa only [Submodule.coe_add,map_add] using hx.add hy)
      map_smul' := by
        intro c x
        have hx := approx_integral P f hf x.val ((mem_domain P f hf x.val).mp x.property)
        exact tendsto_nhds_unique
          (approx_integral P f hf (c • x).val ((mem_domain P f hf (c • x).val).mp (c • x).property))
          (by simpa only [Submodule.coe_smul,map_smul,RingHom.id_apply] using hx.const_smul c) }

theorem operator_apply (f : ℝ → ℂ) (hf : Measurable f) (x : (operator P f hf).domain) :
    operator P f hf x = vectorIntegral P f x.val ((mem_domain P f hf x.val).mp x.property) := rfl

theorem operator_esquare (f : ℝ → ℂ) (hf : Measurable f) (x : (operator P f hf).domain) :
    ENNReal.ofReal (‖operator P f hf x‖^2) =
      ∫⁻ t, ENNReal.ofReal (‖f t‖^2) ∂scalarMeasure P x.val :=
  vectorIntegral_esquare P f x.val _

theorem operator_square (f : ℝ → ℂ) (hf : Measurable f) (x : (operator P f hf).domain) :
    ‖operator P f hf x‖^2 = ∫ t, ‖f t‖^2 ∂scalarMeasure P x.val :=
  vectorIntegral_square P f x.val _

/-- The maximal operator extends every already constructed bounded integral. -/
theorem bounded_agrees (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ t, ‖f t‖ ≤ C) (x : E) :
    ∃ hx : x ∈ (operator P f hf).domain,
      operator P f hf ⟨x,hx⟩ = bounded P f hf C hC hb x := by
  exact ⟨(mem_domain P f hf x).mpr (MemLp.of_bound hf.aestronglyMeasurable C (.of_forall hb)),rfl⟩

end QuantumNLS.Ext025B9MaximalIntegral


/-! GP-08: density of the constructed maximal domain and exact reduction
by each original measurable spectral projection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B9IntegralDomain
open BetheChargeResolution Ext025B6PVM Ext025B8SimpleCalculus Ext025B8BorelCalculus
open Ext025B9MaximalIntegral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

/-- Spectral restriction preserves the full maximal domain. -/
theorem projection_mem (f : ℝ → ℂ) (s : Set ℝ) (hs : MeasurableSet s)
    (x : E) (hx : x ∈ domain P f) : P.toFun s x ∈ domain P f :=
  Ext025B7PVMForms.projection_form_domain P s hs _ x hx

/-- Reduction includes the unbounded operator's actual values. -/
theorem projection_commutes (f : ℝ → ℂ) (hf : Measurable f) (s : Set ℝ)
    (hs : MeasurableSet s) (x : E) (hx : x ∈ domain P f) :
    operator P f hf ⟨P.toFun s x,projection_mem P f s hs x hx⟩ =
      P.toFun s (operator P f hf ⟨x,hx⟩) := by
  have hl := approx_integral P f hf (P.toFun s x)
    ((mem_domain P f hf _).mp (projection_mem P f s hs x hx))
  have hr := (P.toFun s).continuous.continuousAt.tendsto.comp
    (approx_integral P f hf x ((mem_domain P f hf x).mp hx))
  change vectorIntegral P f (P.toFun s x) _ = P.toFun s (vectorIntegral P f x _)
  apply tendsto_nhds_unique hl
  exact hr.congr' (.of_forall fun n =>
    (congrArg (fun T : E →L[ℂ] E => T x)
      (simple_commutes P (approx f hf n) s hs).eq).symm)

/-- On a set where the symbol is bounded, every projected vector belongs
to the maximal domain. -/
theorem bounded_window_mem (f : ℝ → ℂ) (hf : Measurable f) (s : Set ℝ)
    (hs : MeasurableSet s) (C : ℝ) (hb : ∀ t ∈ s, ‖f t‖ ≤ C) (x : E) :
    P.toFun s x ∈ domain P f := by
  apply (mem_domain P f hf _).mpr
  rw [scalarMeasure_project P s hs]
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hs] with t ht
  exact hb t ht

/-- Symbol-size windows exhaust the whole line even for an unbounded
finite-valued Borel symbol. -/
theorem windows_exhaust (f : ℝ → ℂ) :
    ⋃ n : ℕ, {t | ‖f t‖ ≤ (n : ℝ)} = Set.univ := by
  ext t
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
  exact exists_nat_ge ‖f t‖

/-- The maximal operator is densely defined. No global spectral
representation or countable spectral multiplicity is needed. -/
theorem domain_dense (f : ℝ → ℂ) (hf : Measurable f) :
    Dense (domain P f : Set E) := by
  intro x
  have hs (n : ℕ) : MeasurableSet {t | ‖f t‖ ≤ (n : ℝ)} := measurableSet_le hf.norm measurable_const
  have ht := Ext025B7SpectralCompression.exhaustion_strong P
    (fun n : ℕ => {t | ‖f t‖ ≤ (n : ℝ)}) hs
    (fun m n hmn t ht => show ‖f t‖ ≤ (n : ℝ) from
      (show ‖f t‖ ≤ (m : ℝ) from ht).trans (Nat.cast_le.mpr hmn)) (windows_exhaust f) x
  exact mem_closure_of_tendsto ht (.of_forall fun n =>
    bounded_window_mem P f hf _ (hs n) n (fun _ ht => ht) x)

/-- Approximants of a real symbol are literally real-valued. -/
theorem real_approx_star (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) :
    (approx (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf) n).map star =
      approx (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf) n := by
  ext t
  have h := SimpleFunc.approxOn_mem (Complex.measurable_ofReal.comp hf)
    (s := Set.range (fun t => (f t : ℂ)) ∪ {0})
    (by simp : (0 : ℂ) ∈ Set.range (fun t => (f t : ℂ)) ∪ {0}) n t
  change approx (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf) n t ∈
    Set.range (fun t => (f t : ℂ)) ∪ {0} at h
  change star (approx (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf) n t) = _
  rcases h with ⟨u,hu⟩ | h
  · rw [← hu]
    exact Complex.conj_ofReal _
  · rw [Set.mem_singleton_iff.mp h,star_zero]

/-- A real unbounded symbol gives a symmetric operator on its entire
maximal square-integral domain. -/
theorem real_formalAdjoint (f : ℝ → ℝ) (hf : Measurable f) :
    (operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf)).IsFormalAdjoint
      (operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf)) := by
  intro x y
  let g : ℝ → ℂ := fun t => (f t : ℂ)
  have hg : Measurable g := Complex.measurable_ofReal.comp hf
  have hx := approx_integral P g hg x.val ((mem_domain P g hg x.val).mp x.property)
  have hy := approx_integral P g hg y.val ((mem_domain P g hg y.val).mp y.property)
  have hl := hx.inner (𝕜 := ℂ) (tendsto_const_nhds (x := y.val))
  have hr := (tendsto_const_nhds (x := x.val)).inner (𝕜 := ℂ) hy
  change ⟪vectorIntegral P g x.val _,y.val⟫_ℂ = ⟪x.val,vectorIntegral P g y.val _⟫_ℂ
  apply tendsto_nhds_unique hl
  apply hr.congr'
  apply Eventually.of_forall
  intro n
  have ha : (simple P (approx g hg n)).adjoint = simple P (approx g hg n) := by
    rw [simple_star,real_approx_star f hf n]
  have hpair := ContinuousLinearMap.adjoint_inner_left (simple P (approx g hg n)) y.val x.val
  rw [ha] at hpair
  exact hpair.symm

end QuantumNLS.Ext025B9IntegralDomain


/-! GP-08: bounded-window identification for the constructed maximal
Borel operator, including the literal square-root cutoff of R-C17D95AA. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B9IntegralCutoff
open BetheChargeResolution Ext025B6PVM Ext025B8SimpleCalculus Ext025B8BorelCalculus
open Ext025B8BorelLaws Ext025B9MaximalIntegral Ext025B9IntegralDomain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem simple_restrict (f : SimpleFunc ℝ ℂ) (s : Set ℝ) (hs : MeasurableSet s) :
    simple P (f.restrict s) = simple P f * P.toFun s := by
  let χ : SimpleFunc ℝ ℂ := SimpleFunc.piecewise s hs (SimpleFunc.const ℝ 1) (SimpleFunc.const ℝ 0)
  have he : f.restrict s = f*χ := by
    ext t
    by_cases ht : t ∈ s <;> simp [SimpleFunc.restrict_apply f hs,χ,ht]
  rw [he,simple_mul,simple_indicator]

/-- Identify the unbounded integral on a bounded spectral window with the
constructed bounded integral of the restricted symbol. -/
theorem window_action (f : ℝ → ℂ) (hf : Measurable f) (s : Set ℝ) (hs : MeasurableSet s)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ∈ s, ‖f t‖ ≤ C) (x : E) :
    operator P f hf ⟨P.toFun s x,bounded_window_mem P f hf s hs C hb x⟩ =
      bounded P (s.indicator f) (hf.indicator hs) C hC
        (fun t => by by_cases ht : t ∈ s <;> simp [ht,hb t,hC]) x := by
  let g : ℕ → SimpleFunc ℝ ℂ := fun n => (approx f hf n).restrict s
  have hg (n : ℕ) (t : ℝ) : ‖g n t‖ ≤ 2*C := by
    by_cases ht : t ∈ s
    · have hn := SimpleFunc.norm_approxOn_zero_le hf
        (s := Set.range f ∪ {0}) (by simp : (0 : ℂ) ∈ Set.range f ∪ {0}) t n
      change ‖approx f hf n t‖ ≤ ‖f t‖+‖f t‖ at hn
      simpa only [g,SimpleFunc.restrict_apply _ hs,Set.indicator_of_mem ht] using
        hn.trans (by linarith [hb t ht])
    · simp [g,SimpleFunc.restrict_apply _ hs,ht,mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC]
  have htarget (t : ℝ) : ‖s.indicator f t‖ ≤ 2*C := by
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht]
      linarith [hb t ht]
    · rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  have hpt (t : ℝ) : Tendsto (fun n => g n t) atTop (𝓝 (s.indicator f t)) := by
    by_cases ht : t ∈ s
    · simpa only [g,SimpleFunc.restrict_apply _ hs,Set.indicator_of_mem ht] using approx_pointwise f hf t
    · simp only [g,SimpleFunc.restrict_apply _ hs,Set.indicator_of_notMem ht]
      exact tendsto_const_nhds
  have hl := approx_integral P f hf (P.toFun s x)
    ((mem_domain P f hf _).mp (bounded_window_mem P f hf s hs C hb x))
  have hr := bounded_strong P (fun n => g n) (s.indicator f) (fun n => (g n).measurable)
    (hf.indicator hs) (2*C) (by positivity) hg htarget hpt x
  have he (n : ℕ) : simple P (approx f hf n) (P.toFun s x) =
      bounded P (g n) (g n).measurable (2*C) (by positivity) (hg n) x := by
    rw [bounded_simple]
    change simple P (approx f hf n) (P.toFun s x) = simple P ((approx f hf n).restrict s) x
    rw [simple_restrict P (approx f hf n) s hs]
    rfl
  have hh := tendsto_nhds_unique hl (hr.congr' (.of_forall fun n => (he n).symm))
  exact hh

/-- The full unbounded square-root integral on its maximal first-moment domain. -/
def spectralRoot : E →ₗ.[ℂ] E :=
  operator P (fun t : ℝ => (Real.sqrt t : ℂ))
    (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)

/-- R-C17D95AA: every [1,M] cutoff lies in the square-root domain, and
S P_M is exactly the previously constructed bounded sqrt(t) cutoff. -/
theorem root_cutoff (M : ℝ) (x : E) :
    ∃ hx : P.toFun (Set.Icc 1 M) x ∈ (spectralRoot P).domain,
      spectralRoot P ⟨P.toFun (Set.Icc 1 M) x,hx⟩ =
        Ext025B8EnergyCompression.rootCutoff P M x := by
  have hb (t : ℝ) (ht : t ∈ Set.Icc 1 M) : ‖(Real.sqrt t : ℂ)‖ ≤ Real.sqrt M := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using
      Real.sqrt_le_sqrt ht.2
  refine ⟨bounded_window_mem P _ (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)
    _ measurableSet_Icc (Real.sqrt M) hb x,?_⟩
  exact window_action P _ (Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable)
    _ measurableSet_Icc (Real.sqrt M) (Real.sqrt_nonneg M) hb x

/-- On positive spectral support, the exact square-root domain is the
finite first scalar moment, including its infinity case. -/
theorem root_domain (hpos : P.toFun (Set.Ici 1) = 1) (x : E) :
    x ∈ (spectralRoot P).domain ↔
      (∫⁻ t, ENNReal.ofReal t ∂scalarMeasure P x) ≠ ⊤ := by
  have he : scalarMeasure P x = (scalarMeasure P x).restrict (Set.Ici 1) := by
    have h := scalarMeasure_project P (Set.Ici 1) measurableSet_Ici x
    rw [hpos] at h
    exact h
  change (∫⁻ t, ENNReal.ofReal (‖(Real.sqrt t : ℂ)‖^2) ∂scalarMeasure P x) ≠ ⊤ ↔ _
  have hh : (fun t : ℝ => ENNReal.ofReal (‖(Real.sqrt t : ℂ)‖^2)) =ᵐ[scalarMeasure P x]
      (fun t => ENNReal.ofReal t) := by
    rw [he]
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (zero_le_one.trans ht)]
  rw [lintegral_congr_ae hh]

end QuantumNLS.Ext025B9IntegralCutoff


/-! GP-08: real-symbol selfadjointness of the constructed arbitrary-PVM
maximal integral. The adjoint domain is derived by bounded spectral tests
and monotone convergence; it is never assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory Filter Topology Function
open scoped InnerProductSpace ENNReal LinearPMap
namespace QuantumNLS.Ext025B9SelfAdjoint
open BetheChargeResolution Ext025B6PVM Ext025B8BorelCalculus Ext025B8BorelLaws
open Ext025B9MaximalIntegral Ext025B9IntegralDomain Ext025B9IntegralCutoff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (P : ProjectionMeasure E)

theorem real_selfAdjoint (f : ℝ → ℝ) (hf : Measurable f) :
    IsSelfAdjoint (operator P (fun t => (f t : ℂ)) (Complex.measurable_ofReal.comp hf)) := by
  let g : ℝ → ℂ := fun t => (f t : ℂ)
  have hg : Measurable g := Complex.measurable_ofReal.comp hf
  let T := operator P g hg
  have hd : Dense (T.domain : Set E) := domain_dense P g hg
  have hle : T ≤ T† := LinearPMap.IsFormalAdjoint.le_adjoint hd (real_formalAdjoint P f hf)
  have hdom : T†.domain ≤ T.domain := by
    intro y hy
    let z := T† ⟨y,hy⟩
    let s : ℕ → Set ℝ := fun n => {t | ‖g t‖ ≤ (n : ℝ)}
    have hs (n : ℕ) : MeasurableSet (s n) := measurableSet_le hg.norm measurable_const
    have hb (n : ℕ) (t : ℝ) : ‖(s n).indicator g t‖ ≤ (n : ℝ) := by
      by_cases ht : t ∈ s n
      · rw [Set.indicator_of_mem ht]; exact ht
      · rw [Set.indicator_of_notMem ht,norm_zero]; exact Nat.cast_nonneg n
    let B (n : ℕ) : E →L[ℂ] E :=
      bounded P ((s n).indicator g) (hg.indicator (hs n)) n (Nat.cast_nonneg n) (hb n)
    have hB (n : ℕ) : (B n).adjoint = B n := by
      have he : (fun t => star ((s n).indicator g t)) = (s n).indicator g := by
        ext t
        by_cases ht : t ∈ s n <;> simp [ht,g]
      change (bounded P _ _ _ _ _).adjoint = _
      rw [bounded_star]
      simp only [he]
      rfl
    have hw (n : ℕ) (x : E) :
        T ⟨P.toFun (s n) x,bounded_window_mem P g hg (s n) (hs n) n (fun _ ht => ht) x⟩ = B n x :=
      window_action P g hg (s n) (hs n) n (Nat.cast_nonneg n) (fun _ ht => ht) x
    have heq (n : ℕ) : B n y = P.toFun (s n) z := by
      apply ext_inner_right ℂ
      intro x
      calc
        ⟪B n y,x⟫_ℂ = ⟪y,B n x⟫_ℂ := by
          simpa only [hB n] using
            (ContinuousLinearMap.adjoint_inner_left (B n) x y)
        _ = ⟪z,P.toFun (s n) x⟫_ℂ := by
          rw [← hw n x]
          exact (LinearPMap.adjoint_isFormalAdjoint hd ⟨y,hy⟩
            ⟨P.toFun (s n) x,bounded_window_mem P g hg (s n) (hs n) n (fun _ ht => ht) x⟩).symm
        _ = ⟪P.toFun (s n) z,x⟫_ℂ := (inner_project P (s n) (hs n) z x).symm
    have hi (n : ℕ) :
        (∫⁻ t, ENNReal.ofReal (‖(s n).indicator g t‖^2) ∂scalarMeasure P y) ≤
          ENNReal.ofReal (‖z‖^2) := by
      rw [← vectorIntegral_esquare P ((s n).indicator g) y
        (MemLp.of_bound (hg.indicator (hs n)).aestronglyMeasurable n (.of_forall (hb n)))]
      change ENNReal.ofReal (‖B n y‖^2) ≤ _
      rw [heq n]
      exact ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (projection_norm_le P _ (hs n) z) 2)
    let w : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (‖(s n).indicator g t‖^2)
    have hm : Monotone w := by
      intro m n hmn t
      by_cases ht : t ∈ s m
      · have ht' : t ∈ s n := (show ‖g t‖ ≤ (m : ℝ) from ht).trans (Nat.cast_le.mpr hmn)
        simp only [w,Set.indicator_of_mem ht,Set.indicator_of_mem ht']
        exact le_rfl
      · simp only [w,Set.indicator_of_notMem ht,norm_zero,zero_pow (by norm_num : 2 ≠ 0),ENNReal.ofReal_zero]
        exact bot_le
    have hsup (t : ℝ) : (⨆ n, w n t) = ENNReal.ofReal (‖g t‖^2) := by
      apply le_antisymm
      · apply iSup_le
        intro n
        by_cases ht : t ∈ s n
        · simp only [w,Set.indicator_of_mem ht]
          exact le_rfl
        · simp [w,Set.indicator_of_notMem ht]
      · obtain ⟨n,hn⟩ := exists_nat_ge ‖g t‖
        have ht : t ∈ s n := hn
        exact (show ENNReal.ofReal (‖g t‖^2) = w n t by simp only [w,Set.indicator_of_mem ht]).le.trans (le_iSup (w · t) n)
    have hfinite : (∫⁻ t, ENNReal.ofReal (‖g t‖^2) ∂scalarMeasure P y) ≤ ENNReal.ofReal (‖z‖^2) := by
      calc
        _ = ∫⁻ t, ⨆ n, w n t ∂scalarMeasure P y := by simp only [hsup]
        _ = ⨆ n, ∫⁻ t, w n t ∂scalarMeasure P y :=
          lintegral_iSup (fun n => ENNReal.measurable_ofReal.comp ((hg.indicator (hs n)).norm.pow_const 2)) hm
        _ ≤ _ := iSup_le hi
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfinite
  exact LinearPMap.isSelfAdjoint_def.mpr
    (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

theorem spectralRoot_selfAdjoint : IsSelfAdjoint (spectralRoot P) :=
  real_selfAdjoint P Real.sqrt Real.continuous_sqrt.measurable

end QuantumNLS.Ext025B9SelfAdjoint

#print axioms QuantumNLS.Ext025B9Diagonal.domain
#print axioms QuantumNLS.Ext025B9Diagonal.mem_domain
#print axioms QuantumNLS.Ext025B9Diagonal.multiplier
#print axioms QuantumNLS.Ext025B9Diagonal.multiplier_coord
#print axioms QuantumNLS.Ext025B9Diagonal.maximal
#print axioms QuantumNLS.Ext025B9Diagonal.basis_mem_domain
#print axioms QuantumNLS.Ext025B9Diagonal.multiplier_basis
#print axioms QuantumNLS.Ext025B9Diagonal.domain_dense
#print axioms QuantumNLS.Ext025B9Diagonal.constant_domain
#print axioms QuantumNLS.Ext025B9Diagonal.constant_apply
#print axioms QuantumNLS.Ext025B9Diagonal.multiplier_formalAdjoint
#print axioms QuantumNLS.Ext025B9Diagonal.multiplier_selfAdjoint
#print axioms QuantumNLS.Ext025B9JointGraph.pairMap
#print axioms QuantumNLS.Ext025B9JointGraph.graphSpace
#print axioms QuantumNLS.Ext025B9JointGraph.mem_graphSpace
#print axioms QuantumNLS.Ext025B9JointGraph.graphSpace_closed
#print axioms QuantumNLS.Ext025B9JointGraph.graph_complete
#print axioms QuantumNLS.Ext025B9JointGraph.inclusion
#print axioms QuantumNLS.Ext025B9JointGraph.inclusion_injective
#print axioms QuantumNLS.Ext025B9JointGraph.lift
#print axioms QuantumNLS.Ext025B9JointGraph.inclusion_lift
#print axioms QuantumNLS.Ext025B9JointGraph.inclusion_range
#print axioms QuantumNLS.Ext025B9JointGraph.norm_sq
#print axioms QuantumNLS.Ext025B9JointGraph.norm_sq_density
#print axioms QuantumNLS.Ext025B9JointGraph.finite_core
#print axioms QuantumNLS.Ext025B9Occupation.physical_conjugacy
#print axioms QuantumNLS.Ext025B9Occupation.physical_graph_complete
#print axioms QuantumNLS.Ext025B9Occupation.basis
#print axioms QuantumNLS.Ext025B9Occupation.basis_coord
#print axioms QuantumNLS.Ext025B9Occupation.transform_coord
#print axioms QuantumNLS.Ext025B9Occupation.occupationOperator
#print axioms QuantumNLS.Ext025B9Occupation.occupation_selfAdjoint
#print axioms QuantumNLS.Ext025B9Occupation.domain_iff
#print axioms QuantumNLS.Ext025B9Occupation.conjugacy
#print axioms QuantumNLS.Ext025B9Occupation.graph_conjugacy
#print axioms QuantumNLS.Ext025B9Occupation.common_domain_iff
#print axioms QuantumNLS.Ext025B9Occupation.joint_symbol_domain
#print axioms QuantumNLS.Ext025B9MaximalIntegral.scalarMeasure_add_le
#print axioms QuantumNLS.Ext025B9MaximalIntegral.energy_add_le
#print axioms QuantumNLS.Ext025B9MaximalIntegral.domain
#print axioms QuantumNLS.Ext025B9MaximalIntegral.mem_domain
#print axioms QuantumNLS.Ext025B9MaximalIntegral.operator
#print axioms QuantumNLS.Ext025B9MaximalIntegral.operator_apply
#print axioms QuantumNLS.Ext025B9MaximalIntegral.operator_esquare
#print axioms QuantumNLS.Ext025B9MaximalIntegral.operator_square
#print axioms QuantumNLS.Ext025B9MaximalIntegral.bounded_agrees
#print axioms QuantumNLS.Ext025B9IntegralDomain.projection_mem
#print axioms QuantumNLS.Ext025B9IntegralDomain.projection_commutes
#print axioms QuantumNLS.Ext025B9IntegralDomain.bounded_window_mem
#print axioms QuantumNLS.Ext025B9IntegralDomain.windows_exhaust
#print axioms QuantumNLS.Ext025B9IntegralDomain.domain_dense
#print axioms QuantumNLS.Ext025B9IntegralDomain.real_approx_star
#print axioms QuantumNLS.Ext025B9IntegralDomain.real_formalAdjoint
#print axioms QuantumNLS.Ext025B9IntegralCutoff.simple_restrict
#print axioms QuantumNLS.Ext025B9IntegralCutoff.window_action
#print axioms QuantumNLS.Ext025B9IntegralCutoff.spectralRoot
#print axioms QuantumNLS.Ext025B9IntegralCutoff.root_cutoff
#print axioms QuantumNLS.Ext025B9IntegralCutoff.root_domain
#print axioms QuantumNLS.Ext025B9SelfAdjoint.spectralRoot_selfAdjoint
#print axioms QuantumNLS.Ext025B9SelfAdjoint.real_selfAdjoint

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B9" then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Ext025B9Bridges audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
