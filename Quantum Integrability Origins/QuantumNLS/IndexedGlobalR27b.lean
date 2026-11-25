import QuantumNLS.IndexedFieldR27b
import QuantumNLS.RootMassPropernessR27
import QuantumNLS.Ext025A6CompactFlow
import QuantumNLS.Ext025A8Global

/-! LOCAL-016 classical completeness from the compact actual indexed-mass
fibres. The field and its first integrals are those of the physical L2
Hamiltonian. A global trajectory is constructed, never supplied. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open scoped NNReal
namespace QuantumNLS.IndexedGlobalR27b
open PhysicalTensor (L2T)
open IndexedFieldR27b
attribute [local instance] InnerProductSpace.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

def fibre (hκ : 0 < κ) (u : L2T L) : Set (L2T L) :=
  (RootIndexedMasses.masses hκ) ⁻¹' {RootIndexedMasses.masses hκ u}

theorem compact_fibre (hκ : 0 < κ) (u : L2T L) : IsCompact (fibre hκ u) :=
  (RootMassPropernessR27.root_mass_properness hκ).2.2.2.1 _

theorem contDiff_field (hκ : 0 < κ) (n : ℤ) : ContDiff ℝ 1 (field (L := L) hκ n) :=
  contDiff_iff_contDiffAt.mpr (fun u => (analytic_field hκ n u).contDiffAt)

theorem fibre_lipschitz (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    ∃ K : ℝ≥0, LipschitzOnWith K (field hκ n) (fibre hκ u) :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (compact_fibre hκ u)
    (contDiff_field hκ n).locallyLipschitz.locallyLipschitzOn

theorem global_exists (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    ∃ γ : ℝ → L2T L, γ 0 = u ∧
      ∀ t, HasDerivAt γ (field hκ n (γ t)) t ∧ γ t ∈ fibre hκ u := by
  have hu : u ∈ fibre hκ u := rfl
  obtain ⟨K,hK⟩ := fibre_lipschitz hκ n u
  obtain ⟨r,hr,δ,hδ,hlocal⟩ := Ext025A6.compact_common_local_solutions
    (compact_fibre hκ u) ⟨u,hu⟩
    (fun x _ => (contDiff_field hκ n).contDiffAt) 0
  apply Ext025A8.uniform_invariant_global hK hδ _ hu
  intro x hx
  obtain ⟨γ,hγ0,hγ⟩ := hlocal x hx x (mem_closedBall_self hr.le)
  have hd : ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (field hκ n (γ t)) t := by
    simpa only [zero_sub,zero_add] using hγ
  refine ⟨γ,hγ0,fun t ht => ⟨hd t ht,?_⟩⟩
  have hc := (conservation_on hκ n (show (0 : ℝ) ∈ Ioo (-δ) δ from
    ⟨neg_lt_zero.mpr hδ,hδ⟩) hd t ht).1
  change RootIndexedMasses.masses hκ (γ t) = RootIndexedMasses.masses hκ u
  rw [hc,hγ0]
  exact hx

def flow (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) : L2T L :=
  (global_exists hκ n u).choose t

theorem flow_initial (hκ : 0 < κ) (n : ℤ) (u : L2T L) : flow hκ n 0 u = u :=
  (global_exists hκ n u).choose_spec.1

theorem flow_derivative (hκ : 0 < κ) (n : ℤ) (u : L2T L) (t : ℝ) :
    HasDerivAt (fun s => flow hκ n s u) (field hκ n (flow hκ n t u)) t :=
  ((global_exists hκ n u).choose_spec.2 t).1

theorem time_contDiff (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    ContDiff ℝ 1 (fun t => flow hκ n t u) := by
  have hc : Continuous (fun t => flow hκ n t u) :=
    continuous_iff_continuousAt.mpr (fun t => (flow_derivative hκ n u t).continuousAt)
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (flow_derivative hκ n u t).differentiableAt,?_⟩
  have hd : deriv (fun t => flow hκ n t u) = fun t => field hκ n (flow hκ n t u) :=
    funext (fun t => (flow_derivative hκ n u t).deriv)
  rw [hd]
  exact (contDiff_field hκ n).continuous.comp hc

theorem flow_masses (hκ : 0 < κ) (n : ℤ) (u : L2T L) (t : ℝ) :
    RootIndexedMasses.masses hκ (flow hκ n t u) = RootIndexedMasses.masses hκ u :=
  ((global_exists hκ n u).choose_spec.2 t).2

theorem solution_conservation (hκ : 0 < κ) (n : ℤ) {γ : ℝ → L2T L}
    (hd : ∀ t, HasDerivAt γ (field hκ n (γ t)) t) (t : ℝ) :
    RootIndexedMasses.masses hκ (γ t) = RootIndexedMasses.masses hκ (γ 0) ∧
      ‖γ t‖ = ‖γ 0‖ := by
  apply conservation_on hκ n (a := -(|t|+1)) (b := |t|+1)
    (by constructor <;> linarith [abs_nonneg t]) (fun s _ => hd s) t
  exact abs_lt.mp (lt_add_one |t|)

theorem flow_norm (hκ : 0 < κ) (n : ℤ) (u : L2T L) (t : ℝ) :
    ‖flow hκ n t u‖ = ‖u‖ := by
  simpa only [flow_initial] using (solution_conservation hκ n (flow_derivative hκ n u) t).2

theorem solution_unique (hκ : 0 < κ) (n : ℤ) (u : L2T L) {γ : ℝ → L2T L}
    (hγ0 : γ 0 = u) (hd : ∀ t, HasDerivAt γ (field hκ n (γ t)) t) :
    γ = fun t => flow hκ n t u := by
  obtain ⟨K,hK⟩ := fibre_lipschitz hκ n u
  have hm (t : ℝ) : γ t ∈ fibre hκ u := by
    change RootIndexedMasses.masses hκ (γ t) = RootIndexedMasses.masses hκ u
    rw [(solution_conservation hκ n hd t).1,hγ0]
  exact ODE_solution_unique_univ (t₀ := 0) (fun _ => hK)
    (fun t => ⟨hd t,hm t⟩)
    (fun t => ⟨flow_derivative hκ n u t,flow_masses hκ n u t⟩)
    (hγ0.trans (flow_initial hκ n u).symm)

theorem flow_add (hκ : 0 < κ) (n : ℤ) (u : L2T L) (s t : ℝ) :
    flow hκ n (s+t) u = flow hκ n t (flow hκ n s u) := by
  have he := solution_unique hκ n (flow hκ n s u)
    (γ := fun t => flow hκ n (s+t) u) (by simp)
    (fun t => by
      simpa only [Function.comp_def,one_smul] using
        (flow_derivative hκ n u (s+t)).scomp t ((hasDerivAt_id t).const_add s))
  exact congrFun he t

theorem flow_stationary (hκ : 0 < κ) (n : ℤ) (u : L2T L)
    (hu : field hκ n u = 0) (t : ℝ) : flow hκ n t u = u := by
  have he := solution_unique hκ n u (γ := fun _ => u) rfl
    (fun s => by simpa only [hu] using hasDerivAt_const s u)
  exact (congrFun he t).symm

theorem flow_zero (hκ : 0 < κ) (n : ℤ) (t : ℝ) : flow (L := L) hκ n t 0 = 0 :=
  flow_stationary hκ n 0 (field_zero hκ n) t

theorem flow_plane (hκ : 0 < κ) (n j : ℤ) (hj : j ≠ n) (c : ℂ) (t : ℝ) :
    flow hκ n t (c • Fourier.modeLp L j) = c • Fourier.modeLp L j :=
  flow_stationary hκ n _ (field_plane hκ n j hj c) t

theorem flow_ball_invariant (hκ : 0 < κ) (n : ℤ) (R t : ℝ) :
    MapsTo (flow (L := L) hκ n t) (ball 0 R) (ball 0 R) := by
  intro u hu
  simpa only [mem_ball_zero_iff,flow_norm] using hu

/-- The source's support-independent radius. -/
def delta (L κ : ℝ) : ℝ := Real.sqrt ((1/1000000000000 : ℝ)/(κ*L))

/-- The invariant-ball clause of LOCAL-016, at precisely its printed radius.
The common-period clause is not asserted by this supporting theorem. -/
theorem printed_ball_invariant (hκ : 0 < κ) :
    0 < delta L κ ∧ (delta L κ)^2 = (1/1000000000000 : ℝ)/(κ*L) ∧
      ∀ n : ℤ, ∀ t : ℝ, MapsTo (flow (L := L) hκ n t)
        (ball 0 (delta L κ)) (ball 0 (delta L κ)) := by
  have h : 0 < (1/1000000000000 : ℝ)/(κ*L) := by
    have hL : 0 < L := Fact.out
    positivity
  exact ⟨Real.sqrt_pos.mpr h,Real.sq_sqrt h.le,
    fun n t => flow_ball_invariant hκ n (delta L κ) t⟩

end QuantumNLS.IndexedGlobalR27b
#print axioms QuantumNLS.IndexedGlobalR27b.global_exists
#print axioms QuantumNLS.IndexedGlobalR27b.solution_unique
#print axioms QuantumNLS.IndexedGlobalR27b.flow_ball_invariant
#print axioms QuantumNLS.IndexedGlobalR27b.printed_ball_invariant
