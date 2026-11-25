import Mathlib
import QuantumNLS.RB7FinalR15
import QuantumNLS.RB7Conserve

/-!
# R-7B122087 `thm:hierarchy` / DEF-024: all six printed clauses in one theorem (RB7FinalAll)

Source: `source-text/chapters/core/DYNAMICS_LEMMAS.tex:115-128` (proof to ~198).  Printed clauses and where they are proved:

1. `Clause1`: every fixed `I_{r+1}^{(κ)}` has a global smooth Hamiltonian flow from every smooth datum (`IsHamFlow`: `Φ_0 = id`, joint `C^∞`, `∂_s Φ = -i∇I`, smooth periodic for ALL real `s`), it is unique
   (`UniqueHamFlow`), and it is a one-parameter group.  Statement for every `r : ℕ` (in particular `r ≥ 2`).  [`RB7Final.isHamFlow_chart`, `unique_chart`, `group_chart`.]
2. `Clause2`: finite families commute: for ANY family `F : HamFlows L κ 𝓡` of smooth Hamiltonian flows, all pairs `r, r' ∈ 𝓡`, all real times, `F.Φ r s ∘ F.Φ r' s' = F.Φ r' s' ∘ F.Φ r s` on smooth data
   (all orders, not only `0, 1`), and the composition over every permutation of `𝓡` is `jointClassicalFlow F t`; the joint flow is smooth.  [`RB7Commute`: via the constant-action rotation form.]
3. `Clause3`: in the chart coordinates `Φ` they are constant-action rotations: there are `F_r : h^{S_r} → ℝ` (`S_r = 3(r+2)+1`; `C²`, invariant under coordinatewise rotations, `F_r(Φ f) = Re I_{r+1}(f)`) such that for EVERY
   Hamiltonian flow `Ψ'` of order `r`: `Φ_n(Ψ'_s u) = exp(-i s ω_{r,n}) Φ_n(u)` with `ω_{r,n} = freq F_r (Φ u) n = Re(conj z_n ∇_n F_r)/|z_n|^2`, the moduli `|Φ_n|` are constant, every order's frequency is constant along the orbit and on
   full modulus tori; and `Φ_n(joint flow) = exp(-i Σ_{r∈𝓡} t_r ω_{r,n}) Φ_n(u)`.  [`RB7Rotation`, `RB7Commute.joint_rotation_form`.]
4. `OrbitCompactInput`: relative compactness of full orbits in the smooth topology (`∏_k H^k` topology on smooth profiles).  NOT PROVED HERE: this is haiku_inventory's clause (RB7H* modules, in progress); it enters the final theorem as the explicit hypothesis `hO`.
5. `JointContInput`: continuous dependence on compact smooth initial classes and compact boxes of joint times, in the smooth topology.  NOT PROVED HERE (haiku_inventory); explicit hypothesis `hJ`.
6. `Clause6`: all local charges `I_j^{(κ)}` (`j : ℕ`, complex valued) and all indexed actions are conserved along every smooth Hamiltonian flow of every order and along every joint classical flow.  [`RB7Conserve`.]

REG-015 enters only through `Reg015HFinal.REG015_final` (accepted), by `RB7FinalR15`'s swap.  `hierarchy_1236` is unconditional (given REG-015); `hierarchy_all` adds the two explicit inputs for clauses 4, 5.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.Reg015Setting QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.HierarchyFlow QuantumNLS.LossSobolev QuantumNLS.Def024LowEquivariance

variable {L κ : ℝ} [Fact (0 < L)]

/-! ## The smooth topology -/

open Classical in
/-- The jet of a profile in `∏_{k : ℕ} H^k`: its `L²` class in every `H^k` if it is smooth periodic (`0` otherwise). -/
def jetOf (g : ℝ → ℂ) : ∀ k : ℕ, H02 L (k : ℝ) :=
  fun k => if h : SmoothPeriodic L g then WField.mk (smoothL2 h) (memHs_of_smooth h (k : ℝ)) else 0

/-- Smooth periodic profiles. -/
structure SmoothProf (L : ℝ) where
  val : ℝ → ℂ
  smooth : SmoothPeriodic L val

/-- The smooth topology on smooth profiles: induced by `f ↦ (f in H^k)_k`, the product of all Sobolev topologies. -/
instance (L : ℝ) [Fact (0 < L)] : TopologicalSpace (SmoothProf L) :=
  TopologicalSpace.induced (fun f : SmoothProf L => (jetOf f.val : ∀ k : ℕ, H02 L (k : ℝ))) inferInstance

/-! ## Clauses 4 and 5 (explicit inputs) -/

/-- **Clause (4).**  Full orbits (under all joint times) of smooth data are relatively compact in the smooth topology. -/
def OrbitCompactInput (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) : Prop :=
  ∀ (F : HamFlows L κ 𝓡) (u : SmoothProf L),
    IsCompact (closure (Set.range fun t : ℕ → ℝ => (jetOf (jointClassicalFlow F t u.val) : ∀ k : ℕ, H02 L (k : ℝ))))

/-- **Clause (5).**  The joint flow depends continuously, in the smooth topology, on compact smooth initial classes
and compact boxes of joint times. -/
def JointContInput (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) : Prop :=
  ∀ (F : HamFlows L κ 𝓡) (K : Set (SmoothProf L)) (B : Set (ℕ → ℝ)), IsCompact K → IsCompact B →
    ContinuousOn (fun p : (ℕ → ℝ) × SmoothProf L =>
      (jetOf (jointClassicalFlow F p.1 p.2.val) : ∀ k : ℕ, H02 L (k : ℝ))) (B ×ˢ K)

/-! ## Clauses 1, 2, 3, 6 -/

/-- **Clause (1)**: unique global smooth Hamiltonian flow of `Re I_{r+1}`, every `r`; group law; smooth joint flows. -/
def Clause1 (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) : Prop :=
  (∀ r : ℕ, ∃ Φ : ℝ → (ℝ → ℂ) → (ℝ → ℂ), IsHamFlow L (hamiltonian L κ r) Φ ∧
    UniqueHamFlow L (hamiltonian L κ r) Φ ∧
    ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s a : ℝ, Φ s (Φ a u) = Φ (s + a) u) ∧
  (∃ F : HamFlows L κ 𝓡, ∀ r ∈ 𝓡, UniqueHamFlow L (hamiltonian L κ r) (F.Φ r)) ∧
  (∀ (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (u : ℝ → ℂ), SmoothPeriodic L u →
    SmoothPeriodic L (jointClassicalFlow F t u))

/-- **Clause (2)**: finite families commute (all orders). -/
def Clause2 (L κ : ℝ) [Fact (0 < L)] (𝓡 : Finset ℕ) : Prop :=
  ∀ F : HamFlows L κ 𝓡,
    (∀ r ∈ 𝓡, ∀ r' ∈ 𝓡, ∀ u : ℝ → ℂ, SmoothPeriodic L u → ∀ s s' : ℝ,
      F.Φ r s (F.Φ r' s' u) = F.Φ r' s' (F.Φ r s u)) ∧
    (∀ (t : ℕ → ℝ) (l : List ℕ), l.Perm (𝓡.sort (· ≤ ·)) → ∀ u : ℝ → ℂ, SmoothPeriodic L u →
      ((l.map fun r => F.Φ r (t r)).foldr (· ∘ ·) id) u = jointClassicalFlow F t u)

/-- **Clause (3)**: constant-action rotations in the chart coordinates. -/
def Clause3 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (𝓡 : Finset ℕ) : Prop :=
  ∃ (C : ChartFacts (L := L) hκ) (Fr : ∀ r : ℕ, h02 L ((SOf r : ℝ≥0) : ℝ) → ℝ),
    (∀ r : ℕ, ContDiff ℝ 2 (Fr r) ∧ (∀ (c : ℤ → Circle) z, Fr r (rot c z) = Fr r z) ∧
      ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (z : h02 L ((SOf r : ℝ≥0) : ℝ)),
        z.val = (fun n => C.Φ (smoothL2 hf) n) → Fr r z = (charge L κ f (r + 1)).re) ∧
    (∀ (r : ℕ) (Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)), IsHamFlow L (hamiltonian L κ r) Ψ' →
      ∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)) (n : ℤ),
        (C.Φ (smoothL2 hs) : ℤ → ℂ) n =
          Complex.exp (((-(s * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fr r) (fun m => C.Φ (smoothL2 hu) m) n) : ℝ) : ℂ) *
            Complex.I) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n ∧
        ‖(C.Φ (smoothL2 hs) : ℤ → ℂ) n‖ = ‖(C.Φ (smoothL2 hu) : ℤ → ℂ) n‖ ∧
        ∀ r' : ℕ, FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hs) m) n =
          FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hu) m) n) ∧
    (∀ (r' : ℕ) {u v : ℝ → ℂ} (hu : SmoothPeriodic L u) (hv : SmoothPeriodic L v) (c : ℤ → Circle),
      (∀ n, (C.Φ (smoothL2 hv) : ℤ → ℂ) n = (c n : ℂ) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n) →
      ∀ n, FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hv) m) n =
        FreqSeq ((SOf r' : ℝ≥0) : ℝ) (Fr r') (fun m => C.Φ (smoothL2 hu) m) n) ∧
    (∀ (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (u : ℝ → ℂ) (hu : SmoothPeriodic L u)
      (hj : SmoothPeriodic L (jointClassicalFlow F t u)) (n : ℤ),
        (C.Φ (smoothL2 hj) : ℤ → ℂ) n =
          Complex.exp (((-(∑ r ∈ 𝓡, t r * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fr r)
            (fun m => C.Φ (smoothL2 hu) m) n) : ℝ) : ℂ) * Complex.I) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n)

/-- **Clause (6)**: every local charge and every indexed action is conserved. -/
def Clause6 (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (𝓡 : Finset ℕ) : Prop :=
  (∀ (r : ℕ) (Ψ' : ℝ → (ℝ → ℂ) → (ℝ → ℂ)), IsHamFlow L (hamiltonian L κ r) Ψ' →
    ∀ (u : ℝ → ℂ) (hu : SmoothPeriodic L u) (s : ℝ) (hs : SmoothPeriodic L (Ψ' s u)),
      (∀ j : ℕ, charge L κ (Ψ' s u) j = charge L κ u j) ∧
      ∀ n : ℤ, (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hs)).1 n =
        (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hu)).1 n) ∧
  (∀ (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (u : ℝ → ℂ) (hu : SmoothPeriodic L u)
    (hj : SmoothPeriodic L (jointClassicalFlow F t u)),
      (∀ j : ℕ, charge L κ (jointClassicalFlow F t u) j = charge L κ u j) ∧
      ∀ n : ℤ, (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hj)).1 n =
        (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hu)).1 n)

/-- The printed theorem: all six clauses. -/
def HierarchyAll (L κ : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (𝓡 : Finset ℕ) : Prop :=
  Clause1 L κ 𝓡 ∧ Clause2 L κ 𝓡 ∧ Clause3 L κ hκ 𝓡 ∧ OrbitCompactInput L κ 𝓡 ∧ JointContInput L κ 𝓡 ∧
    Clause6 L κ hκ 𝓡

variable {hκ : 0 < κ}

theorem clause1_of (hR : REG015Concl (L := L) hκ) (𝓡 : Finset ℕ) : Clause1 L κ 𝓡 := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  refine ⟨fun r => ⟨chartFlow hR C r, isHamFlow_chart hR C r, unique_chart hR C r,
      fun u hu s a => group_chart hR C r hu s a⟩, ⟨chartHamFlows hR C 𝓡, fun r _ => unique_chart hR C r⟩, ?_⟩
  intro F t u hu
  exact joint_smooth_of_family hR C F t hu

theorem clause2_of (hR : REG015Concl (L := L) hκ) (𝓡 : Finset ℕ) : Clause2 L κ 𝓡 := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  intro F
  exact ⟨fun r hr r' hr' u hu s s' => comm_pair hR C F hr hr' hu s s',
    fun t l hl u hu => foldr_perm hR C F t hl hu⟩

theorem clause3_of (hR : REG015Concl (L := L) hκ) (𝓡 : Finset ℕ) : Clause3 L κ hκ 𝓡 := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  refine ⟨C, fun r => Fd hR C r, fun r => ⟨Fd_contDiff hR C r, fun c z => Fd_inv hR C r c z, ?_⟩, ?_, ?_, ?_⟩
  · intro f hf z hz
    have : z = zS hR C r hf := WSeq.ext hz
    rw [this]
    exact Fd_charge hR C r hf
  · intro r Ψ' hΨ u hu s hs n
    exact ⟨rotation_form hR C r hΨ hu s hs n, norm_const_flow hR C r hΨ hu s hs n,
      fun r' => freq_flow_const hR C r r' hΨ hu s hs n⟩
  · intro r' u v hu hv c h n
    rw [← omegaOf_eq_FreqSeq, ← omegaOf_eq_FreqSeq]
    exact omegaOf_congr hR C r' hu hv c h n
  · intro F t u hu hj n
    exact joint_rotation_form hR C F t hu hj n

theorem clause6_of (hR : REG015Concl (L := L) hκ) (𝓡 : Finset ℕ) : Clause6 L κ hκ 𝓡 := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  refine ⟨fun r Ψ' hΨ u hu s hs => ⟨fun j => charge_conserved hR C r hΨ hu s hs j,
      fun n => actions_conserved hR C r hΨ hu s hs n⟩, fun F t u hu hj => ⟨fun j => ?_, fun n => ?_⟩⟩
  · exact joint_charge_conserved hR C F t hu j
  · exact joint_actions_conserved hR C F t hu hj n

/-- Clauses `(1), (2), (3), (6)` of `thm:hierarchy` from REG-015 alone. -/
theorem hierarchy_1236_of (hR : REG015Concl (L := L) hκ) (𝓡 : Finset ℕ) :
    Clause1 L κ 𝓡 ∧ Clause2 L κ 𝓡 ∧ Clause3 L κ hκ 𝓡 ∧ Clause6 L κ hκ 𝓡 :=
  ⟨clause1_of hR 𝓡, clause2_of hR 𝓡, clause3_of hR 𝓡, clause6_of hR 𝓡⟩

/-- All six clauses, from REG-015 and the two explicit inputs for clauses (4) and (5). -/
theorem hierarchy_all_of (hR : REG015Concl (L := L) hκ) (𝓡 : Finset ℕ)
    (hO : OrbitCompactInput L κ 𝓡) (hJ : JointContInput L κ 𝓡) : HierarchyAll L κ hκ 𝓡 :=
  ⟨clause1_of hR 𝓡, clause2_of hR 𝓡, clause3_of hR 𝓡, hO, hJ, clause6_of hR 𝓡⟩

/-- **Clauses (1), (2), (3), (6) with `REG015_final` (accepted).** -/
theorem hierarchy_1236 (hκ : 0 < κ) (𝓡 : Finset ℕ) :
    Clause1 L κ 𝓡 ∧ Clause2 L κ 𝓡 ∧ Clause3 L κ hκ 𝓡 ∧ Clause6 L κ hκ 𝓡 :=
  hierarchy_1236_of (QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ) 𝓡

/-- **All six printed clauses**: REG-015 enters via `REG015_final`; clauses (4), (5) via the explicit inputs
`OrbitCompactInput`, `JointContInput` (haiku_inventory's results, in progress). -/
theorem hierarchy_all (hκ : 0 < κ) (𝓡 : Finset ℕ) (hO : OrbitCompactInput L κ 𝓡) (hJ : JointContInput L κ 𝓡) :
    HierarchyAll L κ hκ 𝓡 :=
  hierarchy_all_of (QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ) 𝓡 hO hJ

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.clause1_of
#print axioms QuantumNLS.RB7.clause2_of
#print axioms QuantumNLS.RB7.clause3_of
#print axioms QuantumNLS.RB7.clause6_of
#print axioms QuantumNLS.RB7.hierarchy_1236
#print axioms QuantumNLS.RB7.hierarchy_all
