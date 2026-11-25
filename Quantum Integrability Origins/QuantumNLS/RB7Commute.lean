import Mathlib
import QuantumNLS.RB7Rotation

/-!
# R-7B122087 `thm:hierarchy`, clause (2): every finite family of the flows commutes (RB7Commute)

Printed: "Every finite family of these flows commutes" with the proof "finite families commute because their coordinate rotations do".

`compFlow l` is the composition of chart flows along a list `l` of (order, time) pairs.  `comp_coords` (induction on `l`): for smooth `u` the composition is smooth and its chart coordinates are
`Φ_n = exp(-i Σ_{(r,s)∈l} s ω_{r,n}(Φ u)) Φ_n(u)`, because (i) one flow acts on the coordinates by `RB7Rotation.coords_chartFlow` and (ii) every frequency `ω_{r',n}` is invariant under coordinatewise
rotations (`RB7Rotation.omegaOf_congr`, i.e. constant actions).  The sum of the angles is symmetric, so `compFlow_perm`: the composition does not depend on the order of the list.
Consequences for an ARBITRARY family `F : HamFlows L κ 𝓡` of smooth Hamiltonian flows (these are the chart flows on smooth data by uniqueness):

* `comm_pair`: `F.Φ r s (F.Φ r' s' u) = F.Φ r' s' (F.Φ r s u)`, all `r, r' ∈ 𝓡` (all orders, no restriction to orders `0, 1`), all real `s, s'`, smooth `u`;
* `foldr_perm`: the composition over any permutation of `𝓡` equals `jointClassicalFlow F t`;
* `joint_rotation_form`: `Φ_n(jointClassicalFlow F t u) = exp(-i Σ_{r∈𝓡} t_r ω_{r,n}(Φ u)) Φ_n(u)`.
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
open QuantumNLS.HierarchyFlow QuantumNLS.LossSobolev

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

/-- The composition of chart flows along a list of (order, time) pairs. -/
def compFlow (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (l : List (ℕ × ℝ)) :
    (ℝ → ℂ) → (ℝ → ℂ) :=
  (l.map fun p => chartFlow hR C p.1 p.2).foldr (· ∘ ·) id

/-- Two smooth profiles with the same chart coordinates are equal. -/
theorem eq_of_coords (C : ChartFacts (L := L) hκ) {f g : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (hg : SmoothPeriodic L g) (h : ∀ n, (C.Φ (smoothL2 hf) : ℤ → ℂ) n = (C.Φ (smoothL2 hg) : ℤ → ℂ) n) : f = g := by
  apply RB7H.eq_of_smoothL2_eq hf hg
  have h1 : C.Φ (smoothL2 hf) = C.Φ (smoothL2 hg) := lp.ext (funext h)
  have := congrArg C.Ψ h1
  rwa [C.ΨΦ, C.ΨΦ] at this

theorem comp_coords (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (l : List (ℕ × ℝ))
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    ∃ hf : SmoothPeriodic L (compFlow hR C l u), ∀ n : ℤ, (C.Φ (smoothL2 hf) : ℤ → ℂ) n =
      Complex.exp (((-((l.map fun p => p.2 * omegaOf hR C p.1 hu n).sum) : ℝ) : ℂ) * Complex.I) *
        (C.Φ (smoothL2 hu) : ℤ → ℂ) n := by
  induction l with
  | nil =>
    refine ⟨hu, fun n => ?_⟩
    simp only [List.map_nil, List.sum_nil, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    rfl
  | cons p l ih =>
    obtain ⟨hv, hvc⟩ := ih
    have hf : SmoothPeriodic L (chartFlow hR C p.1 p.2 (compFlow hR C l u)) :=
      ((isHamFlow_chart hR C p.1 _ hv).2.2 p.2).1
    refine ⟨hf, fun n => ?_⟩
    have hω : ∀ m, omegaOf hR C p.1 hv m = omegaOf hR C p.1 hu m :=
      omegaOf_congr hR C p.1 hu hv (fun m => Circle.exp (-((l.map fun p => p.2 * omegaOf hR C p.1 hu m).sum)))
        (fun m => by rw [hvc m, circle_exp_coe])
    refine (coords_chartFlow hR C p.1 hv p.2 hf n).trans ?_
    rw [hω n, hvc n, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [List.map_cons, List.sum_cons]
    push_cast
    ring

theorem compFlow_perm (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {l l' : List (ℕ × ℝ)}
    (h : l.Perm l') {u : ℝ → ℂ} (hu : SmoothPeriodic L u) : compFlow hR C l u = compFlow hR C l' u := by
  obtain ⟨hf, hc⟩ := comp_coords hR C l hu
  obtain ⟨hf', hc'⟩ := comp_coords hR C l' hu
  refine eq_of_coords C hf hf' fun n => ?_
  rw [hc n, hc' n, (h.map fun p => p.2 * omegaOf hR C p.1 hu n).sum_eq]

theorem compFlow_cons (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (p : ℕ × ℝ) (l : List (ℕ × ℝ))
    (u : ℝ → ℂ) : compFlow hR C (p :: l) u = chartFlow hR C p.1 p.2 (compFlow hR C l u) := rfl

/-- Any two chart flows commute on smooth data (all orders, all times). -/
theorem comm_chart_pair (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r r' : ℕ) (s s' : ℝ)
    {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    chartFlow hR C r s (chartFlow hR C r' s' u) = chartFlow hR C r' s' (chartFlow hR C r s u) := by
  have := compFlow_perm hR C (l := [(r, s), (r', s')]) (l' := [(r', s'), (r, s)]) (List.Perm.swap _ _ [])
    hu
  exact this

/-- A member of an arbitrary family of Hamiltonian flows is the chart flow on smooth data. -/
theorem family_eq (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) {r : ℕ} (hr : r ∈ 𝓡) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (s : ℝ) :
    F.Φ r s u = chartFlow hR C r s u :=
  isHamFlow_eq hR C r (F.ham r hr) hu s

theorem foldr_eq_comp (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (l : List ℕ) (hl : ∀ r ∈ l, r ∈ 𝓡) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) :
    ((l.map fun r => F.Φ r (t r)).foldr (· ∘ ·) id) u = compFlow hR C (l.map fun r => (r, t r)) u := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    have hl' : ∀ r ∈ l, r ∈ 𝓡 := fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')
    have hv := (comp_coords hR C (l.map fun r => (r, t r)) hu).1
    simp only [List.map_cons, List.foldr_cons, Function.comp_apply]
    rw [ih hl', family_eq hR C F (hl r List.mem_cons_self) hv]
    rfl

theorem comm_pair (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) {r r' : ℕ} (hr : r ∈ 𝓡) (hr' : r' ∈ 𝓡) {u : ℝ → ℂ} (hu : SmoothPeriodic L u)
    (s s' : ℝ) : F.Φ r s (F.Φ r' s' u) = F.Φ r' s' (F.Φ r s u) := by
  have h1 : SmoothPeriodic L (chartFlow hR C r' s' u) := ((isHamFlow_chart hR C r' u hu).2.2 s').1
  have h2 : SmoothPeriodic L (chartFlow hR C r s u) := ((isHamFlow_chart hR C r u hu).2.2 s).1
  rw [family_eq hR C F hr' hu, family_eq hR C F hr h1, family_eq hR C F hr hu, family_eq hR C F hr' h2]
  exact comm_chart_pair hR C r r' s s' hu

theorem foldr_perm (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) {l : List ℕ} (hl : l.Perm (𝓡.sort (· ≤ ·))) {u : ℝ → ℂ}
    (hu : SmoothPeriodic L u) :
    ((l.map fun r => F.Φ r (t r)).foldr (· ∘ ·) id) u = jointClassicalFlow F t u := by
  have hmem : ∀ r ∈ l, r ∈ 𝓡 := fun r hr => (Finset.mem_sort (· ≤ ·)).1 (hl.subset hr)
  have hmem' : ∀ r ∈ 𝓡.sort (· ≤ ·), r ∈ 𝓡 := fun r hr => (Finset.mem_sort (· ≤ ·)).1 hr
  unfold jointClassicalFlow
  rw [foldr_eq_comp hR C F t l hmem hu, foldr_eq_comp hR C F t _ hmem' hu]
  exact compFlow_perm hR C (hl.map _) hu

theorem joint_rotation_form (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u)
    (hj : SmoothPeriodic L (jointClassicalFlow F t u)) (n : ℤ) :
    (C.Φ (smoothL2 hj) : ℤ → ℂ) n =
      Complex.exp (((-(∑ r ∈ 𝓡, t r * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fd hR C r)
        (fun m => C.Φ (smoothL2 hu) m) n) : ℝ) : ℂ) * Complex.I) * (C.Φ (smoothL2 hu) : ℤ → ℂ) n := by
  have hmem' : ∀ r ∈ 𝓡.sort (· ≤ ·), r ∈ 𝓡 := fun r hr => (Finset.mem_sort (· ≤ ·)).1 hr
  have he : jointClassicalFlow F t u = compFlow hR C ((𝓡.sort (· ≤ ·)).map fun r => (r, t r)) u := by
    unfold jointClassicalFlow
    exact foldr_eq_comp hR C F t _ hmem' hu
  obtain ⟨hf, hc⟩ := comp_coords hR C ((𝓡.sort (· ≤ ·)).map fun r => (r, t r)) hu
  have h3 : smoothL2 hj = smoothL2 hf := smoothL2_congr he hj hf
  rw [h3, hc n]
  congr 3
  have hs : (((𝓡.sort (· ≤ ·)).map fun r => (r, t r)).map fun p => p.2 * omegaOf hR C p.1 hu n).sum =
      ∑ r ∈ 𝓡, t r * omegaOf hR C r hu n := by
    rw [List.map_map]
    have := ((Finset.sort_perm_toList 𝓡 (· ≤ ·)).map (fun r => t r * omegaOf hR C r hu n)).sum_eq
    refine this.trans ?_
    exact Finset.sum_map_toList 𝓡 _
  rw [hs]
  have hs2 : ∑ r ∈ 𝓡, t r * omegaOf hR C r hu n =
      ∑ r ∈ 𝓡, t r * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fd hR C r) (fun m => C.Φ (smoothL2 hu) m) n :=
    Finset.sum_congr rfl fun r _ => by rw [omegaOf_eq_FreqSeq]
  rw [hs2]

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.comp_coords
#print axioms QuantumNLS.RB7.compFlow_perm
#print axioms QuantumNLS.RB7.comm_chart_pair
#print axioms QuantumNLS.RB7.comm_pair
#print axioms QuantumNLS.RB7.foldr_perm
#print axioms QuantumNLS.RB7.joint_rotation_form
