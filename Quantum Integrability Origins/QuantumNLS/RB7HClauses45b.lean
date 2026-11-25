import Mathlib
import QuantumNLS.RB7HSmooth2
import QuantumNLS.RB7FinalAll
import QuantumNLS.Reg015HFinal

/-!
# R-7B122087 `thm:hierarchy`, clauses 4-5: bridges to the frozen interface (RB7HClauses45b, haiku_inventory)

Proves the two frozen Props of `RB7FinalAll` for EVERY family `F : HamFlows L κ 𝓡` (not only `chartHamFlows`):

* `orbitCompactInput_of hκ 𝓡 : OrbitCompactInput L κ 𝓡`  (clause 4: full orbits relatively compact in `∏_k H^k`, the closure
  taken in the product topology as in the frozen statement; the smooth subspace is handled by `jetOf_smAll`);
* `jointContInput_of hκ 𝓡 : JointContInput L κ 𝓡`  (clause 5: joint flow continuous on `(ℕ → ℝ) × SmoothProf L`, hence on every `B ×ˢ K`).

Routes:
* clause 4: for smooth `u` and joint time `t`, the joint flow is smooth (`joint_smooth_of_family`) and its chart coordinates are the
  coordinates of `u` multiplied by ONE unimodular sequence `V t` (`joint_rotation_form`, valid for every `F`).  Hence every orbit point is
  `gN k (rot V (wN k u))` in every level `k`; the set of such points over all `V : ℤ → Circle` is the continuous image of the modulus torus
  (`isCompact_smoothTorus`), compact, and contains the orbit.  A compact set contains the closure of the orbit.
* clause 5: each `F` agrees with `chartHamFlows` on smooth data (uniqueness, `unique_chart`), so the joint flow equals `compSm` (the
  continuous finite composition of `RB7HSmooth2`); `smAll ∘ compSm` is continuous, and `jetOf` coincides with it.

REG-015 enters only through `Reg015HFinal.REG015_final` (accepted); no sorry, no new axiom.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
noncomputable section

open scoped ComplexConjugate Topology NNReal ContDiff
open Set Filter

namespace QuantumNLS.RB7HBridge

open QuantumNLS.RB7 QuantumNLS.RB7HSm2 QuantumNLS.Sobolev QuantumNLS.HierarchyFlow
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.PhysicalTensor

variable {L κ : ℝ} [Fact (0 < L)]

/-! ## Jets and smooth profiles -/

/-- The jet of a smooth profile is the `H^k`-class of the smooth datum (the `smAll` embedding). -/
theorem jetOf_smAll (Y : SmData L) (k : ℕ) : jetOf (L := L) Y.fn k = smAll Y k := by
  unfold jetOf
  exact dif_pos Y.smooth

/-- Smooth data attached to a smooth profile. -/
def mkSm (f : SmoothProf L) : SmData L := ⟨f.val, f.smooth⟩

theorem jetOf_smAll_prof (f : SmoothProf L) (k : ℕ) : jetOf (L := L) f.val k = smAll (mkSm f) k :=
  jetOf_smAll (mkSm f) k

theorem continuous_mkSm : Continuous (mkSm (L := L)) := by
  refine continuous_induced_rng.2 ?_
  have h1 : Continuous (fun f : SmoothProf L => (jetOf (L := L) f.val : ∀ k : ℕ, H02 L (k : ℝ))) :=
    continuous_induced_dom
  exact h1.congr fun f => funext fun k => jetOf_smAll_prof f k

/-! ## Agreement of an arbitrary family with the chart family on smooth data -/

/-- On smooth data, the composition of the flows of any family `F` equals the composition of the chart flows. -/
theorem foldr_agree {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) :
    ∀ (l : List ℕ), (∀ r ∈ l, r ∈ 𝓡) → ∀ u : ℝ → ℂ, SmoothPeriodic L u →
      ((l.map fun r => F.Φ r (t r)).foldr (· ∘ ·) id) u =
        ((l.map fun r => chartFlow hR C r (t r)).foldr (· ∘ ·) id) u := by
  intro l
  induction l with
  | nil => intro _ u _; rfl
  | cons r l ih =>
    intro hl u hu
    have hr : r ∈ 𝓡 := hl r (by simp)
    have hl' : ∀ r' ∈ l, r' ∈ 𝓡 := fun r' hr' => hl r' (by simp [hr'])
    simp only [List.map_cons, List.foldr_cons, Function.comp_apply]
    rw [ih hl' u hu]
    exact unique_chart hR C r (F.Φ r) (F.ham r hr) _ (smooth_foldr hR C t l hu) (t r)

/-- The joint flow of any family agrees with the chart joint flow on smooth data. -/
theorem joint_agree {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {𝓡 : Finset ℕ}
    (F : HamFlows L κ 𝓡) (t : ℕ → ℝ) (v : ℝ → ℂ) (hv : SmoothPeriodic L v) :
    jointClassicalFlow F t v = jointClassicalFlow (chartHamFlows hR C 𝓡) t v := by
  unfold jointClassicalFlow
  exact foldr_agree hR C F t (𝓡.sort (· ≤ ·)) (fun r hr => (Finset.mem_sort (· ≤ ·)).1 hr) v hv

/-! ## Clause (4): relative compactness of the full orbits -/

/-- Full joint orbits of smooth data have compact closure in `∏_k H^k` (the frozen `OrbitCompactInput` for one `F, u`). -/
theorem orbit_joint {hκ : 0 < κ} (𝓡 : Finset ℕ) (F : HamFlows L κ 𝓡) (u : SmoothProf L) :
    IsCompact (closure (Set.range fun t : ℕ → ℝ =>
      (jetOf (L := L) (jointClassicalFlow F t u.val) : ∀ k : ℕ, H02 L (k : ℝ)))) := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  have hR : REG015Concl (L := L) hκ := QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ
  let x : SmData L := ⟨u.val, u.smooth⟩
  let M : Set (∀ k : ℕ, H02 L (k : ℝ)) :=
    (fun y : (∀ k : ℕ, h02 L (k : ℝ)) => fun k : ℕ => gN hR C k (y k)) ''
      (Set.range fun V : ℤ → Circle => fun k : ℕ => rot V (wN hR C k x))
  have hG : Continuous (fun y : (∀ k : ℕ, h02 L (k : ℝ)) => fun k : ℕ => gN hR C k (y k)) :=
    continuous_pi fun k => (gN_cont hR C k).comp (continuous_apply k)
  have hT : IsCompact (Set.range fun V : ℤ → Circle => fun k : ℕ => rot V (wN hR C k x)) :=
    isCompact_smoothTorus L (fun k : ℕ => wN hR C k x)
  have hM : IsCompact M := hT.image hG
  have hsub : Set.range (fun t : ℕ → ℝ =>
      (jetOf (L := L) (jointClassicalFlow F t u.val) : ∀ k : ℕ, H02 L (k : ℝ))) ⊆ M := by
    rintro _ ⟨t, rfl⟩
    have hj : SmoothPeriodic L (jointClassicalFlow F t u.val) :=
      joint_smooth_of_family hR C F t u.smooth
    have hV : ∀ n : ℤ, ∃ c : Circle, (C.Φ (smoothL2 hj) : ℤ → ℂ) n =
        (c : ℂ) * (C.Φ (smoothL2 u.smooth) : ℤ → ℂ) n := by
      intro n
      exact ⟨Circle.exp (-(∑ r ∈ 𝓡, t r * FreqSeq ((SOf r : ℝ≥0) : ℝ) (Fd hR C r)
          (fun m => C.Φ (smoothL2 u.smooth) m) n)),
        by rw [joint_rotation_form hR C F t u.smooth hj n, Circle.coe_exp]⟩
    choose V hV using hV
    refine ⟨fun k : ℕ => rot V (wN hR C k x), ⟨V, rfl⟩, ?_⟩
    funext k
    show gN hR C k (rot V (wN hR C k x)) =
      (jetOf (L := L) (jointClassicalFlow F t u.val) : ∀ k : ℕ, H02 L (k : ℝ)) k
    have hjk : (jetOf (L := L) (jointClassicalFlow F t u.val) : ∀ k : ℕ, H02 L (k : ℝ)) k =
        smAll ⟨jointClassicalFlow F t u.val, hj⟩ k :=
      jetOf_smAll ⟨jointClassicalFlow F t u.val, hj⟩ k
    rw [hjk]
    exact gN_eq_smAll hR C k ⟨jointClassicalFlow F t u.val, hj⟩ (rot V (wN hR C k x))
      (fun n => by rw [rot_val, wN_apply]; exact (hV n).symm)
  exact IsCompact.of_isClosed_subset hM isClosed_closure (closure_minimal hsub hM.isClosed)

/-- **Clause (4) for every family.** The frozen `OrbitCompactInput L κ 𝓡`. -/
theorem orbitCompactInput_of (hκ : 0 < κ) (𝓡 : Finset ℕ) : OrbitCompactInput L κ 𝓡 :=
  fun F u => orbit_joint (hκ := hκ) 𝓡 F u

/-! ## Clause (5): continuous dependence on initial data and joint times -/

/-- The joint flow of any family, as a function of joint time and smooth initial class, is continuous into `∏_k H^k`. -/
theorem jointCont_all {hκ : 0 < κ} (𝓡 : Finset ℕ) (F : HamFlows L κ 𝓡) :
    Continuous (fun p : (ℕ → ℝ) × SmoothProf L =>
      (jetOf (L := L) (jointClassicalFlow F p.1 p.2.val) : ∀ k : ℕ, H02 L (k : ℝ))) := by
  obtain ⟨C⟩ := chartFacts_exists (L := L) hκ
  have hR : REG015Concl (L := L) hκ := QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ
  have hmk : Continuous (fun p : (ℕ → ℝ) × SmoothProf L => ((p.1, mkSm p.2) : (ℕ → ℝ) × SmData L)) :=
    Continuous.prodMk continuous_fst (continuous_mkSm.comp continuous_snd)
  have hcomp : Continuous (fun p : (ℕ → ℝ) × SmoothProf L =>
      smAll (compSm hR C (𝓡.sort (· ≤ ·)) (p.1, mkSm p.2))) :=
    continuous_smAll_dom.comp ((compSm_cont hR C (𝓡.sort (· ≤ ·))).comp hmk)
  have hfun : (fun p : (ℕ → ℝ) × SmoothProf L =>
      (jetOf (L := L) (jointClassicalFlow F p.1 p.2.val) : ∀ k : ℕ, H02 L (k : ℝ))) =
      fun p => smAll (compSm hR C (𝓡.sort (· ≤ ·)) (p.1, mkSm p.2)) := by
    funext p
    have hagree : jointClassicalFlow F p.1 p.2.val =
        jointClassicalFlow (chartHamFlows hR C 𝓡) p.1 p.2.val :=
      joint_agree hR C F p.1 p.2.val p.2.smooth
    have hY : (compSm hR C (𝓡.sort (· ≤ ·)) (p.1, mkSm p.2)).fn =
        jointClassicalFlow (chartHamFlows hR C 𝓡) p.1 p.2.val :=
      compSm_fn hR C (𝓡.sort (· ≤ ·)) (p.1, mkSm p.2)
    funext k
    rw [hagree, ← hY, jetOf_smAll]
  rw [hfun]
  exact hcomp

/-- **Clause (5) for every family.** The frozen `JointContInput L κ 𝓡`. -/
theorem jointContInput_of (hκ : 0 < κ) (𝓡 : Finset ℕ) : JointContInput L κ 𝓡 := by
  intro F K B _ _
  exact (jointCont_all (hκ := hκ) 𝓡 F).continuousOn

/-! ## All six clauses -/

/-- **All six printed clauses of `thm:hierarchy`**: `RB7FinalAll.hierarchy_all` with the two bridges above.
REG-015 enters only through `Reg015HFinal.REG015_final` (accepted). -/
theorem hierarchy_all_unconditional (hκ : 0 < κ) (𝓡 : Finset ℕ) : HierarchyAll L κ hκ 𝓡 :=
  QuantumNLS.RB7.hierarchy_all hκ 𝓡 (orbitCompactInput_of hκ 𝓡) (jointContInput_of hκ 𝓡)

end QuantumNLS.RB7HBridge

#print axioms QuantumNLS.RB7HBridge.jetOf_smAll
#print axioms QuantumNLS.RB7HBridge.continuous_mkSm
#print axioms QuantumNLS.RB7HBridge.foldr_agree
#print axioms QuantumNLS.RB7HBridge.joint_agree
#print axioms QuantumNLS.RB7HBridge.orbit_joint
#print axioms QuantumNLS.RB7HBridge.orbitCompactInput_of
#print axioms QuantumNLS.RB7HBridge.jointCont_all
#print axioms QuantumNLS.RB7HBridge.jointContInput_of
#print axioms QuantumNLS.RB7HBridge.hierarchy_all_unconditional
