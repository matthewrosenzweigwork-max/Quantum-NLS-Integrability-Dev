import QuantumNLS.FiniteCellEvents
import Mathlib.Data.ZMod.Basic

/-! R-D8BB052C I: actual cyclic count laws and residue averaging. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical
namespace QuantumNLS.FiniteCellResidues
open Occupation OccupationHilbert FiniteCellCoefficientLaw FiniteCellTotalVariation FiniteCellEvents
variable {N : ℕ}

/-- Fiber grouping of a summable real law; used only with actual coefficient laws below. -/
def coarse {X Y : Type*} (f : X → Y) (p : X → ℝ) (y : Y) : ℝ := ∑' x : f ⁻¹' {y}, p x.1

theorem coarse_hasSum {X Y : Type*} (f : X → Y) (p : X → ℝ) (hp : Summable p) :
    HasSum (coarse f p) (∑' x, p x) := hp.hasSum.tsum_fiberwise f

theorem coarse_nonneg {X Y : Type*} (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (y : Y) :
    0 ≤ coarse f p y := tsum_nonneg (fun x => hp x.1)

/-- Grouping arbitrary fibers contracts the complete l1 difference. -/
theorem coarse_l1_le {X Y : Type*} (f : X → Y) (p q : X → ℝ)
    (hp : Summable p) (hq : Summable q) (hd : Summable (fun x => |p x - q x|)) :
    Summable (fun y => |coarse f p y - coarse f q y|) ∧
      (∑' y, |coarse f p y - coarse f q y|) ≤ ∑' x, |p x - q x| := by
  have h := coarse_hasSum f (fun x => |p x - q x|) hd
  have hle : ∀ y, |coarse f p y - coarse f q y| ≤ coarse f (fun x => |p x - q x|) y := by
    intro y
    unfold coarse
    have he := (hp.subtype (· ∈ f ⁻¹' {y})).tsum_sub (hq.subtype (· ∈ f ⁻¹' {y}))
    dsimp only [Function.comp_def] at he
    rw [← he]
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm (f := fun x : f ⁻¹' {y} => p x.1 - q x.1)
        (hd.subtype (· ∈ f ⁻¹' {y})))
  have hs := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle h.summable
  exact ⟨hs, (hs.tsum_le_tsum hle h.summable).trans_eq h.tsum_eq⟩

/-- Equivariant grouping transports the translated law exactly. -/
theorem coarse_translate {X Y : Type*} (f : X → Y) (p : X → ℝ) (e : X ≃ X) (rho : Y ≃ Y)
    (h : ∀ x, f (e x) = rho (f x)) (y : Y) :
    coarse f (fun x => p (e x)) y = coarse f p (rho y) := by
  let d : (f ⁻¹' {y}) ≃ (f ⁻¹' {rho y}) :=
    { toFun := fun x => ⟨e x.1, by change f (e x.1) = rho y; rw [h, show f x.1 = y from x.2]⟩
      invFun := fun x => ⟨e.symm x.1, by
        change f (e.symm x.1) = y
        apply rho.injective
        rw [← h, e.apply_symm_apply]
        exact x.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1) }
  exact d.tsum_eq (fun x => p x.1)

/-- Actual pushforwards compose without discarding any full-array fiber. -/
theorem pushLaw_comp {X Y : Type*} (f : Arr N → X) (F : X → Y) (g : H N) (y : Y) :
    coarse F (pushLaw f g) y = pushLaw (F ∘ f) g y := pushLaw_event f g (F ⁻¹' {y})

def selectedDistance (I : Finset ℤ) (a b : ℤ) (g : H N) : ℝ :=
  (1 / 2 : ℝ) * ∑' k, |pushLaw (selected (N := N) I) g k -
    pushLaw (selected (N := N) I) g (selectedStep I a b k)|

theorem selectedDistance_nonneg (I : Finset ℤ) (a b : ℤ) (g : H N) :
    0 ≤ selectedDistance I a b g := mul_nonneg (by norm_num) (tsum_nonneg (fun _ => abs_nonneg _))

theorem selectedDistance_reverse (I : Finset ℤ) (a b : ℤ) (g : H N) :
    selectedDistance I b a g = selectedDistance I a b g := by
  let P := pushLaw (selected (N := N) I) g
  let e := selectedStepEquiv I a b
  have h := e.tsum_eq (fun k => |P k - P (e.symm k)|)
  change (∑' k, |P (e k) - P (e.symm (e k))|) = ∑' k, |P k - P (e.symm k)| at h
  simp only [e.symm_apply_apply, abs_sub_comm (P (e _)) (P _)] at h
  exact congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) h.symm

/-- The actual selected coordinate, reduced modulo ell. -/
def countResidue (I : Finset ℤ) (ell : ℕ) (c : ↥I) (k : ↥I → ℤ) : ZMod ell := k c

def residueLaw (I : Finset ℤ) (ell : ℕ) (c : ↥I) (g : H N) : ZMod ell → ℝ :=
  pushLaw (countResidue I ell c ∘ selected (N := N) I) g

theorem residueLaw_normalized (I : Finset ℤ) (ell : ℕ) (c : ↥I) (g : H N) (hg : ‖g‖ = 1) :
    (∀ j, 0 ≤ residueLaw I ell c g j) ∧ Summable (residueLaw I ell c g) ∧
      (∑' j, residueLaw I ell c g j) = 1 :=
  ⟨pushLaw_nonneg _ _, pushLaw_normalized _ _ hg⟩

def cycle (ell : ℕ) : ZMod ell ≃ ZMod ell where
  toFun j := j + 1
  invFun j := j - 1
  left_inv j := by simp
  right_inv j := by simp

/-- An actual receiver coordinate has one-step cyclic TV at most the actual selected TV. -/
theorem receiver_residue_tv (I : Finset ℤ) (ell : ℕ) (a b : ℤ) (hb : b ∈ I) (hab : a ≠ b)
    (g : H N)
    (hd : Summable (fun k => |pushLaw (selected (N := N) I) g k -
      pushLaw (selected (N := N) I) g (selectedStep I a b k)|)) :
    Summable (fun j => |residueLaw I ell ⟨b,hb⟩ g j - residueLaw I ell ⟨b,hb⟩ g (j + 1)|) ∧
      (1 / 2 : ℝ) * (∑' j, |residueLaw I ell ⟨b,hb⟩ g j -
        residueLaw I ell ⟨b,hb⟩ g (j + 1)|) ≤ selectedDistance I a b g := by
  let P := pushLaw (selected (N := N) I) g
  let f := countResidue I ell ⟨b,hb⟩
  let e := selectedStepEquiv I a b
  have hp := (pushLaw_hasSum (selected (N := N) I) g).summable
  have hq := hp.comp_injective e.injective
  have ht : ∀ j, coarse f (fun k => P (e k)) j = residueLaw I ell ⟨b,hb⟩ g (j + 1) := by
    intro j
    rw [coarse_translate f P e (cycle ell)]
    · exact pushLaw_comp _ _ _ _
    · intro k
      change ((selectedStep I a b k ⟨b,hb⟩ : ℤ) : ZMod ell) = (k ⟨b,hb⟩ : ZMod ell) + 1
      simp [selectedStep, hab.symm, Int.cast_add]
  have h := coarse_l1_le f P (fun k => P (e k)) hp hq hd
  have hf : ∀ j, coarse f P j = residueLaw I ell ⟨b,hb⟩ g j := fun _ => pushLaw_comp _ _ _ _
  simp_rw [hf, ht] at h
  exact ⟨h.1, mul_le_mul_of_nonneg_left h.2 (by norm_num)⟩

/-- h-step cyclic TV grows at most linearly, with no residue estimate as a premise. -/
theorem cyclic_hstep (ell : ℕ) [NeZero ell] (p : ZMod ell → ℝ) (d : ℝ)
    (hone : (1 / 2 : ℝ) * (∑ j, |p j - p (j + 1)|) ≤ d) (h : ℕ) :
    (1 / 2 : ℝ) * (∑ j, |p j - p (j + (h : ZMod ell))|) ≤ (h : ℝ) * d := by
  induction h with
  | zero => simp
  | succ h ih =>
    have ht : (∑ j, |p j - p (j + ((h + 1 : ℕ) : ZMod ell))|) ≤
        (∑ j, |p j - p (j + (h : ZMod ell))|) + (∑ j, |p j - p (j + 1)|) := by
      calc
        _ ≤ ∑ j, (|p j - p (j + (h : ZMod ell))| +
            |p (j + (h : ZMod ell)) - p ((j + (h : ZMod ell)) + 1)|) := by
          apply Finset.sum_le_sum
          intro j _
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
            abs_sub_le (p j) (p (j + (h : ZMod ell))) (p ((j + (h : ZMod ell)) + 1))
        _ = _ := by
          rw [Finset.sum_add_distrib]
          congr 1
          exact Equiv.sum_comp (Equiv.addRight (h : ZMod ell)) (fun j => |p j - p (j + 1)|)
    simp only [Nat.cast_add, Nat.cast_one] at ht ⊢
    linarith

/-- Equal-total laws control every individual residue by half their l1 distance. -/
theorem cyclic_pointwise (ell : ℕ) [NeZero ell] (p : ZMod ell → ℝ)
    (j : ZMod ell) (h : ℕ) :
    |p j - p (j + (h : ZMod ell))| ≤
      (1 / 2 : ℝ) * ∑ k, |p k - p (k + (h : ZMod ell))| := by
  have hequal : (∑' k, p k) = ∑' k, p (k + (h : ZMod ell)) :=
    ((Equiv.addRight (h : ZMod ell)).tsum_eq p).symm
  have ht := event_difference_le_tv p (fun k => p (k + (h : ZMod ell)))
    (hasSum_fintype _).summable (hasSum_fintype _).summable hequal (hasSum_fintype _).summable ({j} : Set (ZMod ell))
  simpa [tsum_subtype, tsum_fintype] using ht

theorem sum_steps (ell : ℕ) : (∑ h : Fin ell, (h.1 : ℝ)) = (ell : ℝ) * ((ell : ℝ) - 1) / 2 := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, Fin.val_succ, Nat.cast_add, Nat.cast_one,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ih]
    ring

open Fin.NatCast in
theorem finEquiv_natCast (ell : ℕ) [NeZero ell] (h : Fin ell) :
    ZMod.finEquiv ell h = (h.1 : ZMod ell) := by
  cases ell with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ ell =>
    apply Fin.ext
    change h.1 = ((h.1 : Fin (ell + 1)).1)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt h.2]

/-- Averaging all translates gives the printed constant for EVERY residue. -/
theorem cyclic_residue_bound (ell : ℕ) [NeZero ell] (p : ZMod ell → ℝ)
    (hptotal : ∑ j, p j = 1) (d : ℝ)
    (hone : (1 / 2 : ℝ) * (∑ j, |p j - p (j + 1)|) ≤ d) (j : ZMod ell) :
    p j ≤ 1 / (ell : ℝ) + ((ell : ℝ) - 1) * d / 2 := by
  have hsteps : ∀ h : Fin ell, p j ≤ p (j + (h.1 : ZMod ell)) + (h.1 : ℝ) * d := by
    intro h
    have hpoint := cyclic_pointwise ell p j h.1
    have hstep := cyclic_hstep ell p d hone h.1
    linarith [le_abs_self (p j - p (j + (h.1 : ZMod ell)))]
  have havg := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin ell))) => hsteps h)
  have hsum : (∑ h : Fin ell, p (j + (h.1 : ZMod ell))) = 1 := by
    simp_rw [← finEquiv_natCast ell]
    calc
      _ = ∑ h : Fin ell, p (j + (ZMod.finEquiv ell).toEquiv h) := rfl
      _ = ∑ h : ZMod ell, p (j + h) := Equiv.sum_comp (ZMod.finEquiv ell).toEquiv (fun h : ZMod ell => p (j + h))
      _ = ∑ h : ZMod ell, p h := Equiv.sum_comp (Equiv.addLeft j) p
      _ = 1 := hptotal
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib, hsum, ← Finset.sum_mul, sum_steps] at havg
  have he : (0 : ℝ) < ell := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne ell))
  calc
    p j ≤ (1 + ((ell : ℝ) * ((ell : ℝ) - 1) / 2) * d) / ell :=
      (le_div_iff₀ he).mpr (by nlinarith [havg])
    _ = (1 / (ell : ℝ) + ((ell : ℝ) - 1) * d / 2) := by field_simp

/-- The residue law is exactly the actual full-array count event. -/
theorem residueLaw_eq_mass (I : Finset ℤ) (ell : ℕ) (c : ↥I) (g : H N) (j : ZMod ell) :
    residueLaw I ell c g j = mass g {m : Arr N | (m.1 c.1 : ZMod ell) = j} := by
  have hf : countResidue I ell c ∘ selected (N := N) I =
      fun m : Arr N => (m.1 c.1 : ZMod ell) := by
    funext m
    change ((m.1 c.1 : ℤ) : ZMod ell) = (m.1 c.1 : ZMod ell)
    exact Int.cast_natCast _
  unfold residueLaw
  rw [hf]
  rfl

/-- All actual selected differences are summable, without a residual assumption. -/
theorem selected_difference_summable (I : Finset ℤ) (a b : ℤ) (g : H N) :
    Summable (fun k => |pushLaw (selected (N := N) I) g k -
      pushLaw (selected (N := N) I) g (selectedStep I a b k)|) := by
  have hp := (pushLaw_hasSum (selected (N := N) I) g).summable
  have hq := hp.comp_injective (selectedStepEquiv I a b).injective
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ (hp.add hq)
  intro k
  change |pushLaw (selected (N := N) I) g k - pushLaw (selected (N := N) I) g (selectedStep I a b k)| ≤
    pushLaw (selected (N := N) I) g k + pushLaw (selected (N := N) I) g (selectedStep I a b k)
  have h1 := pushLaw_nonneg (selected (N := N) I) g k
  have h2 := pushLaw_nonneg (selected (N := N) I) g (selectedStep I a b k)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Actual receiver h-step TV, derived by contraction and cyclic telescoping. -/
theorem receiver_hstep (I : Finset ℤ) (ell : ℕ) [NeZero ell]
    (a b : ℤ) (hb : b ∈ I) (hab : a ≠ b) (g : H N) (h : ℕ) :
    (1 / 2 : ℝ) * (∑' j, |residueLaw I ell ⟨b,hb⟩ g j -
      residueLaw I ell ⟨b,hb⟩ g (j + (h : ZMod ell))|) ≤
      (h : ℝ) * selectedDistance I a b g := by
  have hone := (receiver_residue_tv I ell a b hb hab g (selected_difference_summable I a b g)).2
  simp only [tsum_fintype] at hone ⊢
  exact cyclic_hstep ell _ _ hone h

/-- Actual donor h-step TV has exactly the same selected distance. -/
theorem donor_hstep (I : Finset ℤ) (ell : ℕ) [NeZero ell]
    (a b : ℤ) (ha : a ∈ I) (hab : a ≠ b) (g : H N) (h : ℕ) :
    (1 / 2 : ℝ) * (∑' j, |residueLaw I ell ⟨a,ha⟩ g j -
      residueLaw I ell ⟨a,ha⟩ g (j + (h : ZMod ell))|) ≤
      (h : ℝ) * selectedDistance I a b g := by
  have ht := receiver_hstep I ell b a ha hab.symm g h
  rwa [selectedDistance_reverse] at ht

/-- Every prescribed receiver residue has the printed actual mass bound. -/
theorem receiver_residue_bound (I : Finset ℤ) (ell : ℕ) [NeZero ell]
    (a b : ℤ) (hb : b ∈ I) (hab : a ≠ b) (g : H N) (hg : ‖g‖ = 1) (j : ZMod ell) :
    mass g {m : Arr N | (m.1 b : ZMod ell) = j} ≤
      1 / (ell : ℝ) + ((ell : ℝ) - 1) * selectedDistance I a b g / 2 := by
  rw [← residueLaw_eq_mass I ell ⟨b,hb⟩]
  have hn := (residueLaw_normalized I ell ⟨b,hb⟩ g hg).2.2
  have ht := (receiver_residue_tv I ell a b hb hab g (selected_difference_summable I a b g)).2
  simp only [tsum_fintype] at hn ht
  exact cyclic_residue_bound ell _ hn _ ht j

/-- Every prescribed donor residue has the same printed actual mass bound. -/
theorem donor_residue_bound (I : Finset ℤ) (ell : ℕ) [NeZero ell]
    (a b : ℤ) (ha : a ∈ I) (hab : a ≠ b) (g : H N) (hg : ‖g‖ = 1) (j : ZMod ell) :
    mass g {m : Arr N | (m.1 a : ZMod ell) = j} ≤
      1 / (ell : ℝ) + ((ell : ℝ) - 1) * selectedDistance I a b g / 2 := by
  have ht := receiver_residue_bound I ell b a ha hab.symm g hg j
  rwa [selectedDistance_reverse] at ht

theorem mass_union (g : H N) (A B : Set (Arr N)) : mass g (A ∪ B) ≤ mass g A + mass g B := by
  let F : Bool → Set (Arr N) := fun b => if b then B else A
  have he : {m : Arr N | ∃ b ∈ (Finset.univ : Finset Bool), m ∈ F b} = A ∪ B := by
    ext m
    simp [F]
  have h := mass_finite_union (Finset.univ : Finset Bool) F g
  rw [he] at h
  simpa [F, Fintype.sum_bool, add_comm] using h

/-- The exact source residue union estimate, retaining every exterior array. -/
theorem residue_union_bound (I : Finset ℤ) (ell : ℕ) [NeZero ell]
    (a b : ℤ) (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) (g : H N) (hg : ‖g‖ = 1) :
    mass g {m : Arr N | (m.1 a : ZMod ell) = 0 ∨ (m.1 b : ZMod ell) = -1} ≤
      2 / (ell : ℝ) + (ell : ℝ) * selectedDistance I a b g := by
  have hu := mass_union g {m : Arr N | (m.1 a : ZMod ell) = 0}
    {m : Arr N | (m.1 b : ZMod ell) = -1}
  have ha' := donor_residue_bound I ell a b ha hab g hg 0
  have hb' := receiver_residue_bound I ell a b hb hab g hg (-1)
  have hd := selectedDistance_nonneg I a b g
  change mass g {m : Arr N | (m.1 a : ZMod ell) = 0 ∨ (m.1 b : ZMod ell) = -1} ≤ _ at hu
  calc
    _ ≤ mass g {m : Arr N | (m.1 a : ZMod ell) = 0} +
      mass g {m : Arr N | (m.1 b : ZMod ell) = -1} := hu
    _ ≤ 2 / (ell : ℝ) + (ell : ℝ) * selectedDistance I a b g := by
      simp only [div_eq_mul_inv, one_mul] at ha' hb' ⊢
      linarith

/-- I's actual-law bound specializes directly to the printed completed-operator residual sum. -/
theorem residue_union_from_residual_sum (I G : Finset ℤ) (ell : ℕ) [NeZero ell]
    (c : FiniteCellSupport.OrderedSeeds N) (t : ℤ → FullOccupationAffinity.Phase)
    (g : H N) (hg : ‖g‖ = 1) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : FiniteCellEstimate.Pairs G, ‖FiniteCellEstimate.pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ℤ) (haI : a ∈ I) (hbI : b ∈ I) (haG : a ∈ G) (hbG : b ∈ G) (hab : a ≠ b) :
    mass g {m : Arr N | (m.1 a : ZMod ell) = 0 ∨ (m.1 b : ZMod ell) = -1} ≤
      2 / (ell : ℝ) + (ell : ℝ) * Real.sqrt (2 * eta) := by
  have hd := (selected_tv_from_residual_sum I G c t g hg eta heta hres a b haG hbG hab).2
  exact (residue_union_bound I ell a b haI hbI hab g hg).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg ell)))

end QuantumNLS.FiniteCellResidues

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellResidues.coarse
#print axioms QuantumNLS.FiniteCellResidues.coarse_hasSum
#print axioms QuantumNLS.FiniteCellResidues.coarse_nonneg
#print axioms QuantumNLS.FiniteCellResidues.coarse_l1_le
#print axioms QuantumNLS.FiniteCellResidues.coarse_translate
#print axioms QuantumNLS.FiniteCellResidues.pushLaw_comp
#print axioms QuantumNLS.FiniteCellResidues.selectedDistance
#print axioms QuantumNLS.FiniteCellResidues.selectedDistance_nonneg
#print axioms QuantumNLS.FiniteCellResidues.selectedDistance_reverse
#print axioms QuantumNLS.FiniteCellResidues.countResidue
#print axioms QuantumNLS.FiniteCellResidues.residueLaw
#print axioms QuantumNLS.FiniteCellResidues.residueLaw_normalized
#print axioms QuantumNLS.FiniteCellResidues.cycle
#print axioms QuantumNLS.FiniteCellResidues.receiver_residue_tv
#print axioms QuantumNLS.FiniteCellResidues.cyclic_hstep
#print axioms QuantumNLS.FiniteCellResidues.cyclic_pointwise
#print axioms QuantumNLS.FiniteCellResidues.sum_steps
#print axioms QuantumNLS.FiniteCellResidues.finEquiv_natCast
#print axioms QuantumNLS.FiniteCellResidues.cyclic_residue_bound
#print axioms QuantumNLS.FiniteCellResidues.residueLaw_eq_mass
#print axioms QuantumNLS.FiniteCellResidues.selected_difference_summable
#print axioms QuantumNLS.FiniteCellResidues.receiver_hstep
#print axioms QuantumNLS.FiniteCellResidues.donor_hstep
#print axioms QuantumNLS.FiniteCellResidues.receiver_residue_bound
#print axioms QuantumNLS.FiniteCellResidues.donor_residue_bound
#print axioms QuantumNLS.FiniteCellResidues.mass_union
#print axioms QuantumNLS.FiniteCellResidues.residue_union_bound
#print axioms QuantumNLS.FiniteCellResidues.residue_union_from_residual_sum

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellResidues.coarse,
    ``QuantumNLS.FiniteCellResidues.coarse_hasSum,
    ``QuantumNLS.FiniteCellResidues.coarse_nonneg,
    ``QuantumNLS.FiniteCellResidues.coarse_l1_le,
    ``QuantumNLS.FiniteCellResidues.coarse_translate,
    ``QuantumNLS.FiniteCellResidues.pushLaw_comp,
    ``QuantumNLS.FiniteCellResidues.selectedDistance,
    ``QuantumNLS.FiniteCellResidues.selectedDistance_nonneg,
    ``QuantumNLS.FiniteCellResidues.selectedDistance_reverse,
    ``QuantumNLS.FiniteCellResidues.countResidue,
    ``QuantumNLS.FiniteCellResidues.residueLaw,
    ``QuantumNLS.FiniteCellResidues.residueLaw_normalized,
    ``QuantumNLS.FiniteCellResidues.cycle,
    ``QuantumNLS.FiniteCellResidues.receiver_residue_tv,
    ``QuantumNLS.FiniteCellResidues.cyclic_hstep,
    ``QuantumNLS.FiniteCellResidues.cyclic_pointwise,
    ``QuantumNLS.FiniteCellResidues.sum_steps,
    ``QuantumNLS.FiniteCellResidues.finEquiv_natCast,
    ``QuantumNLS.FiniteCellResidues.cyclic_residue_bound,
    ``QuantumNLS.FiniteCellResidues.residueLaw_eq_mass,
    ``QuantumNLS.FiniteCellResidues.selected_difference_summable,
    ``QuantumNLS.FiniteCellResidues.receiver_hstep,
    ``QuantumNLS.FiniteCellResidues.donor_hstep,
    ``QuantumNLS.FiniteCellResidues.receiver_residue_bound,
    ``QuantumNLS.FiniteCellResidues.donor_residue_bound,
    ``QuantumNLS.FiniteCellResidues.mass_union,
    ``QuantumNLS.FiniteCellResidues.residue_union_bound,
    ``QuantumNLS.FiniteCellResidues.residue_union_from_residual_sum]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Abstract finite-cell proof reached EXT-001: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"FiniteCellResidues aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
