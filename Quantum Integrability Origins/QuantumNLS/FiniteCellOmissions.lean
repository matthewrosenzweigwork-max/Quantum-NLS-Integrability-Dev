import QuantumNLS.FiniteCellResidues
import QuantumNLS.FiniteCellInternal

/-! R-D8BB052C J: the actual excluded event and complete-array omitted edges. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical ComplexConjugate
namespace QuantumNLS.FiniteCellOmissions
open Occupation OccupationHilbert FullOccupationAffinity FiniteCellSupport FiniteCellPartition
  FiniteCellGauge FiniteCellTransport FiniteCellEstimate FiniteCellInternal
  FiniteCellCoefficientLaw FiniteCellTotalVariation FiniteCellEvents FiniteCellResidues
variable {N : ℕ}

/-- All omitted-source conditions depend only on selected integer counts. -/
def excludedSelected (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) : Set (↥I → ℤ) :=
  {k | ¬ (∀ c : ↥I, (K : ℤ) ≤ k c → c.1 ∈ G) ∨ k a ≤ (K : ℤ) ∨ k b < (K : ℤ) ∨
    (k a : ZMod ell) = 0 ∨ (k b : ZMod ell) = -1}

def excluded (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) : Set (Arr N) :=
  selected (N := N) I ⁻¹' excludedSelected I G K ell a b

theorem excluded_iff (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) (m : Arr N) :
    m ∈ excluded I G K ell a b ↔
      ¬ active I K m ⊆ G ∨ m.1 a.1 ≤ K ∨ m.1 b.1 < K ∨
        (m.1 a.1 : ZMod ell) = 0 ∨ (m.1 b.1 : ZMod ell) = -1 := by
  have hact : (∀ c : ↥I, (K : ℤ) ≤ (m.1 c.1 : ℤ) → c.1 ∈ G) ↔ active I K m ⊆ G := by
    constructor
    · intro h c hc
      have hc' := Finset.mem_filter.mp hc
      exact h ⟨c,hc'.1⟩ (by exact_mod_cast hc'.2)
    · intro h c hc
      exact h (Finset.mem_filter.mpr ⟨c.2, by exact_mod_cast hc⟩)
  change (¬ (∀ c : ↥I, (K : ℤ) ≤ (m.1 c.1 : ℤ) → c.1 ∈ G) ∨
    (m.1 a.1 : ℤ) ≤ (K : ℤ) ∨ (m.1 b.1 : ℤ) < (K : ℤ) ∨
    ((m.1 a.1 : ℤ) : ZMod ell) = 0 ∨ ((m.1 b.1 : ℤ) : ZMod ell) = -1) ↔ _
  rw [hact]
  simp only [Int.cast_natCast, Nat.cast_le, Nat.cast_lt]

/-- Exact excluded source mass, derived from H and I without an event-mass premise. -/
theorem excluded_mass (I : Finset ℤ) (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (v : ℤ → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta) (g : H N) (hg : ‖g‖ = 1)
    (herr : ∀ c ∈ I, ‖E N c c g - (v c : ℂ) • g‖ ≤ delta)
    (a b : ↥I) (hab : a.1 ≠ b.1) (ha : 4 / (ell : ℝ) ≤ v a.1) (hb : 4 / (ell : ℝ) ≤ v b.1) :
    mass g (excluded I (I.filter (fun c => 1 / (2 * (ell : ℝ)) ≤ v c)) (threshold N ell) ell a b) ≤
      (4 * (I.card : ℝ) + 2) * (ell : ℝ) ^ 2 * delta ^ 2 + 2 / (ell : ℝ) +
        (ell : ℝ) * selectedDistance I a.1 b.1 g := by
  let : NeZero ell := ⟨by omega⟩
  let G := I.filter (fun c => 1 / (2 * (ell : ℝ)) ≤ v c)
  let A : Set (Arr N) := {m | ¬ active I (threshold N ell) m ⊆ G}
  let B : Set (Arr N) := {m | m.1 a.1 ≤ threshold N ell}
  let C : Set (Arr N) := {m | m.1 b.1 < threshold N ell}
  let D : Set (Arr N) := {m | (m.1 a.1 : ZMod ell) = 0 ∨ (m.1 b.1 : ZMod ell) = -1}
  have he : excluded I G (threshold N ell) ell a b = A ∪ (B ∪ (C ∪ D)) := by
    ext m
    exact excluded_iff I G (threshold N ell) ell a b m
  have hA := active_not_good I ell hell hN v delta hdelta g herr
  have hB := endpoint_low_count ell hell hN a.1 (v a.1) delta hdelta ha g (herr a.1 a.2)
  have hC := endpoint_strict_count ell hell hN b.1 (v b.1) delta hdelta hb g (herr b.1 b.2)
  have hD := residue_union_bound I ell a.1 b.1 a.2 b.2 hab g hg
  have hu1 := mass_union g A (B ∪ (C ∪ D))
  have hu2 := mass_union g B (C ∪ D)
  have hu3 := mass_union g C D
  change mass g (excluded I G (threshold N ell) ell a b) ≤ _
  rw [he]
  change mass g A ≤ _ at hA
  change mass g B ≤ _ at hB
  change mass g C ≤ _ at hC
  change mass g D ≤ _ at hD
  linarith

/-- Avoiding the zero residue keeps a donor decrement in the same quotient interval. -/
theorem donor_quotient (ell m : ℕ) (hm : 0 < m) (hres : (m : ZMod ell) ≠ 0) :
    m / ell = (m - 1) / ell := by
  have hdiv : ¬ ell ∣ m := by simpa only [← ZMod.natCast_eq_zero_iff] using hres
  have hs : (m - 1 + 1) / ell = (m - 1) / ell + if ell ∣ m - 1 + 1 then 1 else 0 := Nat.succ_div
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), ite_eq_right hdiv, add_zero] at hs
  exact hs

/-- Avoiding residue -1 keeps a receiver increment in the same quotient interval. -/
theorem receiver_quotient (ell m : ℕ) (hres : (m : ZMod ell) ≠ -1) :
    m / ell = (m + 1) / ell := by
  have hdiv : ¬ ell ∣ m + 1 := by
    intro h
    have hz := (ZMod.natCast_eq_zero_iff (m + 1) ell).mpr h
    rw [Nat.cast_add, Nat.cast_one] at hz
    exact hres (eq_neg_iff_add_eq_zero.mpr hz)
  rw [Nat.succ_div, ite_eq_right hdiv, add_zero]

/-- Every allowed full-array source outside the actual excluded event has internal endpoints. -/
theorem not_excluded_internal (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I)
    (hab : a.1 ≠ b.1) (m : Donor N a.1) (hm : m.1 ∉ excluded I G K ell a b) :
    SameCell I K ell m.1 (destination N a.1 b.1 m) ∧ active I K m.1 ⊆ G := by
  have hx := (excluded_iff I G K ell a b m.1).not.mp hm
  push Not at hx
  obtain ⟨hgood,ha,hb,hra,hrb⟩ := hx
  have hda : (destination N a.1 b.1 m).1 a.1 = m.1.1 a.1 - 1 := shift_apply_donor m.1.1 hab
  have hdb : (destination N a.1 b.1 m).1 b.1 = m.1.1 b.1 + 1 := shift_apply_receiver m.1.1 hab
  have hdx : ∀ c, c ≠ a.1 → c ≠ b.1 → (destination N a.1 b.1 m).1 c = m.1.1 c :=
    fun c hca hcb => shift_apply_exterior m.1.1 hca hcb
  have hact : active I K m.1 = active I K (destination N a.1 b.1 m) := by
    ext c
    simp only [active, Finset.mem_filter]
    by_cases hca : c = a.1
    · subst c
      rw [hda]
      simp only [a.2, ha.le, Nat.le_sub_one_of_lt ha, and_self]
    · by_cases hcb : c = b.1
      · subst c
        rw [hdb]
        simp only [b.2, hb, hb.trans (Nat.le_succ _), and_self]
      · rw [hdx c hca hcb]
  refine ⟨⟨?_,hact,?_,?_⟩,hgood⟩
  · intro c hc
    exact (hdx c (by intro h; subst c; exact hc a.2) (by intro h; subst c; exact hc b.2)).symm
  · intro c hc hcin
    have hca : c ≠ a.1 := by
      intro h; subst c
      exact hcin (Finset.mem_filter.mpr ⟨a.2,by omega⟩)
    have hcb : c ≠ b.1 := by
      intro h; subst c
      exact hcin (Finset.mem_filter.mpr ⟨b.2,by omega⟩)
    exact (hdx c hca hcb).symm
  · intro c _
    by_cases hca : c = a.1
    · subst c
      rw [hda]
      exact donor_quotient ell _ m.2 hra
    · by_cases hcb : c = b.1
      · subst c
        rw [hdb]
        exact receiver_quotient ell _ hrb
      · rw [hdx c hca hcb]

/-- Any injective family contained in a full-array event has at most its actual mass. -/
theorem restricted_mass_le {X : Type*} (j : X → Arr N) (hj : Function.Injective j)
    (A : Set (Arr N)) (hA : ∀ x, j x ∈ A) (g : H N) :
    (∑' x, law g (j x)) ≤ mass g A := by
  let k : X → A := fun x => ⟨j x,hA x⟩
  have hk : Function.Injective k := by
    intro x y h
    apply hj
    exact congrArg (fun m : A => m.1) h
  have hs := (law_summable g).subtype (· ∈ A)
  exact (hs.comp_injective hk).tsum_le_tsum_of_inj k hk
    (fun m _ => law_nonneg g m.1) (fun _ => le_rfl) hs

abbrev Omitted (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) :=
  {m : Donor N a.1 // m.1 ∈ excluded I G K ell a b}

theorem omitted_source_injective (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) :
    Function.Injective (fun m : Omitted (N := N) I G K ell a b => m.1.1) := by
  intro m n h
  exact Subtype.ext (Subtype.ext h)

theorem omitted_target_injective (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) :
    Function.Injective (fun m : Omitted (N := N) I G K ell a b => destination N a.1 b.1 m.1) :=
  (destination_injective N a.1 b.1).comp Subtype.val_injective

/-- Actual omitted allowed-source mass is bounded by the excluded event. -/
theorem omitted_source_mass (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) (g : H N) :
    (∑' m : Omitted (N := N) I G K ell a b, law g m.1.1) ≤ mass g (excluded I G K ell a b) :=
  restricted_mass_le _ (omitted_source_injective I G K ell a b) _ (fun m => m.2) g

/-- Actual omitted targets lie in the literal selected translate of the excluded event. -/
theorem omitted_target_mem (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) (hab : a.1 ≠ b.1)
    (m : Omitted (N := N) I G K ell a b) :
    destination N a.1 b.1 m.1 ∈ selected (N := N) I ⁻¹'
      (selectedStep I b.1 a.1 ⁻¹' excludedSelected I G K ell a b) := by
  change selectedStep I b.1 a.1 (selected (N := N) I (destination N a.1 b.1 m.1)) ∈ excludedSelected I G K ell a b
  rw [selected_destination I a.1 b.1 hab m.1]
  change (selectedStepEquiv I a.1 b.1).symm ((selectedStepEquiv I a.1 b.1) (selected I m.1.1)) ∈ excludedSelected I G K ell a b
  rw [Equiv.symm_apply_apply]
  exact m.2

/-- Source/target event bookkeeping is proved from G and H0 for the actual residual sum. -/
theorem omitted_target_mass (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) (hab : a.1 ≠ b.1)
    (c : OrderedSeeds N) (t : ℤ → Phase) (g : H N) (hg : ‖g‖ = 1) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2)
    (haG : a.1 ∈ G) (hbG : b.1 ∈ G) :
    (∑' m : Omitted (N := N) I G K ell a b, law g (destination N a.1 b.1 m.1)) ≤
      mass g (excluded I G K ell a b) + Real.sqrt (2 * eta) := by
  have hj := restricted_mass_le _ (omitted_target_injective I G K ell a b) _
    (omitted_target_mem I G K ell a b hab) g
  have he := full_event_from_residual_sum I G c t g hg eta heta hres a.1 b.1 haG hbG hab
    (excludedSelected I G K ell a b)
  have hl := neg_abs_le (mass g (excluded I G K ell a b) -
    mass g (selected (N := N) I ⁻¹' (selectedStep I b.1 a.1 ⁻¹' excludedSelected I G K ell a b)))
  change |mass g (excluded I G K ell a b) - _| ≤ _ at he
  linarith

/-- Pointwise omitted allowed-edge energy uses only its actual source and target coefficients. -/
theorem allowed_edge_energy (Q : Arr N → Phase) (t : ℤ → Phase) (a b : ℤ)
    (g : H N) (m : Donor N a) :
    ‖(W Q a b g - ((t a).1 * conj (t b).1) • g) (destination N a b m)‖ ^ 2 ≤
      2 * law g m.1 + 2 * law g (destination N a b m) := by
  let zeta := (t a).1 * conj (t b).1
  have hz : ‖zeta‖ = 1 := by dsimp [zeta]; rw [norm_mul, Complex.norm_conj, (t a).2, (t b).2, one_mul]
  change ‖transfer a b (edgePhase Q a b) g (destination N a b m) - zeta * g (destination N a b m)‖ ^ 2 ≤ _
  rw [transfer_at_destination]
  have hn := norm_sub_le ((edgePhase Q a b m).1 * g m.1) (zeta * g (destination N a b m))
  simp only [norm_mul, (edgePhase Q a b m).2, hz, one_mul] at hn
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  dsimp only [law]
  nlinarith [sq_nonneg (‖g m.1‖ - ‖g (destination N a b m)‖)]

/-- Summed actual omitted allowed-edge energy has no supplied source or target conclusion. -/
theorem omitted_energy (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) (hab : a.1 ≠ b.1)
    (Q : Arr N → Phase) (c : OrderedSeeds N) (t : ℤ → Phase)
    (g : H N) (hg : ‖g‖ = 1) (eta : ℝ) (heta : 0 ≤ eta)
    (hres : (∑ p : Pairs G, ‖pairResidual c t G g p‖ ^ 2) ≤ eta ^ 2)
    (haG : a.1 ∈ G) (hbG : b.1 ∈ G) :
    Summable (fun m : Omitted (N := N) I G K ell a b =>
      ‖(W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g) (destination N a.1 b.1 m.1)‖ ^ 2) ∧
    (∑' m : Omitted (N := N) I G K ell a b,
      ‖(W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g) (destination N a.1 b.1 m.1)‖ ^ 2) ≤
      4 * mass g (excluded I G K ell a b) + 2 * Real.sqrt (2 * eta) := by
  let R := W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g
  have hs : Summable (fun m : Omitted (N := N) I G K ell a b => law g m.1.1) :=
    (law_summable g).comp_injective (omitted_source_injective I G K ell a b)
  have ht : Summable (fun m : Omitted (N := N) I G K ell a b => law g (destination N a.1 b.1 m.1)) :=
    (law_summable g).comp_injective (omitted_target_injective I G K ell a b)
  have he : Summable (fun m : Omitted (N := N) I G K ell a b => ‖R (destination N a.1 b.1 m.1)‖ ^ 2) :=
    (summable_energy R).comp_injective (omitted_target_injective I G K ell a b)
  refine ⟨he,?_⟩
  have hbound : (∑' m : Omitted (N := N) I G K ell a b, ‖R (destination N a.1 b.1 m.1)‖ ^ 2) ≤
      2 * (∑' m : Omitted (N := N) I G K ell a b, law g m.1.1) +
      2 * (∑' m : Omitted (N := N) I G K ell a b, law g (destination N a.1 b.1 m.1)) := by
    calc
      _ ≤ ∑' m : Omitted (N := N) I G K ell a b,
          (2 * law g m.1.1 + 2 * law g (destination N a.1 b.1 m.1)) :=
        he.tsum_le_tsum (fun m => allowed_edge_energy Q t a.1 b.1 g m.1)
          ((hs.mul_left 2).add (ht.mul_left 2))
      _ = _ := by rw [Summable.tsum_add (hs.mul_left 2) (ht.mul_left 2), tsum_mul_left, tsum_mul_left]
  have hsource := omitted_source_mass I G K ell a b g
  have htarget := omitted_target_mass I G K ell a b hab c t g hg eta heta hres haG hbG
  change (∑' m : Omitted (N := N) I G K ell a b, ‖R (destination N a.1 b.1 m.1)‖ ^ 2) ≤ _
  linarith

/-- The actual missing receiver coefficient has exactly the boundary source energy. -/
theorem receiver_boundary_energy (Q : Arr N → Phase) (t : ℤ → Phase) (a b : ℤ) (hab : a ≠ b)
    (g : H N) (m : Arr N) (hm : m.1 b = 0) :
    ‖(W Q a b g - ((t a).1 * conj (t b).1) • g) m‖ ^ 2 = law g m := by
  have hd : ¬ DonorOK b m.1 := by change ¬ 0 < m.1 b; omega
  change ‖transfer a b (edgePhase Q a b) g m - ((t a).1 * conj (t b).1) * g m‖ ^ 2 = _
  rw [transfer_off_receiver a b hab (edgePhase Q a b) g m hd, zero_sub, norm_neg,
    norm_mul, norm_mul, Complex.norm_conj, (t a).2, (t b).2, one_mul, one_mul]
  rfl

/-- Tested endpoints belong to the actual cutoff good set. -/
theorem tested_good (I : Finset ℤ) (ell : ℕ) (hell : 2 ≤ ell) (v : ℤ → ℝ)
    (a : ℤ) (haI : a ∈ I) (ha : 4 / (ell : ℝ) ≤ v a) :
    a ∈ I.filter (fun c => 1 / (2 * (ell : ℝ)) ≤ v c) := by
  refine Finset.mem_filter.mpr ⟨haI,?_⟩
  have he : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hp : 0 ≤ (ell : ℝ)⁻¹ := by positivity
  simp only [div_eq_mul_inv, mul_inv_rev] at ha ⊢
  norm_num
  linarith

/-- The EXACT printed omitted-edge plus missing-receiver squared-energy bound. -/
theorem omitted_boundary_bound (I : Finset ℤ) (ell : ℕ) (hell : 2 ≤ ell) (hN : ell ≤ N)
    (v : ℤ → ℝ) (delta eta : ℝ) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (Q : Arr N → Phase) (c : OrderedSeeds N) (t : ℤ → Phase) (g : H N) (hg : ‖g‖ = 1)
    (herr : ∀ j ∈ I, ‖E N j j g - (v j : ℂ) • g‖ ≤ delta)
    (hres : (∑ p : Pairs (I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)),
      ‖pairResidual c t (I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)) g p‖ ^ 2) ≤ eta ^ 2)
    (a b : ↥I) (hab : a.1 ≠ b.1) (ha : 4 / (ell : ℝ) ≤ v a.1) (hb : 4 / (ell : ℝ) ≤ v b.1) :
    (∑' m : Omitted (N := N) I (I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)) (threshold N ell) ell a b,
      ‖(W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g) (destination N a.1 b.1 m.1)‖ ^ 2) +
      mass g {m : Arr N | m.1 b.1 = 0} ≤
      (16 * (I.card : ℝ) + 9) * (ell : ℝ) ^ 2 * delta ^ 2 + 8 / (ell : ℝ) +
        (4 * (ell : ℝ) + 2) * Real.sqrt (2 * eta) := by
  let G := I.filter (fun j => 1 / (2 * (ell : ℝ)) ≤ v j)
  have haG := tested_good I ell hell v a.1 a.2 ha
  have hbG := tested_good I ell hell v b.1 b.2 hb
  have he := (omitted_energy I G (threshold N ell) ell a b hab Q c t g hg eta heta hres haG hbG).2
  have hm := excluded_mass I ell hell hN v delta hdelta g hg herr a b hab ha hb
  have hd := (selected_tv_from_residual_sum I G c t g hg eta heta hres a.1 b.1 haG hbG hab).2
  change selectedDistance I a.1 b.1 g ≤ Real.sqrt (2 * eta) at hd
  have hs := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg ell)
  have hbdy := endpoint_zero_count ell hell hN b.1 (v b.1) delta hdelta hb g (herr b.1 b.2)
  have hm' : mass g (excluded I G (threshold N ell) ell a b) ≤
      (4 * (I.card : ℝ) + 2) * (ell : ℝ) ^ 2 * delta ^ 2 + 2 / (ell : ℝ) +
        (ell : ℝ) * Real.sqrt (2 * eta) := hm.trans (add_le_add le_rfl hs)
  simp only [div_eq_mul_inv] at hm' ⊢
  nlinarith

abbrev Kept (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) :=
  {m : Donor N a.1 // m.1 ∉ excluded I G K ell a b}

/-- The retained source family injects into the SAME E3 internal-edge family. -/
theorem kept_energy_le_internal (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) (hab : a.1 ≠ b.1)
    (Q : Arr N → Phase) (t : ℤ → Phase) (g : H N) :
    (∑' m : Kept (N := N) I G K ell a b,
      ‖(W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g) (destination N a.1 b.1 m.1)‖ ^ 2) ≤
    ∑' m : Internal (N := N) I G K ell a.1 b.1,
      ‖(W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g) (destination N a.1 b.1 m.1)‖ ^ 2 := by
  let R := W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g
  let j : Kept (N := N) I G K ell a b → Internal (N := N) I G K ell a.1 b.1 :=
    fun m => ⟨m.1,not_excluded_internal I G K ell a b hab m.1 m.2⟩
  have hj : Function.Injective j := by
    intro m n h
    exact Subtype.ext (congrArg (fun m : Internal (N := N) I G K ell a.1 b.1 => m.1) h)
  have ht := (summable_energy R).comp_injective (internal_target_injective I G K ell a.1 b.1)
  have hs := ht.comp_injective hj
  exact hs.tsum_le_tsum_of_inj j hj (fun _ _ => sq_nonneg _) (fun _ => le_rfl) ht

/-- Exact full-energy decomposition into retained allowed edges, omitted allowed
edges and the receiver-zero boundary. No exterior list enters this partition. -/
theorem residual_energy_partition (I G : Finset ℤ) (K ell : ℕ) (a b : ↥I) (hab : a.1 ≠ b.1)
    (Q : Arr N → Phase) (t : ℤ → Phase) (g : H N) :
    ‖W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g‖ ^ 2 =
      (∑' m : Kept (N := N) I G K ell a b,
        ‖(W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g) (destination N a.1 b.1 m.1)‖ ^ 2) +
      (∑' m : Omitted (N := N) I G K ell a b,
        ‖(W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g) (destination N a.1 b.1 m.1)‖ ^ 2) +
      mass g {m : Arr N | m.1 b.1 = 0} := by
  let R := W Q a.1 b.1 g - ((t a.1).1 * conj (t b.1).1) • g
  let Rec : Set (Arr N) := {m | DonorOK b.1 m.1}
  let Bad : Set (Donor N a.1) := {m | m.1 ∈ excluded I G K ell a b}
  have hfull := (summable_energy R).tsum_subtype_add_tsum_subtype_compl Rec
  have hrec : (∑' m : Rec, ‖R m.1‖ ^ 2) = ∑' m : Donor N a.1, ‖R (destination N a.1 b.1 m)‖ ^ 2 :=
    ((donorEquiv a.1 b.1 hab).tsum_eq (fun m => ‖R m.1‖ ^ 2)).symm
  have hboundary : (∑' m : ↥(Recᶜ), ‖R m.1‖ ^ 2) = mass g {m : Arr N | m.1 b.1 = 0} := by
    have he : Recᶜ = {m : Arr N | m.1 b.1 = 0} := by
      ext m
      change ¬ 0 < m.1 b.1 ↔ m.1 b.1 = 0
      omega
    rw [he]
    exact tsum_congr (fun m => receiver_boundary_energy Q t a.1 b.1 hab g m.1 m.2)
  have hdonor := ((summable_energy R).comp_injective (destination_injective N a.1 b.1)).tsum_subtype_add_tsum_subtype_compl Bad
  change (∑' m : Omitted (N := N) I G K ell a b, ‖R (destination N a.1 b.1 m.1)‖ ^ 2) +
    (∑' m : Kept (N := N) I G K ell a b, ‖R (destination N a.1 b.1 m.1)‖ ^ 2) =
      ∑' m : Donor N a.1, ‖R (destination N a.1 b.1 m)‖ ^ 2 at hdonor
  rw [hrec,hboundary,tsum_energy,← hdonor] at hfull
  dsimp only [R] at hfull
  linarith

end QuantumNLS.FiniteCellOmissions

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FiniteCellOmissions.excludedSelected
#print axioms QuantumNLS.FiniteCellOmissions.excluded
#print axioms QuantumNLS.FiniteCellOmissions.excluded_iff
#print axioms QuantumNLS.FiniteCellOmissions.excluded_mass
#print axioms QuantumNLS.FiniteCellOmissions.donor_quotient
#print axioms QuantumNLS.FiniteCellOmissions.receiver_quotient
#print axioms QuantumNLS.FiniteCellOmissions.not_excluded_internal
#print axioms QuantumNLS.FiniteCellOmissions.restricted_mass_le
#print axioms QuantumNLS.FiniteCellOmissions.Omitted
#print axioms QuantumNLS.FiniteCellOmissions.omitted_source_injective
#print axioms QuantumNLS.FiniteCellOmissions.omitted_target_injective
#print axioms QuantumNLS.FiniteCellOmissions.omitted_source_mass
#print axioms QuantumNLS.FiniteCellOmissions.omitted_target_mem
#print axioms QuantumNLS.FiniteCellOmissions.omitted_target_mass
#print axioms QuantumNLS.FiniteCellOmissions.allowed_edge_energy
#print axioms QuantumNLS.FiniteCellOmissions.omitted_energy
#print axioms QuantumNLS.FiniteCellOmissions.receiver_boundary_energy
#print axioms QuantumNLS.FiniteCellOmissions.tested_good
#print axioms QuantumNLS.FiniteCellOmissions.omitted_boundary_bound
#print axioms QuantumNLS.FiniteCellOmissions.Kept
#print axioms QuantumNLS.FiniteCellOmissions.kept_energy_le_internal
#print axioms QuantumNLS.FiniteCellOmissions.residual_energy_partition

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FiniteCellOmissions.excludedSelected,
    ``QuantumNLS.FiniteCellOmissions.excluded,
    ``QuantumNLS.FiniteCellOmissions.excluded_iff,
    ``QuantumNLS.FiniteCellOmissions.excluded_mass,
    ``QuantumNLS.FiniteCellOmissions.donor_quotient,
    ``QuantumNLS.FiniteCellOmissions.receiver_quotient,
    ``QuantumNLS.FiniteCellOmissions.not_excluded_internal,
    ``QuantumNLS.FiniteCellOmissions.restricted_mass_le,
    ``QuantumNLS.FiniteCellOmissions.Omitted,
    ``QuantumNLS.FiniteCellOmissions.omitted_source_injective,
    ``QuantumNLS.FiniteCellOmissions.omitted_target_injective,
    ``QuantumNLS.FiniteCellOmissions.omitted_source_mass,
    ``QuantumNLS.FiniteCellOmissions.omitted_target_mem,
    ``QuantumNLS.FiniteCellOmissions.omitted_target_mass,
    ``QuantumNLS.FiniteCellOmissions.allowed_edge_energy,
    ``QuantumNLS.FiniteCellOmissions.omitted_energy,
    ``QuantumNLS.FiniteCellOmissions.receiver_boundary_energy,
    ``QuantumNLS.FiniteCellOmissions.tested_good,
    ``QuantumNLS.FiniteCellOmissions.omitted_boundary_bound,
    ``QuantumNLS.FiniteCellOmissions.Kept,
    ``QuantumNLS.FiniteCellOmissions.kept_energy_le_internal,
    ``QuantumNLS.FiniteCellOmissions.residual_energy_partition]
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
  Lean.logInfo m!"FiniteCellOmissions aggregate audit PASS: {seen.size} transitive constants. All declarations independent of EXT-001."
