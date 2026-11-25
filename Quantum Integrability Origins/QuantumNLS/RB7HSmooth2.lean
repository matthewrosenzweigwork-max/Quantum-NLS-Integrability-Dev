import Mathlib
import QuantumNLS.RB7Final

/-!
# R-7B122087 `thm:hierarchy`, clauses 4-5, part 1: smooth data, chart coordinates, smooth flow map (RB7HSmooth2, haiku_inventory)

Supersedes `RB7HSmooth` (failed build `RB7HSmooth.5fa2501d`, kept unchanged).  Changes:
* no `Kn` / `ℝ≥0` cast: the level-`k` inverse chart is `gN hR C k := gAt hR C (k : ℝ) _`, built directly from the REG-015
  forward homeomorphism `Fh` at the real level `(k : ℝ)`, so every level-`k` statement has the type `h02 L (k : ℝ)`;
* the docstring of `coordsAll` is removed (it was the parse error), `continuous_smAll_apply` goes through an explicit
  `continuous_smAll_dom`, and `Lk_cont` names its continuous pieces (the timeout).

Smooth topology: `SmData L` carries the topology induced by `smAll x k := smoothL2 x ∈ H^k` (product over `k : ℕ`).

Proved here (no sorry, no new axiom):
* `gAt`, `gAt_cont`, `gAt_val`: the inverse chart `h^s → H^s` at every real level `s ≥ 0`, continuous, with `(gAt z).val = Ψ (toBase z)`;
* `gN_eq_smAll`: if `w : h^k` has the chart coordinates of the smooth datum `y` then `gN k w = smAll y k`;
* `smAll_Pr`: `smAll (Pr r (τ,x)) k = gN k (Lk r k τ x)` (the smooth one-step flow in level-`k` coordinates);
* `Pr_cont`, `compSm`, `compSm_fn`, `compSm_cont`: continuity of the finite compositions of the smooth flow maps.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped ComplexConjugate Topology NNReal ContDiff
open MeasureTheory Filter Set

namespace QuantumNLS.RB7HSm2

open QuantumNLS.RB7 QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.Reg015Setting
open QuantumNLS.ClassicalCharges QuantumNLS.PhysicalTensor QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.HierarchyFlow

variable {L κ : ℝ} [Fact (0 < L)] {hκ : 0 < κ}

/-! ## Smooth periodic data and the smooth topology -/

/-- Smooth periodic profiles (the carrier of the smooth topology). -/
structure SmData (L : ℝ) where
  /-- The profile. -/
  fn : ℝ → ℂ
  /-- It is smooth and `L`-periodic. -/
  smooth : SmoothPeriodic L fn

/-- The embedding of smooth data into the product `∀ k, H^k`: `smoothL2` in every `H^k`. -/
def smAll (x : SmData L) : ∀ k : ℕ, H02 L (k : ℝ) := fun k =>
  WField.mk (smoothL2 x.smooth) (QuantumNLS.RB7.memHs_of_smooth x.smooth (k : ℝ))

/-- The smooth topology: induced by `smAll` from the product topology of the `H^k`. -/
instance smTop : TopologicalSpace (SmData L) := TopologicalSpace.induced smAll inferInstance

theorem continuous_smAll_dom : Continuous (smAll : SmData L → ∀ k : ℕ, H02 L (k : ℝ)) :=
  continuous_induced_dom

theorem continuous_smAll_apply (k : ℕ) : Continuous fun x : SmData L => smAll x k :=
  (continuous_apply k).comp continuous_smAll_dom

/-! ## The REG-015 forward homeomorphisms and the inverse chart at real levels -/

variable (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ)

/-- The REG-015 forward homeomorphism `H^s → Target` (chosen from `regHomeo`). -/
def Fh (s : ℝ) (hs0 : 0 ≤ s) : H02 L s ≃ₜ Target (L := L) (Set.range C.Φ) s hs0 :=
  Classical.choose (regHomeo hR C s hs0)

theorem Fh_coord (s : ℝ) (hs0 : 0 ≤ s) (v : H02 L s) (n : ℤ) :
    ((Fh hR C s hs0) v).val.val n = C.Φ v.val n :=
  Classical.choose_spec (regHomeo hR C s hs0) v n

/-- The inverse chart `h^s → H^s` at the real level `s ≥ 0` (the inverse of `Fh`, through the chart `Ψ`). -/
def gAt (s : ℝ) (hs : 0 ≤ s) : h02 L s → H02 L s := fun z =>
  (Fh hR C s hs).symm (⟨z, ⟨C.Ψ (toBase (L := L) s hs z), C.ΦΨ _⟩⟩ : Target (L := L) (Set.range C.Φ) s hs)

theorem gAt_cont (s : ℝ) (hs : 0 ≤ s) : Continuous (gAt hR C s hs) := by
  let mk : h02 L s → Target (L := L) (Set.range C.Φ) s hs := fun z =>
    ⟨z, ⟨C.Ψ (toBase (L := L) s hs z), C.ΦΨ _⟩⟩
  have hmk : Continuous mk := Continuous.subtype_mk continuous_id _
  exact (Fh hR C s hs).symm.continuous.comp hmk

theorem gAt_val (s : ℝ) (hs : 0 ≤ s) (z : h02 L s) :
    (gAt hR C s hs z).val = C.Ψ (toBase (L := L) s hs z) := by
  let mk : Target (L := L) (Set.range C.Φ) s hs := ⟨z, ⟨C.Ψ (toBase (L := L) s hs z), C.ΦΨ _⟩⟩
  have h1 : Fh hR C s hs (gAt hR C s hs z) = mk := (Fh hR C s hs).apply_symm_apply _
  have h2 : ∀ n : ℤ, C.Φ (gAt hR C s hs z).val n = (toBase (L := L) s hs z) n := by
    intro n
    rw [← Fh_coord hR C s hs (gAt hR C s hs z) n, h1]
    exact (toBase_apply (L := L) s hs z n).symm
  have h3 : C.Φ (gAt hR C s hs z).val = toBase (L := L) s hs z := lp.ext (funext h2)
  rw [← h3, C.ΨΦ]

/-- The level-`k` inverse chart at the natural level `k` (the real number `(k : ℝ)`). -/
def gN (k : ℕ) : h02 L (k : ℝ) → H02 L (k : ℝ) := gAt hR C (k : ℝ) (Nat.cast_nonneg k)

theorem gN_cont (k : ℕ) : Continuous (gN hR C k) :=
  gAt_cont hR C (k : ℝ) (Nat.cast_nonneg k)

theorem gN_val (k : ℕ) (z : h02 L (k : ℝ)) :
    (gN hR C k z).val = C.Ψ (toBase (L := L) (k : ℝ) (Nat.cast_nonneg k) z) :=
  gAt_val hR C (k : ℝ) (Nat.cast_nonneg k) z

/-- If `w` has the chart coordinates of the smooth datum `y`, then `gN k w` is the `H^k` class of `y`. -/
theorem gN_eq_smAll (k : ℕ) (y : SmData L) (w : h02 L (k : ℝ))
    (hw : ∀ n : ℤ, w.val n = C.Φ (smoothL2 y.smooth) n) : gN hR C k w = smAll y k := by
  have hl : toBase (L := L) (k : ℝ) (Nat.cast_nonneg k) w = C.Φ (smoothL2 y.smooth) :=
    lp.ext (funext fun n => (toBase_apply (L := L) (k : ℝ) (Nat.cast_nonneg k) w n).trans (hw n))
  have key : C.Ψ (toBase (L := L) (k : ℝ) (Nat.cast_nonneg k) w) = smoothL2 y.smooth := by
    rw [hl, C.ΨΦ]
  apply WField.ext
  exact (gN_val hR C k w).trans key

/-! ## Level-`k` coordinates of smooth data -/

/-- The level-`a` coordinates of a smooth datum, for a natural level `a`. -/
def wN (a : ℕ) (x : SmData L) : h02 L (a : ℝ) :=
  ((Fh hR C (a : ℝ) (Nat.cast_nonneg a)) (smAll x a)).val

theorem wN_apply (a : ℕ) (x : SmData L) (n : ℤ) :
    (wN hR C a x).val n = C.Φ (smoothL2 x.smooth) n :=
  Fh_coord hR C _ _ (smAll x a) n

theorem wN_val (a : ℕ) (x : SmData L) : (wN hR C a x).val = fun n => C.Φ (smoothL2 x.smooth) n :=
  funext fun n => wN_apply hR C a x n

theorem wN_cont (a : ℕ) : Continuous fun x : SmData L => wN hR C a x :=
  continuous_subtype_val.comp ((Fh hR C (a : ℝ) (Nat.cast_nonneg a)).continuous.comp (continuous_smAll_apply a))

/-- The level-`a` coordinate sequence of smooth data equals the one of `z0` (the `h^0` datum). -/
theorem wN_eq_z0 (a : ℕ) (x : SmData L) : (wN hR C a x).val = (z0 hR C x.fn).val := by
  rw [z0_val hR C x.smooth]
  exact wN_val hR C a x

/-! ## Levels and the restricted sequence flow -/

/-- The level used to compute the order-`r` flow restricted to `H^k`. -/
def levN (r k : ℕ) : ℕ := k + (3 * r + 7)

theorem SOf_le_levN (r k : ℕ) : ((SOf r : ℝ≥0) : ℝ) ≤ ((levN r k : ℕ) : ℝ) := by
  rw [SOf_coe]
  unfold levN
  push_cast
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem k_le_levN (r k : ℕ) : (k : ℝ) ≤ ((levN r k : ℕ) : ℝ) := by
  unfold levN
  push_cast
  nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

/-- The order-`r` sequence flow at time `τ`, restricted to `H^k` (through level `levN r k`). -/
def Lk (r k : ℕ) (τ : ℝ) (x : SmData L) : h02 L (k : ℝ) :=
  h02_mono L (k_le_levN r k)
    (zflow hR C r ((levN r k : ℕ) : ℝ) (SOf_le_levN r k) τ (wN hR C (levN r k) x))

/-- Continuity of the sequence flow in time and state, at a fixed level. -/
theorem continuous_zflow (r : ℕ) (a : ℝ) (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a) :
    Continuous fun p : ℝ × h02 L a => zflow hR C r a ha p.1 p.2 := by
  have hc1 : Continuous fun τ : ℝ => (τ • one1 : Unit → ℝ) := by
    refine continuous_pi fun u => ?_
    simp only [Pi.smul_apply, one1, smul_eq_mul, mul_one]
    exact continuous_id
  have hc : Continuous fun p : ℝ × h02 L a => ((p.1 • one1 : Unit → ℝ), p.2) :=
    (hc1.comp continuous_fst).prodMk continuous_snd
  exact (continuous_flow (sdata hR C r a ha).D).comp hc

/-- The sequence flow along a continuous state map `w : X → h^a`: jointly continuous in `(time, point)`.
The level `a` is a bare variable here, so no `levN` / `SOf` term is unfolded during unification. -/
theorem continuous_zflow_comp {X : Type*} [TopologicalSpace X] (r : ℕ) (a : ℝ) (ha : ((SOf r : ℝ≥0) : ℝ) ≤ a)
    (w : X → h02 L a) (hw : Continuous w) :
    Continuous fun p : ℝ × X => zflow hR C r a ha p.1 (w p.2) := by
  have hc1 : Continuous fun τ : ℝ => (τ • one1 : Unit → ℝ) := by
    refine continuous_pi fun u => ?_
    simp only [Pi.smul_apply, one1, smul_eq_mul, mul_one]
    exact continuous_id
  have hc : Continuous fun p : ℝ × X => ((p.1 • one1 : Unit → ℝ), w p.2) :=
    (hc1.comp continuous_fst).prodMk (hw.comp continuous_snd)
  exact (continuous_flow (sdata hR C r a ha).D).comp hc

theorem Lk_cont (r k : ℕ) : Continuous fun p : ℝ × SmData L => Lk hR C r k p.1 p.2 := by
  have hz : Continuous fun p : ℝ × SmData L =>
      zflow hR C r ((levN r k : ℕ) : ℝ) (SOf_le_levN r k) p.1 (wN hR C (levN r k) p.2) :=
    continuous_zflow_comp hR C r ((levN r k : ℕ) : ℝ) (SOf_le_levN r k)
      (fun x : SmData L => wN hR C (levN r k) x) (wN_cont hR C (levN r k))
  have hm : Continuous ⇑(h02_mono L (k_le_levN r k)) := (h02_mono L (k_le_levN r k)).continuous
  exact hm.comp hz

/-! ## The smooth flow map `Pr` and its coordinate identity -/

/-- The order-`r` physical flow of `RB7Final.chartFlow` on smooth data, as a map `SmData → SmData`. -/
def Pr (r : ℕ) (p : ℝ × SmData L) : SmData L :=
  ⟨chartFlow hR C r p.1 p.2.fn, ((isHamFlow_chart hR C r p.2.fn p.2.smooth).2.2 p.1).1⟩

theorem Pr_fn (r : ℕ) (p : ℝ × SmData L) : (Pr hR C r p).fn = chartFlow hR C r p.1 p.2.fn := rfl

/-- **The coordinate identity.** The `H^k`-coordinates of the order-`r` smooth flow are the level-`k` inverse chart
applied to the restricted sequence flow. -/
theorem smAll_Pr (r k : ℕ) (p : ℝ × SmData L) :
    smAll (Pr hR C r p) k = gN hR C k (Lk hR C r k p.1 p.2) := by
  have hsm : SmoothPeriodic L (Pr hR C r p).fn := (Pr hR C r p).smooth
  obtain ⟨hf, heq⟩ := (RB7H.joint_smooth (curveOf hR C r p.2.fn) (hlift_chart hR C r p.2.smooth)).2.2 p.1
  have hl : smoothL2 hsm = curveOf hR C r p.2.fn p.1 := heq
  -- coordinates of the sequence flow at level `levN r k`, read off at level `0`
  have hZ : (Zf hR C r p.1 (z0 hR C p.2.fn)).val = (Lk hR C r k p.1 p.2).val :=
    (Zf_val hR C r p.1 (z0 hR C p.2.fn) (SOf_le_levN r k) (wN hR C (levN r k) p.2)
      (wN_eq_z0 hR C _ _)).trans rfl
  have hcoord : toBase (L := L) (((0 : ℝ≥0) : ℝ)) (NNReal.coe_nonneg 0) (Zf hR C r p.1 (z0 hR C p.2.fn)) =
      toBase (L := L) (k : ℝ) (Nat.cast_nonneg k) (Lk hR C r k p.1 p.2) :=
    by
      apply lp.ext
      funext n
      rw [toBase_apply, toBase_apply, hZ]
  -- the curve value is the chart image; `PsiC_val` is applied as a term (no `rw`, see the note above)
  have hPsi : curveOf hR C r p.2.fn p.1 =
      C.Ψ (toBase (L := L) (k : ℝ) (Nat.cast_nonneg k) (Lk hR C r k p.1 p.2)) :=
    (PsiC_val C (Zf hR C r p.1 (z0 hR C p.2.fn))).trans (congrArg C.Ψ hcoord)
  apply WField.ext
  rw [gN_val]
  exact hl.trans hPsi

/-- The map `Pr` is continuous for the smooth topology. -/
theorem Pr_cont (r : ℕ) : Continuous fun p : ℝ × SmData L => Pr hR C r p := by
  refine continuous_induced_rng.2 (continuous_pi fun k => ?_)
  have hfun : (fun p : ℝ × SmData L => smAll (Pr hR C r p) k) =
      fun p => gN hR C k (Lk hR C r k p.1 p.2) := funext fun p => smAll_Pr hR C r k p
  change Continuous fun p : ℝ × SmData L => smAll (Pr hR C r p) k
  rw [hfun]
  exact (gN_cont hR C k).comp (Lk_cont hR C r k)

/-! ## Compositions along finite joint times -/

/-- The composition `Pr r_1 (t_{r_1}) ∘ ⋯ ∘ Pr r_n (t_{r_n})` on smooth data, as in `jointClassicalFlow`. -/
def compSm : List ℕ → ((ℕ → ℝ) × SmData L) → SmData L
  | [], p => p.2
  | r :: l, p => Pr hR C r (p.1 r, compSm l p)

theorem compSm_fn (l : List ℕ) (p : (ℕ → ℝ) × SmData L) :
    (compSm hR C l p).fn = (l.map fun r => chartFlow hR C r (p.1 r)).foldr (· ∘ ·) id p.2.fn := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    simp only [compSm, List.map_cons, List.foldr_cons, Pr_fn]
    rw [ih]
    rfl

theorem compSm_cont (l : List ℕ) : Continuous fun p : (ℕ → ℝ) × SmData L => compSm hR C l p := by
  induction l with
  | nil => exact continuous_snd
  | cons r l ih =>
    have h1 : Continuous fun p : (ℕ → ℝ) × SmData L => (p.1 r, compSm hR C l p) :=
      ((continuous_apply r).comp continuous_fst).prodMk ih
    exact (Pr_cont hR C r).comp h1

end QuantumNLS.RB7HSm2

#print axioms QuantumNLS.RB7HSm2.continuous_smAll_dom
#print axioms QuantumNLS.RB7HSm2.gAt_cont
#print axioms QuantumNLS.RB7HSm2.gAt_val
#print axioms QuantumNLS.RB7HSm2.gN_eq_smAll
#print axioms QuantumNLS.RB7HSm2.wN_cont
#print axioms QuantumNLS.RB7HSm2.Lk_cont
#print axioms QuantumNLS.RB7HSm2.smAll_Pr
#print axioms QuantumNLS.RB7HSm2.Pr_cont
#print axioms QuantumNLS.RB7HSm2.compSm_fn
#print axioms QuantumNLS.RB7HSm2.compSm_cont
