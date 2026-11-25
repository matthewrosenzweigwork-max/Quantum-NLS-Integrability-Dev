import Mathlib
import QuantumNLS.RB7Glue
import QuantumNLS.RB7Bridge

/-!
# R-7B122087 `thm:hierarchy`: the REG-015 homeomorphism clause turned into the chart data used by the final assembly (RB7Reg)

* `REG015Concl hκ`: the conclusion of `Reg015Assembly.REG015Input` (and of `Reg015HFinal.REG015_final`), the SINGLE named input of the final assembly.
  `REG015Concl_of_inputs`: it follows from `REG015Input` with its three named inputs (`reg010`, `reg011`, `reg013`).
* `chartHomeo C`: the accepted chart `Φ : L² → ℓ²` as a homeomorphism onto its range with exact moduli, so the third clause of `REG015Concl` applies.
* `exists_g`: for every order `S` the continuous restriction `g : h^S → H^S` of the inverse chart (`(g z).val = Ψ(toBase z)`), exactly the input of `RB7Glue.Fr_data`.
* `hinf_smooth`: for smooth periodic `f` the chart coordinates of `smoothL2 f` are in `h^s` for every `s ≥ 0`.
* `qOf`, `SOf` (printed `q = r+2`, `s = 3q+1`), `gOf`, `IOf`, `Fd`: the functional `F_r = I_{r+1} ∘ Ψ` on `h^{S_r}` (`C²`, coordinatewise-rotation invariant) chosen once and for all.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped ComplexConjugate Topology NNReal
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.PhysicalTensor QuantumNLS.Fourier
open QuantumNLS.RootWeightedCellsR26 QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound64ExtendedMeasure QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.Reg015Setting QuantumNLS.LossSobolev QuantumNLS.ClassicalCharges
open QuantumNLS.SmoothScalarMomentsPhysical

variable {L κ : ℝ} [Fact (0 < L)]

/-- The conclusion of `REG015Input` (= that of `Reg015HFinal.REG015_final`): the single named input of the final assembly. -/
def REG015Concl (hκ : 0 < κ) : Prop :=
    ∀ s : ℝ, ∀ hs0 : 0 ≤ s,
      (∀ u : L2T L,
        ((∃ v : H02 L s, v.val = u) ↔
          Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) ∧
        (Integrable (fun t : ℝ => (1+|t|)^(2*s)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u) ↔
          Summable (fun n : ℤ => (1+|momentum L n|)^(2*s) *
            (QuantumNLS.RootIndexedMasses.masses hκ u).1 n))) ∧
      (∃ A : H02 L s → lp (fun _ : ℤ => ℝ) 1,
        (∀ u n, A u n = (1+|momentum L n|)^(2*s) *
          (QuantumNLS.RootIndexedMasses.masses hκ u.val).1 n) ∧
        Continuous A ∧
        ∀ B : Set (H02 L s), Bornology.IsBounded B → Bornology.IsBounded (A '' B)) ∧
      (∀ (V : Set Seq) (e : L2T L ≃ₜ V), ExactModuli e hκ →
        ∃ F : H02 L s ≃ₜ Target (L := L) V s hs0, ∀ u n, (F u).val.val n = (e u.val).val n)

theorem REG015Concl_of_inputs (hκ : 0 < κ) (reg010 : Reg010LowOrdersInput (L := L) hκ)
    (reg011 : Reg011HomeomorphismInput (L := L) hκ) (reg013 : Reg013InductionInput (L := L) hκ) :
    REG015Concl (L := L) hκ :=
  QuantumNLS.Reg015Assembly.REG015Input (L := L) hκ reg010 reg011 reg013

/-- The first clause of `REG015Concl` is `Reg015Moments`. -/
theorem reg015Moments_of_concl {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) : Reg015Moments (L := L) hκ := by
  intro s hs u
  have h := (hR s hs).1 u
  exact h.1.trans h.2

/-- The accepted chart as a homeomorphism onto its range. -/
def chartHomeo {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) : L2T L ≃ₜ Set.range C.Φ where
  toFun u := ⟨C.Φ u, u, rfl⟩
  invFun z := C.Ψ z.1
  left_inv u := C.ΨΦ u
  right_inv z := by
    obtain ⟨_, u, rfl⟩ := z
    exact Subtype.ext (by simp [C.ΨΦ])
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_iff_continuousAt.2 fun u => (C.ana_Φ u).continuousAt
  continuous_invFun := by
    exact continuous_iff_continuousAt.2 fun z => ((C.ana_Ψ z.1).continuousAt).comp
      (continuous_subtype_val.continuousAt)

theorem chart_exact {hκ : 0 < κ} (C : ChartFacts (L := L) hκ) : ExactModuli (chartHomeo C) hκ :=
  fun u n => C.mass u n

theorem regHomeo {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (s : ℝ) (hs0 : 0 ≤ s) :
    ∃ F : H02 L s ≃ₜ Target (L := L) (Set.range C.Φ) s hs0, ∀ u n, (F u).val.val n = C.Φ u.val n :=
  (hR s hs0).2.2 _ (chartHomeo C) (chart_exact C)

/-- The restriction `g : h^S → H^S` of the inverse chart, continuous (REG-015 homeomorphism clause). -/
theorem exists_g {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (S : ℝ≥0) :
    ∃ g : h02 L (S : ℝ) → H02 L (S : ℝ), Continuous g ∧
      ∀ z : h02 L (S : ℝ), (g z).val = C.Ψ (toBase (L := L) (S : ℝ) S.2 z) := by
  obtain ⟨F, hF⟩ := regHomeo hR C (S : ℝ) S.2
  let mk : h02 L (S : ℝ) → Target (L := L) (Set.range C.Φ) (S : ℝ) S.2 := fun z =>
    ⟨z, ⟨C.Ψ (toBase (L := L) (S : ℝ) S.2 z), C.ΦΨ _⟩⟩
  refine ⟨fun z => F.symm (mk z), F.symm.continuous.comp (Continuous.subtype_mk continuous_id _), fun z => ?_⟩
  set w := F.symm (mk z) with hw
  have h1 : F w = mk z := F.apply_symm_apply _
  have h2 : ∀ n, C.Φ w.val n = (toBase (L := L) (S : ℝ) S.2 z) n := by
    intro n
    rw [← hF w n, h1]
    exact (toBase_apply (L := L) (S : ℝ) S.2 z n).symm
  have h3 : C.Φ w.val = toBase (L := L) (S : ℝ) S.2 z := lp.ext (funext h2)
  rw [← h3, C.ΨΦ]

/-- Smooth data have rapidly decreasing chart coordinates (REG-015 homeomorphism clause). -/
theorem hinf_smooth {hκ : 0 < κ} (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) (s : ℝ) (hs0 : 0 ≤ s) : MemHs L s (fun n => C.Φ (smoothL2 hf) n) := by
  obtain ⟨F, hF⟩ := regHomeo hR C s hs0
  let v : H02 L s := WField.mk (smoothL2 hf) (memHs_of_smooth hf s)
  have hv : v.val = smoothL2 hf := rfl
  have key : (fun n => C.Φ (smoothL2 hf) n) = (F v).val.val := by
    funext n
    rw [hF v n, hv]
  rw [key]
  exact h02_mem L s (F v).val

/-! ## The order data `F_r = I_{r+1} ∘ Ψ` -/

/-- The printed `q = r + 2`. -/
def qOf (r : ℕ) : ℝ≥0 := (r : ℝ≥0) + 2

/-- The printed `s = 3q + 1`. -/
def SOf (r : ℕ) : ℝ≥0 := 3 * qOf r + 1

theorem qOf_coe (r : ℕ) : (qOf r : ℝ) = (r : ℝ) + 2 := by simp [qOf]

theorem SOf_coe (r : ℕ) : (SOf r : ℝ) = 3 * ((r : ℝ) + 2) + 1 := by simp [SOf, qOf_coe]

theorem q_le (r : ℕ) : (r : ℝ) + 1 ≤ (qOf r : ℝ) := by rw [qOf_coe]; linarith

theorem S_gt (r : ℕ) : (2 + 1) * (qOf r : ℝ) < (SOf r : ℝ) := by rw [SOf_coe, qOf_coe]; linarith

theorem qS_le (r : ℕ) : qOf r ≤ SOf r := by
  rw [← NNReal.coe_le_coe, SOf_coe, qOf_coe]; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

theorem q_pos (r : ℕ) : 0 < qOf r := by
  rw [← NNReal.coe_pos, qOf_coe]; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

variable {hκ : 0 < κ}

/-- The chosen restriction of the inverse chart at the level `S`. -/
def gOf (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (S : ℝ≥0) :
    h02 L (S : ℝ) → H02 L (S : ℝ) := Classical.choose (exists_g hR C S)

theorem gOf_cont (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (S : ℝ≥0) :
    Continuous (gOf hR C S) := (Classical.choose_spec (exists_g hR C S)).1

theorem gOf_val (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (S : ℝ≥0) (z : h02 L (S : ℝ)) :
    (gOf hR C S z).val = C.Ψ (toBase (L := L) (S : ℝ) S.2 z) := (Classical.choose_spec (exists_g hR C S)).2 z

theorem exists_I (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    ∃ I : (fieldScale L).Y (qOf r) → ℝ, ContDiff ℝ 2 I ∧
      (∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hm : MemHsLp L ((qOf r : ℝ≥0) : ℝ) (smoothL2 hf)),
        I ⟨smoothL2 hf, hm⟩ = (charge L κ f (r + 1)).re) ∧
      ContDiff ℝ 2 (fun x : h02 L ((SOf r : ℝ≥0) : ℝ) =>
        I ((fieldScale L).emb (SOf r) (qOf r) (qS_le r) (gOf hR C (SOf r) x))) ∧
      ∀ (u : ℤ → Circle) (z : h02 L ((SOf r : ℝ≥0) : ℝ)),
        I ((fieldScale L).emb (SOf r) (qOf r) (qS_le r) (gOf hR C (SOf r) (rot u z))) =
          I ((fieldScale L).emb (SOf r) (qOf r) (qS_le r) (gOf hR C (SOf r) z)) :=
  Fr_data hκ (reg015Moments_of_concl hR) C r (q_le r) (S_gt r) (qS_le r) (gOf hR C (SOf r))
    (gOf_cont hR C (SOf r)) (gOf_val hR C (SOf r))

/-- The charge functional `I_{r+1}` on `H^q` (chosen). -/
def IOf (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) : (fieldScale L).Y (qOf r) → ℝ :=
  Classical.choose (exists_I hR C r)

/-- `F_r = I_{r+1} ∘ Ψ` on `h^{S_r}`. -/
def Fd (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) : h02 L ((SOf r : ℝ≥0) : ℝ) → ℝ :=
  fun x => IOf hR C r ((fieldScale L).emb (SOf r) (qOf r) (qS_le r) (gOf hR C (SOf r) x))

theorem IOf_contDiff (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    ContDiff ℝ 2 (IOf hR C r) := (Classical.choose_spec (exists_I hR C r)).1

theorem IOf_char (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) (f : ℝ → ℂ)
    (hf : SmoothPeriodic L f) (hm : MemHsLp L ((qOf r : ℝ≥0) : ℝ) (smoothL2 hf)) :
    IOf hR C r ⟨smoothL2 hf, hm⟩ = (charge L κ f (r + 1)).re :=
  (Classical.choose_spec (exists_I hR C r)).2.1 f hf hm

theorem Fd_contDiff (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ) :
    ContDiff ℝ 2 (Fd hR C r) := (Classical.choose_spec (exists_I hR C r)).2.2.1

theorem Fd_inv (hR : REG015Concl (L := L) hκ) (C : ChartFacts (L := L) hκ) (r : ℕ)
    (u : ℤ → Circle) (z : h02 L ((SOf r : ℝ≥0) : ℝ)) : Fd hR C r (rot u z) = Fd hR C r z :=
  (Classical.choose_spec (exists_I hR C r)).2.2.2 u z

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.REG015Concl_of_inputs
#print axioms QuantumNLS.RB7.exists_g
#print axioms QuantumNLS.RB7.hinf_smooth
#print axioms QuantumNLS.RB7.exists_I
#print axioms QuantumNLS.RB7.Fd_inv
