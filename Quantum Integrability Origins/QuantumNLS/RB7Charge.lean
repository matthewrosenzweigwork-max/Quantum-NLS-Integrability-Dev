import Mathlib
import QuantumNLS.RB7Jet
import QuantumNLS.RB7Poly
import QuantumNLS.LossSobolev

/-!
# R-7B122087 `thm:hierarchy`: `I_{r+1}` is a smooth real functional on `H^q` and equals `Re charge` on smooth profiles (own TODO A2)

Printed: "The differential-polynomial recursion makes `I_{r+1}` a smooth real functional on `H^q`" (`q = r + 2`).

Assembly of `RB7Jet` (continuous jets `∂^a u ∈ C(𝕋_L)`, `a + 1 ≤ q`, conjugation, integral) and `RB7Poly` (the DEF-022 recursion as the jet polynomial `jp κ`):

* `chargeFun κ j h : H^q → ℝ`, `u ↦ Re ∫_{𝕋_L} X_{true,0}(u) · jp κ (j+1) (jets of u)` (the real part of `∫ ū v_{j+1}`), for `(j : ℝ) + 1 ≤ q`;
* `chargeFun_contDiff`: `C^∞` (a continuous polynomial in the bounded linear maps `u ↦ ∂^a u`, `u ↦ conj ∂^a u`, followed by the bounded integral);
* `chargeFun_smooth`: for smooth periodic `f` with `smoothL2 f ∈ H^q`, `chargeFun κ j h ⟨smoothL2 f, _⟩ = Re (charge L κ f (j+1))` (DEF-022 `ClassicalCharges.charge`);
* `chargeFun_scale`: the same in the `fieldScale` (`lem:loss` interface) form, with `ContDiff ℝ 2`, exactly the hypotheses `hI`, `hIchar` of `RB7Scale.F_contDiff` / `RB7Invar.F_invariant`.
For `r ≥ 1` the printed `q = r + 2` satisfies `(r + 1 : ℝ) + 1 ≤ q`; the tight requirement of the proof is `q ≥ r + 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate ContDiff NNReal
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.PhysicalTensor
open QuantumNLS.Sobolev QuantumNLS.LossSobolev

variable {L : ℝ} [Fact (0 < L)]

/-- The `ℝ`-linear continuous jet maps `u ↦ ∂^a u` (`b = false`) and `u ↦ conj ∂^a u` (`b = true`). -/
def jetCLM {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (b : Bool) : H02 L q →L[ℝ] C(AddCircle L, ℂ) :=
  if b then cconj.comp ((jet h).restrictScalars ℝ) else (jet h).restrictScalars ℝ

/-- The jets of an `H^q` field, as elements of the algebra `C(𝕋_L, ℂ)` (junk `0` above order `q - 1`). -/
def jetVec {q : ℝ} (u : H02 L q) (i : JetIdx) : C(AddCircle L, ℂ) :=
  if h : (i.2 : ℝ) + 1 ≤ q then jetCLM h i.1 u else 0

theorem contDiff_aeval {q : ℝ} {N : ℕ} (hN : (N : ℝ) + 1 ≤ q) {P : JP} (hP : P ∈ JR N) :
    ContDiff ℝ ∞ (fun u : H02 L q => MvPolynomial.aeval (jetVec u) P) := by
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i.2 : ℝ) + 1 ≤ q := le_trans (by exact_mod_cast Nat.succ_le_succ hi) hN
    simp only [MvPolynomial.aeval_X, jetVec, dif_pos hi']
    exact (jetCLM (L := L) hi' i.1).contDiff
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact contDiff_const
  | add x y hx hy ihx ihy =>
    simp only [map_add]
    exact ihx.add ihy
  | mul x y hx hy ihx ihy =>
    simp only [map_mul]
    exact ihx.mul ihy

theorem aeval_smooth {q : ℝ} {N : ℕ} (hN : (N : ℝ) + 1 ≤ q) {f : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (hm : MemHsLp L q (smoothL2 hf)) {P : JP} (hP : P ∈ JR N) (x : ℝ) :
    MvPolynomial.aeval (jetVec (⟨smoothL2 hf, hm⟩ : H02 L q)) P (x : AddCircle L) = evj f x P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    have hi' : (i.2 : ℝ) + 1 ≤ q := le_trans (by exact_mod_cast Nat.succ_le_succ hi) hN
    rw [MvPolynomial.aeval_X, evj_X]
    simp only [jetVec, dif_pos hi']
    obtain ⟨b, a⟩ := i
    cases b
    · simpa [jetCLM, jetPt] using jet_smooth hi' hf hm x
    · simp only [jetCLM, jetPt, if_true]
      show conj (jet hi' (⟨smoothL2 hf, hm⟩ : H02 L q) (x : AddCircle L)) = _
      rw [jet_smooth hi' hf hm x]
  | algebraMap r =>
    simp only [AlgHom.commutes]
    simp [evj]
  | add y z hy hz ihy ihz =>
    simp only [map_add, ContinuousMap.add_apply, ihy, ihz]
  | mul y z hy hz ihy ihz =>
    simp only [map_mul, ContinuousMap.mul_apply, ihy, ihz]

/-- The jet polynomial of the integrand `ū v_{j+1}`. -/
def chargePoly (κ : ℝ) (j : ℕ) : JP := MvPolynomial.X (true, 0) * jp κ (j + 1)

theorem chargePoly_mem (κ : ℝ) (j : ℕ) : chargePoly κ j ∈ JR j := by
  refine mul_mem (X_mem_JR (by simp)) ?_
  simpa using jp_mem κ (j + 1)

/-- **`I_{j+1}` on `H^q`**: `u ↦ Re ∫_{𝕋_L} ū v_{j+1}` computed from the jets of `u`. -/
def chargeFun (κ : ℝ) (j : ℕ) {q : ℝ} (u : H02 L q) : ℝ :=
  (integralCLM (MvPolynomial.aeval (jetVec u) (chargePoly κ j))).re

theorem chargeFun_contDiff (κ : ℝ) (j : ℕ) {q : ℝ} (hq : (j : ℝ) + 1 ≤ q) :
    ContDiff ℝ ∞ (fun u : H02 L q => chargeFun κ j u) := by
  have h1 := contDiff_aeval (L := L) hq (chargePoly_mem κ j)
  have h2 : ContDiff ℝ ∞ (fun g : C(AddCircle L, ℂ) => (integralCLM g).re) :=
    Complex.reCLM.contDiff.comp ((integralCLM (L := L)).restrictScalars ℝ).contDiff
  exact h2.comp h1

theorem chargeFun_smooth (κ : ℝ) (j : ℕ) {q : ℝ} (hq : (j : ℝ) + 1 ≤ q) {f : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (hm : MemHsLp L q (smoothL2 hf)) :
    chargeFun κ j (⟨smoothL2 hf, hm⟩ : H02 L q) = (charge L κ f (j + 1)).re := by
  unfold chargeFun
  congr 1
  have hcont : Continuous (fun x => conj (f x) * vseq κ f (j + 1) x) := charge_integrand_continuous κ hf (j + 1)
  have hper : Function.Periodic (fun x => conj (f x) * vseq κ f (j + 1) x) L := by
    intro x
    simp only [hf.periodic x, (vseq_regular κ hf (j + 1)).2 x]
  have heq : MvPolynomial.aeval (jetVec (⟨smoothL2 hf, hm⟩ : H02 L q)) (chargePoly κ j) = liftC hcont hper := by
    ext z
    induction z using QuotientAddGroup.induction_on with
    | H x =>
      rw [aeval_smooth hq hf hm (chargePoly_mem κ j) x]
      change _ = liftC hcont hper (x : AddCircle L)
      rw [liftC_coe]
      unfold chargePoly
      rw [map_mul, evj_X, ← vseq_eq_evj κ hf.smooth (j + 1) x]
      simp [jetPt]
  rw [heq, integralCLM_liftC]
  rfl

/-- **The `lem:loss`-interface form**: for `(j : ℝ) + 1 ≤ q` there is `I : H^q → ℝ` (in the DEF-002 `fieldScale`), `C²` (even `C^∞`), equal to `Re I_{j+1}` on smooth periodic
profiles, i.e. the hypotheses `hI`, `hIchar` of `RB7Scale.F_contDiff` and `RB7Invar.F_invariant` (with `I_{r+1} = I_{j+1}`, `j = r`). -/
theorem chargeFun_scale (κ : ℝ) (j : ℕ) {q : ℝ≥0} (hq : (j : ℝ) + 1 ≤ q) :
    ∃ I : (fieldScale L).Y q → ℝ, ContDiff ℝ 2 I ∧
      ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hm : MemHsLp L (q : ℝ) (smoothL2 hf)),
        I ⟨smoothL2 hf, hm⟩ = (charge L κ f (j + 1)).re := by
  refine ⟨fun u => chargeFun κ j (q := (q : ℝ)) u, ?_, ?_⟩
  · exact (chargeFun_contDiff κ j hq).of_le (WithTop.coe_le_coe.2 le_top)
  · intro f hf hm
    exact chargeFun_smooth κ j hq hf hm

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.chargeFun_contDiff
#print axioms QuantumNLS.RB7.chargeFun_smooth
#print axioms QuantumNLS.RB7.chargeFun_scale
