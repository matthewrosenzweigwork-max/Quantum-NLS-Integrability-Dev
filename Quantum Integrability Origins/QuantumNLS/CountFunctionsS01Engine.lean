import QuantumNLS.CountFunctionsS01Class
import QuantumNLS.CountFunctionsS01Sym
import QuantumNLS.CountFunctionsS01Prod

/-!
# CountFunctionsS01Engine: the scaled Dirac bracket on the first-order class

PRINTED SOURCES
* `source-text/chapters/principal_correspondence.tex:44-51` (eq:dirac-main), sha256 `6008c7e6…da56`:
  "For finite expressions made from the Cartesian transfers and `C²` functions of finitely many counts, with classical
   expressions `A,C`,  `sup_{t∈K} ‖(N/i [A_N,C_N] - {A,C}(Φ_t(u))) U_N(t) ψ_N‖ → 0`, `sup_N ‖N[A_N,C_N]‖ < ∞`."
* `source-text/chapters/core/canonical_algebra.tex:40-46`: eq:finite-difference and "Combining this operator-norm
  estimate with the strong Cartesian and continuous-count symbols yields the bracket with `f(a_J)`. Equations
  (eq:exact-algebra) treat two Cartesian generators, and two count functions commute. Repeated use of the commutator
  Leibniz rules proves (eq:dirac-main) for all stated expressions and gives the uniform scaled operator bound."
* `canonical_algebra.tex:54`: "boundedness of the unscaled factors alone would not suffice" (the uniform scaled bound).

The setting (`Setting`) is generic: sector index `Nn`, Bethe basis family and gauge, a preparation family `ψ u t n` over a
parameter set `S × Tb`, and classical points `z u t ∈ ℂ^J`, such that the Cartesian transfers `E^q_{N,ab}`, `a,b∈J`,
have the uniform strong pairs with symbols `z_a z̄_b`.  The R-8362E5EB dynamic input and the R-D2F4CE8F static input
instantiate it (`CountFunctionsS01Dirac`).

PROOF STRUCTURE (the printed argument, by Leibniz induction): `pairOK` (strong pair + norm bound for every expression,
from the generators, `count_pair`, and the telescoping `pair_mul`), `diracLeaf` (two generators: exact algebra; a count
function and a generator: eq:finite-difference and the first-order estimate; two count functions: commute), then
`diracOK` by the commutator Leibniz rule in both slots.  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate
open QuantumNLS Occupation OccupationHilbert BetheCoefficientTransform BetheOccupationGauge
open QuantumNLS.CountFunctionsS01Ops QuantumNLS.CountFunctionsS01Calc QuantumNLS.CountFunctionsS01Poisson
open QuantumNLS.CountFunctionsS01Class QuantumNLS.CountFunctionsS01Sym
open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)

namespace QuantumNLS.CountFunctionsS01Engine

/-! ### Generic calculus of uniform strong symbols -/

section Generic

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
variable {X Θ : Type*} {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N}

theorem strong_add {P Q : ∀ N, H N →L[ℂ] H N} {p q : X → Θ → ℂ}
    (hP : HasUniformStrongT P S Tb ψ p) (hQ : HasUniformStrongT Q S Tb ψ q) :
    HasUniformStrongT (fun N => P N + Q N) S Tb ψ (fun u t => p u t + q u t) := by
  intro ε hε
  filter_upwards [hP (ε / 2) (half_pos hε), hQ (ε / 2) (half_pos hε)] with N h1 h2
  intro u hu t ht
  have e : (P N + Q N - (p u t + q u t) • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) =
      (P N - p u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) +
        (Q N - q u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, add_smul]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (by linarith [h1 u hu t ht, h2 u hu t ht])

theorem strong_smul {P : ∀ N, H N →L[ℂ] H N} {p : X → Θ → ℂ} (c : ℂ)
    (hP : HasUniformStrongT P S Tb ψ p) :
    HasUniformStrongT (fun N => c • P N) S Tb ψ (fun u t => c * p u t) := by
  intro ε hε
  have hc : 0 < ‖c‖ + 1 := by positivity
  filter_upwards [hP (ε / (‖c‖ + 1)) (div_pos hε hc)] with N h1
  intro u hu t ht
  have e : (c • P N - (c * p u t) • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) =
      c • (P N - p u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      smul_sub, smul_smul]
  rw [e, norm_smul]
  have h2 := h1 u hu t ht
  calc ‖c‖ * ‖(P N - p u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖
      ≤ ‖c‖ * (ε / (‖c‖ + 1)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ hc]
        nlinarith [norm_nonneg c]

theorem strong_congr {P : ∀ N, H N →L[ℂ] H N} {p q : X → Θ → ℂ}
    (h : HasUniformStrongT P S Tb ψ p) (e : ∀ u ∈ S, ∀ t ∈ Tb, p u t = q u t) :
    HasUniformStrongT P S Tb ψ q := by
  intro ε hε
  filter_upwards [h ε hε] with N hN
  intro u hu t ht
  rw [← e u hu t ht]
  exact hN u hu t ht

theorem strong_neg {P : ∀ N, H N →L[ℂ] H N} {p : X → Θ → ℂ}
    (hP : HasUniformStrongT P S Tb ψ p) :
    HasUniformStrongT (fun N => -P N) S Tb ψ (fun u t => -p u t) := by
  have h := strong_smul (-1 : ℂ) hP
  have e1 : (fun N => (-1 : ℂ) • P N) = fun N => -P N := by
    funext N; simp
  rw [e1] at h
  exact strong_congr h fun u _ t _ => by simp

theorem strong_zero (p : X → Θ → ℂ) (hp : ∀ u ∈ S, ∀ t ∈ Tb, p u t = 0) :
    HasUniformStrongT (fun N => (0 : H N →L[ℂ] H N)) S Tb ψ p := by
  intro ε hε
  refine Eventually.of_forall fun N u hu t ht => ?_
  simp [hp u hu t ht, hε.le]

/-- `A` is eventually within `ε` of `B` (operator norm), and `B` has a strong symbol: so has `A`. -/
theorem strong_of_close {A B : ∀ N, H N →L[ℂ] H N} {b : X → Θ → ℂ}
    (hB : HasUniformStrongT B S Tb ψ b)
    (hAB : ∀ ε > 0, ∀ᶠ N in atTop, ‖A N - B N‖ ≤ ε)
    (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ ≤ 1) :
    HasUniformStrongT A S Tb ψ b := by
  intro ε hε
  filter_upwards [hB (ε / 2) (half_pos hε), hAB (ε / 2) (half_pos hε), hψ] with N h1 h2 h3
  intro u hu t ht
  have e : (A N - b u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) =
      (A N - B N) (ψ u t N) + (B N - b u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  rw [e]
  have h4 : ‖(A N - B N) (ψ u t N)‖ ≤ ε / 2 :=
    ((A N - B N).le_opNorm _).trans (by
      calc ‖A N - B N‖ * ‖ψ u t N‖ ≤ (ε / 2) * 1 :=
            mul_le_mul h2 (h3 u hu t ht) (norm_nonneg _) (half_pos hε).le
        _ = ε / 2 := mul_one _)
  exact (norm_add_le _ _).trans (by linarith [h1 u hu t ht])

theorem strong_ite {P : ∀ N, H N →L[ℂ] H N} {p : X → Θ → ℂ} (c : Prop) [Decidable c]
    (hP : HasUniformStrongT P S Tb ψ p) :
    HasUniformStrongT (fun N => if c then P N else 0) S Tb ψ (fun u t => if c then p u t else 0) := by
  by_cases h : c
  · simpa [h] using hP
  · simp only [h, if_false]
    exact strong_zero _ (fun _ _ _ _ => rfl)

end Generic


section PairOps

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
variable {X Θ : Type*} {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N}

theorem pair_add {P P' Q Q' : ∀ N, H N →L[ℂ] H N} {p q : X → Θ → ℂ}
    (hP : HasUniformPairT P P' S Tb ψ p) (hQ : HasUniformPairT Q Q' S Tb ψ q) :
    HasUniformPairT (fun N => P N + Q N) (fun N => P' N + Q' N) S Tb ψ (fun u t => p u t + q u t) := by
  refine ⟨strong_add hP.1 hQ.1, strong_congr (strong_add hP.2 hQ.2) fun u _ t _ => ?_⟩
  simp

theorem pair_smul {P P' : ∀ N, H N →L[ℂ] H N} {p : X → Θ → ℂ} (c : ℂ)
    (hP : HasUniformPairT P P' S Tb ψ p) :
    HasUniformPairT (fun N => c • P N) (fun N => conj c • P' N) S Tb ψ (fun u t => c * p u t) := by
  refine ⟨strong_smul c hP.1, strong_congr (strong_smul (conj c) hP.2) fun u _ t _ => ?_⟩
  simp

end PairOps

/-- A bound on the cube for a continuous count function (a chosen one). -/
def cntBnd' (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) : ℝ := by
  classical
  exact if h : ContinuousOn f (cube J) then (BddOn.of_continuousOn h).choose else 0

lemma cntBnd_spec' {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (h : ContinuousOn f (cube J)) :
    0 ≤ cntBnd' J f ∧ ∀ x ∈ cube J, ‖f x‖ ≤ cntBnd' J f := by
  classical
  unfold cntBnd'
  rw [dif_pos h]
  exact (BddOn.of_continuousOn h).choose_spec

/-! ### The setting -/

/-- A setting in which the Cartesian transfers `E^q_{N,ab}` (`a,b ∈ J`) have uniform strong pairs with symbols
`z_a z̄_b` on the parameter set `S × Tb`, for the unit preparations `ψ`. -/
structure Setting (L : ℝ) [Fact (0 < L)] (X Θ : Type*) (J : Finset ℤ) where
  Nn : ℕ → ℕ
  hN : ∀ n, 0 < Nn n
  hNtop : Tendsto Nn atTop atTop
  b : ∀ n, BetheBasis L (Nn n)
  g : Gauge
  S : Set X
  Tb : Set Θ
  ψ : X → Θ → ∀ n, HN L (Nn n)
  z : X → Θ → CPt J
  hψ : ∀ᶠ n in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t n‖ = 1
  hgen : ∀ a c : ↥J, HasUniformPairT (H := fun n => HN L (Nn n))
    (fun n => CartesianOccupationTransfer.physical (b n) g (a : ℤ) (c : ℤ))
    (fun n => (CartesianOccupationTransfer.physical (b n) g (a : ℤ) (c : ℤ)).adjoint)
    S Tb ψ (fun u t => z u t a * conj (z u t c))

section Setting

variable {L : ℝ} [Fact (0 < L)] {X Θ : Type*} {J : Finset ℤ} (σ : Setting L X Θ J)

/-- The operator of an adjoint-free expression at sector `n`. -/
abbrev Setting.op0 (A : Expr0 J) (n : ℕ) : HN L (σ.Nn n) →L[ℂ] HN L (σ.Nn n) := A.op (σ.b n) σ.g

/-- The scale `N/i = -i N`. -/
def Setting.sc (n : ℕ) : ℂ := -Complex.I * (σ.Nn n : ℂ)

lemma mul_conj_eq' (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma Setting.hψ1 : ∀ᶠ n in atTop, ∀ u ∈ σ.S, ∀ t ∈ σ.Tb, ‖σ.ψ u t n‖ ≤ 1 :=
  σ.hψ.mono fun n h u hu t ht => (h u hu t ht).le

lemma Setting.hcube : ∀ u ∈ σ.S, ∀ t ∈ σ.Tb, apt (σ.z u t) ∈ cube J := by
  intro u hu t ht j
  refine ⟨sq_nonneg _, ?_⟩
  have h := CountFunctionsS01Prod.symbol_le_of_strong (H := fun n => HN L (σ.Nn n))
    (A := fun n => CartesianOccupationTransfer.physical (σ.b n) σ.g (j : ℤ) (j : ℤ)) (C := 1)
    (Eventually.of_forall fun n => CartesianOccupationTransfer.physical_norm_le _ _ _ _) σ.hψ
    (σ.hgen j j).1 u hu t ht
  rw [norm_mul, Complex.norm_conj, ← sq] at h
  exact h

end Setting


section PairOK

variable {L : ℝ} [Fact (0 < L)] {X Θ : Type*} {J : Finset ℤ} (σ : Setting L X Θ J)

/-- Uniform operator bound and strong-symbol pair of an expression. -/
def PairOK (A : Expr0 J) : Prop :=
  (∃ K : ℝ, 0 ≤ K ∧ ∀ n, ‖σ.op0 A n‖ ≤ K) ∧
    HasUniformPairT (H := fun n => HN L (σ.Nn n)) (fun n => σ.op0 A n) (fun n => (σ.op0 A n).adjoint)
      σ.S σ.Tb σ.ψ (fun u t => A.cl (σ.z u t))

theorem pairOK_count {f : (↥J → ℝ) → ℂ} (hf : ContinuousOn f (cube J)) :
    HasUniformPairT (H := fun n => HN L (σ.Nn n)) (fun n => countOp (σ.b n) σ.g J f)
      (fun n => (countOp (σ.b n) σ.g J f).adjoint) σ.S σ.Tb σ.ψ (fun u t => cntF f (σ.z u t)) := by
  have hB : ∀ j : ↥J, HasUniformStrongT (H := fun n => HN L (σ.Nn n))
      (fun n => CartesianOccupationTransfer.physical (σ.b n) σ.g (j : ℤ) (j : ℤ)) σ.S σ.Tb σ.ψ
      (fun u t => ((apt (σ.z u t) j : ℝ) : ℂ)) := by
    intro j
    refine strong_congr (σ.hgen j j).1 fun u _ t _ => ?_
    exact (mul_conj_eq' _)
  exact count_pair σ.Nn σ.b σ.g J hf σ.S σ.Tb σ.ψ (fun u t => apt (σ.z u t)) σ.hcube σ.hψ1 hB

theorem pairOK : ∀ A : Expr0 J, PairOK σ A
  | .gen a c => by
      refine ⟨⟨1, zero_le_one, fun n => CartesianOccupationTransfer.physical_norm_le _ _ _ _⟩, ?_⟩
      exact σ.hgen a c
  | .fn f hf => by
      have hb := cntBnd_spec' hf.continuousOn
      refine ⟨⟨_, hb.1, fun n => countOp_norm_le _ _ J hb.1 hb.2⟩, ?_⟩
      exact pairOK_count σ hf.continuousOn
  | .add A B => by
      obtain ⟨⟨KA, hKA, hA⟩, pA⟩ := pairOK A
      obtain ⟨⟨KB, hKB, hB⟩, pB⟩ := pairOK B
      refine ⟨⟨KA + KB, add_nonneg hKA hKB, fun n => ?_⟩, ?_⟩
      · have h1 := norm_add_le (σ.op0 A n) (σ.op0 B n)
        have h2 : ‖σ.op0 (.add A B) n‖ = ‖σ.op0 A n + σ.op0 B n‖ := rfl
        linarith [hA n, hB n]
      · have h := pair_add pA pB
        have e : (fun n => (σ.op0 A n).adjoint + (σ.op0 B n).adjoint) =
            fun n => (σ.op0 (.add A B) n).adjoint := by
          funext n
          exact (map_add (ContinuousLinearMap.adjoint) _ _).symm
        rw [e] at h
        exact h
  | .mul A B => by
      obtain ⟨⟨KA, hKA, hA⟩, pA⟩ := pairOK A
      obtain ⟨⟨KB, hKB, hB⟩, pB⟩ := pairOK B
      refine ⟨⟨KA * KB, mul_nonneg hKA hKB, fun n => ?_⟩, ?_⟩
      · have h1 : ‖σ.op0 A n * σ.op0 B n‖ ≤ ‖σ.op0 A n‖ * ‖σ.op0 B n‖ :=
          ContinuousLinearMap.opNorm_comp_le (σ.op0 A n) (σ.op0 B n)
        have h2 : ‖σ.op0 (.mul A B) n‖ = ‖σ.op0 A n * σ.op0 B n‖ := rfl
        have h3 : ‖σ.op0 A n‖ * ‖σ.op0 B n‖ ≤ KA * KB :=
          mul_le_mul (hA n) (hB n) (norm_nonneg (σ.op0 B n)) hKA
        linarith
      · set C : ℝ := max KA KB with hC
        have hsA : ∀ u ∈ σ.S, ∀ t ∈ σ.Tb, ‖A.cl (σ.z u t)‖ ≤ C := fun u hu t ht =>
          (CountFunctionsS01Prod.symbol_le_of_strong (A := fun n => σ.op0 A n) (Eventually.of_forall hA) σ.hψ
            pA.1 u hu t ht).trans (le_max_left _ _)
        have hsB : ∀ u ∈ σ.S, ∀ t ∈ σ.Tb, ‖B.cl (σ.z u t)‖ ≤ C := fun u hu t ht =>
          (CountFunctionsS01Prod.symbol_le_of_strong (A := fun n => σ.op0 B n) (Eventually.of_forall hB) σ.hψ
            pB.1 u hu t ht).trans (le_max_right _ _)
        have h := FullWickH4.pair_mul (C := C) (K := C)
          (Eventually.of_forall fun n => (hA n).trans (le_max_left _ _))
          (Eventually.of_forall fun n => by
            rw [ContinuousLinearMap.adjoint.norm_map]
            exact (hB n).trans (le_max_right _ _)) hsA hsB pA pB
        have e : (fun n => (σ.op0 B n).adjoint * (σ.op0 A n).adjoint) =
            fun n => (σ.op0 (.mul A B) n).adjoint := by
          funext n
          exact (ContinuousLinearMap.adjoint_comp _ _).symm
        rw [e] at h
        exact h
  | .smul c A => by
      obtain ⟨⟨KA, hKA, hA⟩, pA⟩ := pairOK A
      refine ⟨⟨‖c‖ * KA, mul_nonneg (norm_nonneg _) hKA, fun n => ?_⟩, ?_⟩
      · have h1 : ‖c • σ.op0 A n‖ ≤ ‖c‖ * ‖σ.op0 A n‖ := ContinuousLinearMap.opNorm_smul_le c (σ.op0 A n)
        have h2 : ‖σ.op0 (.smul c A) n‖ = ‖c • σ.op0 A n‖ := rfl
        have h3 : ‖c‖ * ‖σ.op0 A n‖ ≤ ‖c‖ * KA := mul_le_mul_of_nonneg_left (hA n) (norm_nonneg c)
        linarith
      · have h := pair_smul c pA
        have e : (fun n => conj c • (σ.op0 A n).adjoint) = fun n => (σ.op0 (.smul c A) n).adjoint := by
          funext n
          exact (ContinuousLinearMap.adjoint.map_smulₛₗ c (σ.op0 A n)).symm
        rw [e] at h
        exact h

end PairOK


section Dirac

variable {L : ℝ} [Fact (0 < L)] {X Θ : Type*} {J : Finset ℤ} (σ : Setting L X Θ J)

/-- The scaled commutator `(N/i)[A_N, C_N]` at sector `n` (`N/i = -iN`). -/
def Setting.dirOp (A C : Expr0 J) (n : ℕ) : HN L (σ.Nn n) →L[ℂ] HN L (σ.Nn n) :=
  σ.sc n • (σ.op0 A n * σ.op0 C n - σ.op0 C n * σ.op0 A n)

/-- The Dirac clause for the pair `(A, C)`: the scaled commutator is uniformly bounded in operator norm and has the
uniform strong symbol `{A,C}` (Poisson bracket of the classical expressions at `z u t`). -/
def DiracOK (A C : Expr0 J) : Prop :=
  (∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖σ.dirOp A C n‖ ≤ M) ∧
    HasUniformStrongT (H := fun n => HN L (σ.Nn n)) (fun n => σ.dirOp A C n) σ.S σ.Tb σ.ψ
      (fun u t => poisson A.cl C.cl (σ.z u t))

lemma smul_zero_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) :
    c • (0 : E →L[ℂ] E) = 0 := ContinuousLinearMap.ext fun v => by simp

lemma smul_mul_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (f g : E →L[ℂ] E) :
    (c • f) * g = c • (f * g) := ContinuousLinearMap.smul_comp c f g

lemma mul_smul_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ) (f g : E →L[ℂ] E) :
    f * (c • g) = c • (f * g) := ContinuousLinearMap.comp_smul f c g

lemma dirOp_swap (A C : Expr0 J) (n : ℕ) : σ.dirOp C A n = -σ.dirOp A C n := by
  unfold Setting.dirOp
  have : σ.op0 C n * σ.op0 A n - σ.op0 A n * σ.op0 C n =
      -(σ.op0 A n * σ.op0 C n - σ.op0 C n * σ.op0 A n) := (neg_sub _ _).symm
  rw [this]
  exact smul_neg _ _

theorem DiracOK.neg {A C : Expr0 J} (h : DiracOK σ A C) : DiracOK σ C A := by
  obtain ⟨⟨M, hM, hb⟩, hs⟩ := h
  refine ⟨⟨M, hM, fun n => ?_⟩, ?_⟩
  · rw [dirOp_swap]
    have h := norm_neg (σ.dirOp A C n)
    linarith [hb n]
  · have e : (fun n => σ.dirOp C A n) = fun n => -σ.dirOp A C n := funext fun n => dirOp_swap σ A C n
    rw [e]
    refine strong_congr (strong_neg hs) fun u _ t _ => ?_
    rw [poisson_antisymm C.cl A.cl]

theorem DiracOK.add {A B C : Expr0 J} (hA : DiracOK σ A C) (hB : DiracOK σ B C) :
    DiracOK σ (.add A B) C := by
  obtain ⟨⟨MA, hMA, hbA⟩, hsA⟩ := hA
  obtain ⟨⟨MB, hMB, hbB⟩, hsB⟩ := hB
  have e : ∀ n, σ.dirOp (.add A B) C n = σ.dirOp A C n + σ.dirOp B C n := by
    intro n
    simp only [Setting.dirOp, Expr0.op, Setting.op0, add_mul, mul_add, smul_add, smul_sub]
    abel
  refine ⟨⟨MA + MB, add_nonneg hMA hMB, fun n => ?_⟩, ?_⟩
  · rw [e]
    have := norm_add_le (σ.dirOp A C n) (σ.dirOp B C n)
    linarith [hbA n, hbB n]
  · have e' : (fun n => σ.dirOp (.add A B) C n) = fun n => σ.dirOp A C n + σ.dirOp B C n :=
      funext e
    rw [e']
    refine strong_congr (strong_add hsA hsB) fun u hu t ht => ?_
    have hz := σ.hcube u hu t ht
    simp only [Expr0.cl]
    rw [poisson_add_left (A.differentiableAt_cl _ hz) (B.differentiableAt_cl _ hz)]

theorem DiracOK.smul {A C : Expr0 J} (c : ℂ) (hA : DiracOK σ A C) : DiracOK σ (.smul c A) C := by
  obtain ⟨⟨MA, hMA, hbA⟩, hsA⟩ := hA
  have e : ∀ n, σ.dirOp (.smul c A) C n = c • σ.dirOp A C n := by
    intro n
    simp only [Setting.dirOp, Expr0.op, Setting.op0, smul_mul_clm, mul_smul_clm]
    simp only [smul_sub, smul_smul]
    rw [mul_comm c (σ.sc n)]
  refine ⟨⟨‖c‖ * MA, mul_nonneg (norm_nonneg _) hMA, fun n => ?_⟩, ?_⟩
  · rw [e]
    have h1 : ‖c • σ.dirOp A C n‖ ≤ ‖c‖ * ‖σ.dirOp A C n‖ :=
      ContinuousLinearMap.opNorm_smul_le c (σ.dirOp A C n)
    have h2 := mul_le_mul_of_nonneg_left (hbA n) (norm_nonneg c)
    linarith
  · have e' : (fun n => σ.dirOp (.smul c A) C n) = fun n => c • σ.dirOp A C n := funext e
    rw [e']
    refine strong_congr (strong_smul c hsA) fun u hu t ht => ?_
    have hz := σ.hcube u hu t ht
    simp only [Expr0.cl]
    rw [poisson_const_mul_left (A.differentiableAt_cl _ hz) c]

theorem DiracOK.mul {A B C : Expr0 J} (pA : PairOK σ A) (pB : PairOK σ B) (hA : DiracOK σ A C)
    (hB : DiracOK σ B C) : DiracOK σ (.mul A B) C := by
  obtain ⟨⟨KA, hKA, hnA⟩, psA⟩ := pA
  obtain ⟨⟨KB, hKB, hnB⟩, psB⟩ := pB
  obtain ⟨⟨MA, hMA, hbA⟩, hsA⟩ := hA
  obtain ⟨⟨MB, hMB, hbB⟩, hsB⟩ := hB
  have e : ∀ n, σ.dirOp (.mul A B) C n =
      σ.op0 A n * σ.dirOp B C n + σ.dirOp A C n * σ.op0 B n := by
    intro n
    simp only [Setting.dirOp, Expr0.op, Setting.op0]
    rw [mul_smul_clm, smul_mul_clm]
    have hX : σ.op0 A n * σ.op0 B n * σ.op0 C n - σ.op0 C n * (σ.op0 A n * σ.op0 B n) =
        σ.op0 A n * (σ.op0 B n * σ.op0 C n - σ.op0 C n * σ.op0 B n) +
          (σ.op0 A n * σ.op0 C n - σ.op0 C n * σ.op0 A n) * σ.op0 B n := by
          simp only [mul_sub, sub_mul, mul_assoc]
          abel
    rw [hX, smul_add]
  refine ⟨⟨KA * MB + MA * KB, by positivity, fun n => ?_⟩, ?_⟩
  · rw [e]
    have h1 := norm_add_le (σ.op0 A n * σ.dirOp B C n) (σ.dirOp A C n * σ.op0 B n)
    have h2 : ‖σ.op0 A n * σ.dirOp B C n‖ ≤ ‖σ.op0 A n‖ * ‖σ.dirOp B C n‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h3 : ‖σ.dirOp A C n * σ.op0 B n‖ ≤ ‖σ.dirOp A C n‖ * ‖σ.op0 B n‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h4 := mul_le_mul (hnA n) (hbB n) (norm_nonneg (σ.dirOp B C n)) hKA
    have h5 := mul_le_mul (hbA n) (hnB n) (norm_nonneg (σ.op0 B n)) hMA
    linarith
  · have e' : (fun n => σ.dirOp (.mul A B) C n) =
        fun n => σ.op0 A n * σ.dirOp B C n + σ.dirOp A C n * σ.op0 B n := funext e
    rw [e']
    -- symbol bounds
    have hqB : ∀ u ∈ σ.S, ∀ t ∈ σ.Tb, ‖poisson B.cl C.cl (σ.z u t)‖ ≤ MB := fun u hu t ht =>
      CountFunctionsS01Prod.symbol_le_of_strong (A := fun n => σ.dirOp B C n) (Eventually.of_forall hbB)
        σ.hψ hsB u hu t ht
    have hqA : ∀ u ∈ σ.S, ∀ t ∈ σ.Tb, ‖B.cl (σ.z u t)‖ ≤ KB := fun u hu t ht =>
      CountFunctionsS01Prod.symbol_le_of_strong (A := fun n => σ.op0 B n) (Eventually.of_forall hnB)
        σ.hψ psB.1 u hu t ht
    have t1 := FullWickH4.uniform_mul (P := fun n => σ.op0 A n) (Q := fun n => σ.dirOp B C n)
      (p := fun u t => A.cl (σ.z u t)) (q := fun u t => poisson B.cl C.cl (σ.z u t))
      (c := fun u t => A.cl (σ.z u t) * poisson B.cl C.cl (σ.z u t)) (C := KA) (K := MB)
      (Eventually.of_forall hnA) hqB psA.1 hsB (fun u t => rfl)
    have t2 := FullWickH4.uniform_mul (P := fun n => σ.dirOp A C n) (Q := fun n => σ.op0 B n)
      (p := fun u t => poisson A.cl C.cl (σ.z u t)) (q := fun u t => B.cl (σ.z u t))
      (c := fun u t => poisson A.cl C.cl (σ.z u t) * B.cl (σ.z u t)) (C := MA) (K := KB)
      (Eventually.of_forall hbA) hqA hsA psB.1 (fun u t => rfl)
    refine strong_congr (strong_add t1 t2) fun u hu t ht => ?_
    have hz := σ.hcube u hu t ht
    simp only [Expr0.cl]
    rw [poisson_mul_left (A.differentiableAt_cl _ hz) (B.differentiableAt_cl _ hz)]
    ring

end Dirac


section Leaves

variable {L : ℝ} [Fact (0 < L)] {X Θ : Type*} {J : Finset ℤ} (σ : Setting L X Θ J)

lemma ite_smul_one {E : Type*} [AddCommGroup E] [Module ℂ E] (p : Prop) [Decidable p] (x : E) :
    (if p then (1 : ℂ) else 0) • x = if p then x else 0 := by
  split_ifs <;> simp

lemma aux_comm {E : Type*} [AddCommGroup E] [Module ℂ E] (N : ℂ) (hN : N ≠ 0) (p q : Prop) [Decidable p]
    [Decidable q] (X Y : E) :
    (-Complex.I * N) • (N⁻¹ • ((if p then (1 : ℂ) else 0) • X - (if q then (1 : ℂ) else 0) • Y)) =
      (-Complex.I) • ((if p then X else 0) + -(if q then Y else 0)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, smul_smul, mul_assoc, hN, sub_eq_add_neg, smul_add]

lemma norm_ite_le {E : Type*} [NormedAddCommGroup E] (p : Prop) [Decidable p] (x : E) (hx : ‖x‖ ≤ 1) :
    ‖if p then x else 0‖ ≤ 1 := by
  split_ifs
  · exact hx
  · simp

lemma norm_neg_ite_le {E : Type*} [NormedAddCommGroup E] (p : Prop) [Decidable p] (x : E) (hx : ‖x‖ ≤ 1) :
    ‖-(if p then x else 0)‖ ≤ 1 := by
  rw [norm_neg]
  exact norm_ite_le p x hx

/-- **Two generators** (exact algebra, `canonical_algebra.tex:16-17`, eq:exact-algebra): the scaled commutator of two
Cartesian transfers is exactly `-i(δ_ae E_dc - δ_cd E_ae)`. -/
theorem dirOp_gen_gen (a c d e : ↥J) (n : ℕ) :
    σ.dirOp (.gen a c) (.gen d e) n =
      (-Complex.I) • ((if (a : ℤ) = (e : ℤ) then CartesianOccupationTransfer.physical (σ.b n) σ.g (d : ℤ) (c : ℤ)
          else 0) +
        -(if (c : ℤ) = (d : ℤ) then CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (e : ℤ) else 0)) := by
  unfold Setting.dirOp Setting.sc
  simp only [Setting.op0, Expr0.op]
  rw [physical_comm (σ.hN n) (σ.b n) σ.g (a : ℤ) (c : ℤ) (d : ℤ) (e : ℤ)]
  have hN : (σ.Nn n : ℂ) ≠ 0 := by exact_mod_cast (σ.hN n).ne'
  exact aux_comm _ hN _ _ _ _

theorem diracLeaf_gen_gen (a c d e : ↥J) : DiracOK σ (.gen a c) (.gen d e) := by
  have hdir := dirOp_gen_gen σ a c d e
  refine ⟨⟨2, by norm_num, fun n => ?_⟩, ?_⟩
  · rw [hdir n]
    have h1 : ‖(-Complex.I) • ((if (a : ℤ) = (e : ℤ) then
        CartesianOccupationTransfer.physical (σ.b n) σ.g (d : ℤ) (c : ℤ) else 0) +
        -(if (c : ℤ) = (d : ℤ) then CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (e : ℤ)
          else 0))‖ ≤ ‖(-Complex.I)‖ * ‖(if (a : ℤ) = (e : ℤ) then
        CartesianOccupationTransfer.physical (σ.b n) σ.g (d : ℤ) (c : ℤ) else 0) +
        -(if (c : ℤ) = (d : ℤ) then CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (e : ℤ)
          else 0)‖ := ContinuousLinearMap.opNorm_smul_le _ _
    have h2 := norm_add_le (if (a : ℤ) = (e : ℤ) then
        CartesianOccupationTransfer.physical (σ.b n) σ.g (d : ℤ) (c : ℤ) else 0)
      (-(if (c : ℤ) = (d : ℤ) then CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (e : ℤ) else 0))
    have h3 : ‖(if (a : ℤ) = (e : ℤ) then
        CartesianOccupationTransfer.physical (σ.b n) σ.g (d : ℤ) (c : ℤ) else 0)‖ ≤ 1 :=
      norm_ite_le (E := HN L (σ.Nn n) →L[ℂ] HN L (σ.Nn n)) _ _ (CartesianOccupationTransfer.physical_norm_le _ _ _ _)
    have h4 : ‖-(if (c : ℤ) = (d : ℤ) then
        CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (e : ℤ) else 0)‖ ≤ 1 :=
      norm_neg_ite_le (E := HN L (σ.Nn n) →L[ℂ] HN L (σ.Nn n)) _ _ (CartesianOccupationTransfer.physical_norm_le _ _ _ _)
    have h5 : ‖(-Complex.I)‖ = 1 := by simp
    rw [h5] at h1
    linarith
  · have e1 : (fun n => σ.dirOp (.gen a c) (.gen d e) n) = fun n => (-Complex.I) • ((if (a : ℤ) = (e : ℤ) then
        CartesianOccupationTransfer.physical (σ.b n) σ.g (d : ℤ) (c : ℤ) else 0) +
        -(if (c : ℤ) = (d : ℤ) then CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (e : ℤ)
          else 0)) := funext hdir
    rw [e1]
    have hx := strong_ite ((a : ℤ) = (e : ℤ)) (σ.hgen d c).1
    have hy := strong_neg (strong_ite ((c : ℤ) = (d : ℤ)) (σ.hgen a e).1)
    refine strong_congr (strong_smul (-Complex.I) (strong_add hx hy)) fun u hu t ht => ?_
    simp only [Subtype.coe_inj, Expr0.cl, poisson_genF_genF, genF]
    by_cases h1 : a = e <;> by_cases h2 : c = d <;> simp [h1, h2] <;> ring



/-! #### A count function against a generator: eq:finite-difference and the first-order estimate -/

lemma fdiffCoef_norm_le {N : ℕ} {f : (↥J → ℝ) → ℂ} {M : ℝ} (hM : 0 ≤ M) (hbd : ∀ x ∈ cube J, ‖f x‖ ≤ M)
    (a b : ↥J) (m : Arr N) : ‖fdiffCoef N J f a b m‖ ≤ 2 * M := by
  unfold fdiffCoef
  split_ifs with hd
  · have h1 := hbd _ (pt_mem_cube J m.2)
    have h2 : f (pt J N m.1 + (N : ℝ)⁻¹ • hvec J a b) = f (pt J N (shift (a : ℤ) (b : ℤ) m.1)) := by
      rw [pt_shift J N a b hd]
    rw [h2]
    have h3 := hbd _ (pt_mem_cube J (isArray_shift (a := (a : ℤ)) (b := (b : ℤ)) m.2 hd))
    calc ‖f (pt J N (shift (a : ℤ) (b : ℤ) m.1)) - f (pt J N m.1)‖
        ≤ ‖f (pt J N (shift (a : ℤ) (b : ℤ) m.1))‖ + ‖f (pt J N m.1)‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith
  · simp; positivity

lemma fdiffOp_norm_le {N : ℕ} (b : BetheBasis L N) (g : Gauge) {f : (↥J → ℝ) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ x ∈ cube J, ‖f x‖ ≤ M) (a c : ↥J) : ‖fdiffOp b g J f a c‖ ≤ 2 * M :=
  (conjOp_norm_le b g _).trans (dg_norm_le (by positivity) (fdiffCoef_norm_le hM hbd a c))

/-- The scaled finite difference of the gauged operators converges in operator norm after `E^q_{ab}`. -/
theorem fd_close_phys {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) (a c : ↥J) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (N : ℕ) (b : BetheBasis L N) (g : Gauge), N₀ ≤ N → 0 < N →
      ‖(N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * fdiffOp b g J f a c) -
          CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c)‖ ≤ ε := by
  obtain ⟨N₀, h⟩ := fd_scaled_close_H hf a c hε
  refine ⟨N₀, fun N b g hN hpos => ?_⟩
  have e : (N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * fdiffOp b g J f a c) -
      CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c) =
      conjOp b g ((N : ℂ) • (E N (a : ℤ) (c : ℤ) * dg (fdiffCoef N J f a c)) -
        E N (a : ℤ) (c : ℤ) * cntH N J (dirDeriv J f a c)) := by
    simp only [physical_eq_conjOp, fdiffOp, countOp, conjOp_mul, conjOp_smul, conjOp_sub]
  rw [e]
  exact (conjOp_norm_le b g _).trans (h N hN hpos)

/-- The scaled commutator of a count function with a generator is bounded uniformly in `N ≥ 1`. -/
theorem fd_bound_phys {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) (a c : ↥J) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (b : BetheBasis L N) (g : Gauge), 0 < N →
      ‖(N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * fdiffOp b g J f a c)‖ ≤ M := by
  obtain ⟨N₀, h1⟩ := fd_close_phys (L := L) hf a c one_pos
  have hcf := cntBnd_spec' hf.continuousOn
  have hcd := cntBnd_spec' (hf.dirDeriv_continuousOn a c)
  refine ⟨max ((N₀ : ℝ) * (2 * cntBnd' J f)) (1 + cntBnd' J (dirDeriv J f a c)),
    le_max_of_le_right (by linarith [hcd.1]), ?_⟩
  intro N b g hN
  by_cases hge : N₀ ≤ N
  · have h2 := h1 N b g hge hN
    have h3 : ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c)‖ ≤
        cntBnd' J (dirDeriv J f a c) := by
      have h4 : ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c)‖ ≤
          ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ)‖ * ‖countOp b g J (dirDeriv J f a c)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      have h5 := CartesianOccupationTransfer.physical_norm_le b g (a : ℤ) (c : ℤ)
      have h6 := countOp_norm_le b g J hcd.1 hcd.2
      have h7 : ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ)‖ *
          ‖countOp b g J (dirDeriv J f a c)‖ ≤ 1 * cntBnd' J (dirDeriv J f a c) :=
        mul_le_mul h5 h6 (norm_nonneg (countOp b g J (dirDeriv J f a c))) zero_le_one
      linarith
    have h8 := norm_sub_le ((N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) *
        fdiffOp b g J f a c))
      (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c))
    have h9 : ‖(N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * fdiffOp b g J f a c)‖ ≤
        ‖(N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * fdiffOp b g J f a c) -
          CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c)‖ +
        ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c)‖ := by
      have := norm_add_le ((N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) *
          fdiffOp b g J f a c) - CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) *
            countOp b g J (dirDeriv J f a c))
        (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * countOp b g J (dirDeriv J f a c))
      simpa using this
    exact (le_max_right _ _).trans' (by linarith)
  · have hlt : N < N₀ := not_le.1 hge
    have h1' : ‖(N : ℂ) • (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) *
        fdiffOp b g J f a c)‖ ≤ ‖(N : ℂ)‖ * ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) *
          fdiffOp b g J f a c‖ := ContinuousLinearMap.opNorm_smul_le _ _
    have h2' : ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) * fdiffOp b g J f a c‖ ≤
        ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ)‖ * ‖fdiffOp b g J f a c‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have h3' := CartesianOccupationTransfer.physical_norm_le b g (a : ℤ) (c : ℤ)
    have h4' := fdiffOp_norm_le b g hcf.1 hcf.2 a c
    have h5' : ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ)‖ * ‖fdiffOp b g J f a c‖ ≤
        1 * (2 * cntBnd' J f) := mul_le_mul h3' h4' (norm_nonneg (fdiffOp b g J f a c)) zero_le_one
    have h6' : ‖(N : ℂ)‖ ≤ (N₀ : ℝ) := by
      rw [Complex.norm_natCast]; exact_mod_cast hlt.le
    have h7' : ‖(N : ℂ)‖ * ‖CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) *
        fdiffOp b g J f a c‖ ≤ (N₀ : ℝ) * (2 * cntBnd' J f) :=
      mul_le_mul h6' (h2'.trans (by linarith)) (norm_nonneg (CartesianOccupationTransfer.physical b g (a : ℤ) (c : ℤ) *
        fdiffOp b g J f a c)) (Nat.cast_nonneg _)
    exact (le_max_left _ _).trans' (h1'.trans h7')

theorem dirOp_fn_gen {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) (a c : ↥J) (n : ℕ) :
    σ.dirOp (.fn f hf) (.gen a c) n =
      (-Complex.I) • ((σ.Nn n : ℂ) •
        (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) * fdiffOp (σ.b n) σ.g J f a c)) := by
  unfold Setting.dirOp Setting.sc
  simp only [Setting.op0, Expr0.op]
  rw [countOp_comm_E (σ.b n) σ.g J (BddOn.of_continuousOn hf.continuousOn) a c, smul_smul]

theorem diracLeaf_fn_gen {f : (↥J → ℝ) → ℂ} (hf : C2Near J f) (a c : ↥J) :
    DiracOK σ (.fn f hf) (.gen a c) := by
  have hdir := dirOp_fn_gen σ hf a c
  obtain ⟨M, hM, hbd⟩ := fd_bound_phys (L := L) hf a c
  have hcd := cntBnd_spec' (hf.dirDeriv_continuousOn a c)
  refine ⟨⟨M, hM, fun n => ?_⟩, ?_⟩
  · rw [hdir n]
    have h1 : ‖(-Complex.I) • ((σ.Nn n : ℂ) • (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) *
        fdiffOp (σ.b n) σ.g J f a c))‖ ≤ ‖(-Complex.I)‖ * ‖(σ.Nn n : ℂ) •
          (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) * fdiffOp (σ.b n) σ.g J f a c)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    have h5 : ‖(-Complex.I)‖ = 1 := by simp
    rw [h5, one_mul] at h1
    exact h1.trans (hbd (σ.Nn n) (σ.b n) σ.g (σ.hN n))
  · -- the approximant
    set Q : ∀ n, HN L (σ.Nn n) →L[ℂ] HN L (σ.Nn n) := fun n => countOp (σ.b n) σ.g J (dirDeriv J f a c) with hQ
    have pQ := pairOK_count σ (hf.dirDeriv_continuousOn a c)
    have hqb : ∀ u ∈ σ.S, ∀ t ∈ σ.Tb, ‖cntF (dirDeriv J f a c) (σ.z u t)‖ ≤ cntBnd' J (dirDeriv J f a c) :=
      fun u hu t ht => CountFunctionsS01Prod.symbol_le_of_strong (A := Q)
        (Eventually.of_forall fun n => countOp_norm_le _ _ J hcd.1 hcd.2) σ.hψ pQ.1 u hu t ht
    have hprod := FullWickH4.uniform_mul (P := fun n => CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ))
      (Q := Q) (p := fun u t => σ.z u t a * conj (σ.z u t c)) (q := fun u t => cntF (dirDeriv J f a c) (σ.z u t))
      (c := fun u t => (σ.z u t a * conj (σ.z u t c)) * cntF (dirDeriv J f a c) (σ.z u t))
      (C := 1) (K := cntBnd' J (dirDeriv J f a c))
      (Eventually.of_forall fun n => CartesianOccupationTransfer.physical_norm_le _ _ _ _) hqb
      (σ.hgen a c).1 pQ.1 (fun u t => rfl)
    have hB := strong_smul (-Complex.I) hprod
    refine strong_congr (strong_of_close hB ?_ σ.hψ1) fun u hu t ht => ?_
    · intro ε hε
      obtain ⟨N₀, h⟩ := fd_close_phys (L := L) hf a c hε
      filter_upwards [σ.hNtop.eventually_ge_atTop N₀] with n hn
      have e : σ.dirOp (.fn f hf) (.gen a c) n -
          (-Complex.I) • (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) * Q n) =
          (-Complex.I) • ((σ.Nn n : ℂ) • (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) *
            fdiffOp (σ.b n) σ.g J f a c) -
            CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) * Q n) := by
        rw [hdir n, smul_sub]
      show ‖σ.dirOp (.fn f hf) (.gen a c) n -
          (-Complex.I) • (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) * Q n)‖ ≤ ε
      rw [e]
      have h1 : ‖(-Complex.I) • ((σ.Nn n : ℂ) • (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) *
            fdiffOp (σ.b n) σ.g J f a c) -
            CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) * Q n)‖ ≤
          ‖(-Complex.I)‖ * ‖(σ.Nn n : ℂ) • (CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) *
            fdiffOp (σ.b n) σ.g J f a c) -
            CartesianOccupationTransfer.physical (σ.b n) σ.g (a : ℤ) (c : ℤ) * Q n‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      have h5 : ‖(-Complex.I)‖ = 1 := by simp
      rw [h5, one_mul] at h1
      exact h1.trans (h (σ.Nn n) (σ.b n) σ.g hn (σ.hN n))
    · have hz := σ.hcube u hu t ht
      simp only [Expr0.cl]
      rw [poisson_cntF_genF (c2Near_differentiableAt hf hz)]
      simp only [cntF, dirDeriv]
      ring



/-- **Two count functions commute** (`canonical_algebra.tex:46`): both the scaled commutator and the classical bracket
vanish. -/
theorem diracLeaf_fn_fn {f g : (↥J → ℝ) → ℂ} (hf : C2Near J f) (hg : C2Near J g) :
    DiracOK σ (.fn f hf) (.fn g hg) := by
  have h0 : ∀ n, σ.dirOp (.fn f hf) (.fn g hg) n = 0 := by
    intro n
    unfold Setting.dirOp
    simp only [Setting.op0, Expr0.op]
    rw [countOp_comm (σ.b n) σ.g J (BddOn.of_continuousOn hf.continuousOn)
      (BddOn.of_continuousOn hg.continuousOn), sub_self]
    exact smul_zero_clm _
  refine ⟨⟨0, le_rfl, fun n => by rw [h0 n]; exact (ContinuousLinearMap.opNorm_zero).le⟩, ?_⟩
  have e : (fun n => σ.dirOp (.fn f hf) (.fn g hg) n) = fun n => (0 : HN L (σ.Nn n) →L[ℂ] HN L (σ.Nn n)) :=
    funext h0
  rw [e]
  refine strong_zero _ fun u hu t ht => ?_
  have hz := σ.hcube u hu t ht
  simp only [Expr0.cl]
  exact poisson_cntF_cntF (c2Near_differentiableAt hf hz) (c2Near_differentiableAt hg hz)

/-- The leaves of an expression: generators and count functions. -/
def IsLeaf : Expr0 J → Prop
  | .gen _ _ => True
  | .fn _ _ => True
  | _ => False

theorem diracLeaf : ∀ (A C : Expr0 J), IsLeaf A → IsLeaf C → DiracOK σ A C
  | .gen a c, .gen d e, _, _ => diracLeaf_gen_gen σ a c d e
  | .gen a c, .fn g hg, _, _ => (diracLeaf_fn_gen σ hg a c).neg
  | .fn f hf, .gen a c, _, _ => diracLeaf_fn_gen σ hf a c
  | .fn f hf, .fn g hg, _, _ => diracLeaf_fn_fn σ hf hg
  | .add _ _, _, h, _ => h.elim
  | .mul _ _, _, h, _ => h.elim
  | .smul _ _, _, h, _ => h.elim
  | .gen _ _, .add _ _, _, h => h.elim
  | .gen _ _, .mul _ _, _, h => h.elim
  | .gen _ _, .smul _ _, _, h => h.elim
  | .fn _ _, .add _ _, _, h => h.elim
  | .fn _ _, .mul _ _, _, h => h.elim
  | .fn _ _, .smul _ _, _, h => h.elim

theorem diracLeaf_any (A : Expr0 J) (hA : IsLeaf A) : ∀ C : Expr0 J, DiracOK σ A C
  | .gen d e => diracLeaf σ A (.gen d e) hA trivial
  | .fn g hg => diracLeaf σ A (.fn g hg) hA trivial
  | .add C₁ C₂ => (DiracOK.add σ (diracLeaf_any A hA C₁).neg (diracLeaf_any A hA C₂).neg).neg
  | .mul C₁ C₂ =>
      (DiracOK.mul σ (pairOK σ C₁) (pairOK σ C₂) (diracLeaf_any A hA C₁).neg
        (diracLeaf_any A hA C₂).neg).neg
  | .smul c C₁ => (DiracOK.smul σ c (diracLeaf_any A hA C₁).neg).neg

/-- **The Dirac clause for every pair of adjoint-free expressions** (Leibniz induction in both slots). -/
theorem diracOK_all : ∀ A C : Expr0 J, DiracOK σ A C
  | .gen a c => diracLeaf_any σ (.gen a c) trivial
  | .fn f hf => diracLeaf_any σ (.fn f hf) trivial
  | .add A₁ A₂ => fun C => DiracOK.add σ (diracOK_all A₁ C) (diracOK_all A₂ C)
  | .mul A₁ A₂ => fun C =>
      DiracOK.mul σ (pairOK σ A₁) (pairOK σ A₂) (diracOK_all A₁ C) (diracOK_all A₂ C)
  | .smul c A₁ => fun C => DiracOK.smul σ c (diracOK_all A₁ C)

end Leaves

end QuantumNLS.CountFunctionsS01Engine
