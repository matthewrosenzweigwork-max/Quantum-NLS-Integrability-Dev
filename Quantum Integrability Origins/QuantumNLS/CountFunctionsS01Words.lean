import QuantumNLS.CountFunctionsS01Sym
import QuantumNLS.CountFunctionsS01Prod
import QuantumNLS.FullWickH10

/-!
# CountFunctionsS01Words: ordered words mixing Cartesian transfers, phase transfers, Wick quantizations and
continuous functions of finitely many intensive counts, with the product symbol (dynamic and static)

PRINTED SOURCES
* `source-text/chapters/principal_correspondence.tex:42-43` (sha256 `6008c7e6…da56`):
  "Every fixed ordered word in these bounded observables, their adjoints, and continuous functions of finitely many
   intensive counts has the product of the corresponding scalar symbols, in the same strong and compact-time-uniform
   sense. In particular, its expectation converges."
* `principal_correspondence.tex:46-47`: "The fixed balanced polynomial quantization in Section 5 has the same strong
  dynamical symbols, adjoints and norm-close stability."
* `source-text/chapters/core/canonical_algebra.tex:48-54` (eq:words, `b2a1e9c4…0395`): "strong convergence for a fixed
  ordered word follows from the exact telescoping identity ... The prefixes have uniformly bounded norm. Count
  functions follow by bounded convergence under the invariant occupation law."

OBJECTS.  A `Letter` is a Cartesian transfer `E^q_{N,ab}`, a unit-phase transfer `W^q_{N,ab}` (admissible only for
`a ≠ b` with positive tested actions, as printed), a count function `f(B_{N,J})` (admissible for `f` continuous on the
cube `[0,1]^J`; `CountFunctionsS01Ops.countOp`) or a balanced Wick quantization `W^q_N(f)` (DEF-032); a `WLetter`
carries an adjoint flag.  A word is a list of `WLetter`; its operator is the ordered product and its companion is the
reversed product of the adjoints.

HEADLINES: `dynamic_words` (every normalized norm-close preparation `Preparation u ψ`, every compact box `TimeBox`, the
gauge `G` of the supplied `RD8362E5EBInput`) and `static_words` (uniform on `𝒰_R`, the static input
`UniformStatic hκ j q` at the gauge `staticGauge q`; unit-phase letters are not included in the static statement).
No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace
open QuantumNLS CountFunctionsS01Ops CountFunctionsS01Sym
open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.WickSymbols (Sym Balanced coeffNorm)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.UniformStaticR49b (UniformStatic)

namespace QuantumNLS.CountFunctionsS01Words

/-- The letters of a word. -/
inductive Letter where
  | cart (a b : ℤ)
  | phase (a b : ℤ)
  | count (J : Finset ℤ) (f : (↥J → ℝ) → ℂ)
  | wick (f : Sym)

/-- A letter with an adjoint flag. -/
structure WLetter where
  base : Letter
  star : Bool

/-- The classical count point `a_J = (|z_j|²)_{j ∈ J}`. -/
def aPt (J : Finset ℤ) (z : ℤ → ℂ) : ↥J → ℝ := fun j => ‖z (j : ℤ)‖ ^ 2

/-- Classical symbol of a letter at the coordinate point `z`. -/
def baseSym (z : ℤ → ℂ) : Letter → ℂ
  | .cart a b => z a * conj (z b)
  | .phase a b => (z a * conj (z b)) / ((Real.sqrt (‖z a‖ ^ 2 * ‖z b‖ ^ 2) : ℝ) : ℂ)
  | .count J f => f (aPt J z)
  | .wick f => evalSym z f

def wSym (z : ℤ → ℂ) (ℓ : WLetter) : ℂ := if ℓ.star then conj (baseSym z ℓ.base) else baseSym z ℓ.base

open Classical in
/-- A bound for a count function on the cube (zero if `f` is not continuous there). -/
def cntBnd (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) : ℝ :=
  if h : ContinuousOn f (cube J) then (BddOn.of_continuousOn h).choose else 0

lemma cntBnd_spec {J : Finset ℤ} {f : (↥J → ℝ) → ℂ} (h : ContinuousOn f (cube J)) :
    0 ≤ cntBnd J f ∧ ∀ x ∈ cube J, ‖f x‖ ≤ cntBnd J f := by
  unfold cntBnd
  rw [dif_pos h]
  exact (BddOn.of_continuousOn h).choose_spec

lemma cntBnd_nonneg (J : Finset ℤ) (f : (↥J → ℝ) → ℂ) : 0 ≤ cntBnd J f := by
  by_cases h : ContinuousOn f (cube J)
  · exact (cntBnd_spec h).1
  · unfold cntBnd
    rw [dif_neg h]

/-- The operator bound of a letter. -/
def bnd : Letter → ℝ
  | .cart _ _ => 1
  | .phase _ _ => 1
  | .count J f => cntBnd J f
  | .wick f => coeffNorm f

lemma coeffNorm_nonneg' (f : Sym) : 0 ≤ coeffNorm f :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma bnd_nonneg : ∀ ℓ : Letter, 0 ≤ bnd ℓ
  | .cart _ _ => zero_le_one
  | .phase _ _ => zero_le_one
  | .count J f => cntBnd_nonneg J f
  | .wick f => coeffNorm_nonneg' f

lemma aPt_mem_cube {J : Finset ℤ} {z : ℤ → ℂ} (h : ∀ j ∈ J, ‖z j * conj (z j)‖ ≤ 1) :
    aPt J z ∈ cube J := by
  intro j
  refine ⟨sq_nonneg _, ?_⟩
  have := h j j.2
  rwa [norm_mul, Complex.norm_conj, ← sq] at this

lemma mul_conj_eq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Swapping the roles of the operator and its companion conjugates the symbol. -/
theorem pair_swap {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]
    {X Θ : Type*} {A A' : ∀ N, H N →L[ℂ] H N} {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N}
    {s : X → Θ → ℂ} (h : HasUniformPairT A A' S Tb ψ s) :
    HasUniformPairT A' A S Tb ψ (fun u t => conj (s u t)) := by
  refine ⟨h.2, ?_⟩
  have e : (fun u t => conj (conj (s u t))) = s := by
    funext u t
    exact Complex.conj_conj _
  show HasUniformStrongT A S Tb ψ (fun u t => conj (conj (s u t)))
  rw [e]
  exact h.1


/-! ### Dynamic words (printed part (iii)) -/

section Dynamic

variable {L κ : ℝ} [Fact (0 < L)]

/-- The operator of a letter along the R-8362E5EB objects (`N = 1 + n`, gauge `G`). -/
def dynOp (hκ : 0 < κ) (G : Gauge) (n : ℕ) : Letter → (HN L (1 + n) →L[ℂ] HN L (1 + n))
  | .cart a b => ReconstructionR33m.E (L := L) hκ G n a b
  | .phase a b => ReconstructionR33m.W (L := L) hκ G n a b
  | .count J f => countOp (ReconstructionR33m.basis (L := L) hκ n) G J f
  | .wick f => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f

def wOp (hκ : 0 < κ) (G : Gauge) (n : ℕ) (ℓ : WLetter) : HN L (1 + n) →L[ℂ] HN L (1 + n) :=
  if ℓ.star then (dynOp hκ G n ℓ.base).adjoint else dynOp hκ G n ℓ.base

/-- Admissibility of a letter at the initial profile `u` (the printed hypotheses: positive tested actions for the
unit-phase letters, continuity of the count function on the cube, balanced Wick polynomial). -/
def Adm (hκ : 0 < κ) (u : Def033HierarchyR24m.Smooth L) : Letter → Prop
  | .cart _ _ => True
  | .phase a b => a ≠ b ∧
      0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (Def033HierarchyR24m.physical u) a‖ ^ 2 ∧
      0 < ‖(Def021ChartR41b.chart L κ hκ).Φ (Def033HierarchyR24m.physical u) b‖ ^ 2
  | .count J f => ContinuousOn f (cube J)
  | .wick f => Balanced f

lemma dynOp_norm_le (hκ : 0 < κ) (G : Gauge) (n : ℕ) (u : Def033HierarchyR24m.Smooth L) :
    ∀ ℓ : Letter, Adm hκ u ℓ → ‖dynOp (L := L) hκ G n ℓ‖ ≤ bnd ℓ
  | .cart a b, _ => by
      unfold dynOp
      exact CartesianOccupationTransfer.physical_norm_le _ _ _ _
  | .phase a b, _ => by
      unfold dynOp
      exact UnitPhaseTransfer.physical_norm_le _ _ _ _
  | .count J f, h => by
      unfold dynOp
      exact countOp_norm_le _ _ J (cntBnd_spec h).1 (cntBnd_spec h).2
  | .wick f, h => by
      unfold dynOp
      exact FullWickH1.quantization_coeff_bound (by omega) _ G h

lemma wOp_norm_le (hκ : 0 < κ) (G : Gauge) (n : ℕ) (u : Def033HierarchyR24m.Smooth L) (ℓ : WLetter)
    (h : Adm hκ u ℓ.base) :
    ‖wOp (L := L) hκ G n ℓ‖ ≤ bnd ℓ.base ∧ ‖(wOp (L := L) hκ G n ℓ).adjoint‖ ≤ bnd ℓ.base := by
  have h0 := dynOp_norm_le (L := L) hκ G n u ℓ.base h
  unfold wOp
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [ContinuousLinearMap.adjoint.norm_map]; exact h0
    · rw [ContinuousLinearMap.adjoint_adjoint]; exact h0
  · exact ⟨h0, by rw [ContinuousLinearMap.adjoint.norm_map]; exact h0⟩

/-- The one-letter pair clause (dynamic). -/
theorem dyn_letter_pair (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) :
    ∀ ℓ : Letter, Adm hκ u ℓ →
      HasUniformPairT (H := fun n => HN L (1 + n)) (fun n => dynOp hκ G n ℓ)
        (fun n => (dynOp hκ G n ℓ).adjoint) (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => baseSym (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) ℓ)
  | .cart a b, _ => FullWickH5.generator_pair hκ F G D u hu R lo hi ψ hψ a b
  | .phase a b, ⟨hab, h1, h2⟩ => FullWickH5.phase_pair hκ F G D u hu R lo hi ψ hψ a b hab h1 h2
  | .wick f, h => FullWickH9.dyn_poly_pair hκ F G D u hu R lo hi ψ hψ h
  | .count J f, h => by
      have hdiag : ∀ j : ℤ, HasUniformPairT (H := fun n => HN L (1 + n))
          (fun n => ReconstructionR33m.E (L := L) hκ G n j j)
          (fun n => (ReconstructionR33m.E (L := L) hκ G n j j).adjoint) (Set.univ : Set Unit)
          (TimeBox R lo hi) (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
          (fun (_ : Unit) (t : ℕ → ℝ) => (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) j *
            conj ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ) j)) :=
        fun j => FullWickH5.generator_pair hκ F G D u hu R lo hi ψ hψ j j
      have hψ1 : ∀ᶠ n : ℕ in atTop, ∀ _ ∈ (Set.univ : Set Unit), ∀ t ∈ TimeBox R lo hi,
          ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ = 1 :=
        Filter.Eventually.of_forall fun n _ _ t _ => FullWickH9.dyn_prep_norm hκ hψ R n t
      have hcube : ∀ _u ∈ (Set.univ : Set Unit), ∀ t ∈ TimeBox R lo hi,
          aPt J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) ∈ cube J := by
        intro _ _ t ht
        refine aPt_mem_cube fun j _ => ?_
        exact CountFunctionsS01Prod.symbol_le_of_strong
          (A := fun n => ReconstructionR33m.E (L := L) hκ G n j j)
          (C := 1) (Filter.Eventually.of_forall fun n => CartesianOccupationTransfer.physical_norm_le _ _ _ _)
          hψ1 (hdiag j).1 () (Set.mem_univ _) t ht
      have hB : ∀ j : ↥J, HasUniformStrongT (H := fun n => HN L (1 + n))
          (fun n => CartesianOccupationTransfer.physical (ReconstructionR33m.basis (L := L) hκ n) G
            (j : ℤ) (j : ℤ)) (Set.univ : Set Unit) (TimeBox R lo hi)
          (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
          (fun (_ : Unit) (t : ℕ → ℝ) =>
            ((aPt J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) j : ℝ) : ℂ)) := by
        intro j
        have e : (fun (_ : Unit) (t : ℕ → ℝ) => ((aPt J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) j : ℝ) : ℂ)) =
            (fun (_ : Unit) (t : ℕ → ℝ) => (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) (j : ℤ) *
              conj ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ) (j : ℤ))) := by
          funext _ t
          exact (mul_conj_eq _).symm
        rw [e]
        exact (hdiag (j : ℤ)).1
      exact count_pair (fun n => 1 + n) (fun n => ReconstructionR33m.basis (L := L) hκ n) G J h
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => aPt J (ReconstructionR33m.w hκ F u R t : ℤ → ℂ))
        hcube (hψ1.mono fun n hn u hu t ht => (hn u hu t ht).le) hB

/-- The one-letter pair clause for a letter with an adjoint flag. -/
theorem dyn_wletter_pair (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (ℓ : WLetter) (h : Adm hκ u ℓ.base) :
    HasUniformPairT (H := fun n => HN L (1 + n)) (fun n => wOp hκ G n ℓ)
        (fun n => (wOp hκ G n ℓ).adjoint) (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) => wSym (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) ℓ) := by
  have h0 := dyn_letter_pair hκ F G D u hu R lo hi ψ hψ ℓ.base h
  unfold wOp wSym
  cases hs : ℓ.star
  · simpa using h0
  · simp only [ite_true]
    have h1 := pair_swap h0
    have e : (fun n => ((dynOp (L := L) hκ G n ℓ.base).adjoint).adjoint) = fun n => dynOp (L := L) hκ G n ℓ.base := by
      funext n
      exact ContinuousLinearMap.adjoint_adjoint _
    rw [e]
    exact h1



/-- **Dynamic ordered words** (printed part (iii), `principal_correspondence.tex:42-43`; eq:words): for every fixed
word of admissible letters (Cartesian transfers, unit-phase transfers on positive-action pairs, continuous functions of
finitely many intensive counts, balanced Wick quantizations, and adjoints of these), uniformly on every compact box
`TimeBox R lo hi` and for every norm-close preparation `ψ`, the ordered product has the strong symbol equal to the
product of the letter symbols, and the reversed product of the adjoints has the conjugate symbol. -/
theorem dynamic_words (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (l : List WLetter)
    (hl : ∀ ℓ ∈ l, Adm hκ u ℓ.base) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (l.map fun ℓ => wOp hκ G n ℓ).prod)
      (fun n => ((l.map fun ℓ => (wOp hκ G n ℓ).adjoint).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        (l.map fun ℓ => wSym (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) ℓ).prod) := by
  refine CountFunctionsS01Prod.prod_of_pairs (H := fun n => HN L (1 + n))
    (fun ℓ n => wOp hκ G n ℓ) (fun ℓ n => (wOp hκ G n ℓ).adjoint)
    (fun ℓ (_ : Unit) (t : ℕ → ℝ) => wSym (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) ℓ)
    (Set.univ : Set Unit) (TimeBox R lo hi)
    (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
    (fun ℓ => bnd ℓ.base) l (fun ℓ _ => bnd_nonneg _)
    (fun ℓ hℓ => Filter.Eventually.of_forall fun n => (wOp_norm_le hκ G n u ℓ (hl ℓ hℓ)).1)
    (fun ℓ hℓ => Filter.Eventually.of_forall fun n => (wOp_norm_le hκ G n u ℓ (hl ℓ hℓ)).2)
    (fun ℓ hℓ => dyn_wletter_pair hκ F G D u hu R lo hi ψ hψ ℓ (hl ℓ hℓ))
    (Filter.Eventually.of_forall fun n _ _ t _ => FullWickH9.dyn_prep_norm hκ hψ R n t)

theorem expectation_le' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : E →L[ℂ] E)
    (a : ℂ) (v : E) (hv : ‖v‖ = 1) :
    ‖⟪v, A v⟫_ℂ - a‖ ≤ ‖(A - a • ContinuousLinearMap.id ℂ E) v‖ := by
  have h : ⟪v, (A - a • ContinuousLinearMap.id ℂ E) v⟫_ℂ = ⟪v, A v⟫_ℂ - a := by
    change ⟪v, A v - a • v⟫_ℂ = _
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    simp
  rw [← h]
  calc ‖⟪v, (A - a • ContinuousLinearMap.id ℂ E) v⟫_ℂ‖
      ≤ ‖v‖ * ‖(A - a • ContinuousLinearMap.id ℂ E) v‖ := norm_inner_le_norm _ _
    _ = ‖(A - a • ContinuousLinearMap.id ℂ E) v‖ := by rw [hv, one_mul]

/-- **Expectations of dynamic words converge** (`principal_correspondence.tex:43`: "In particular, its expectation
converges"), uniformly on the box. -/
theorem dynamic_word_expectation (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (l : List WLetter)
    (hl : ∀ ℓ ∈ l, Adm hκ u ℓ.base) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ TimeBox R lo hi,
      ‖⟪ReconstructionR33m.U (L := L) hκ R t n (ψ n),
          (l.map fun ℓ => wOp hκ G n ℓ).prod (ReconstructionR33m.U (L := L) hκ R t n (ψ n))⟫_ℂ -
        (l.map fun ℓ => wSym (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) ℓ).prod‖ ≤ ε := by
  intro ε hε
  have h := (dynamic_words hκ F G D u hu R lo hi ψ hψ l hl).1 ε hε
  filter_upwards [h] with n hn
  intro t ht
  have hv : ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ = 1 := FullWickH9.dyn_prep_norm hκ hψ R n t
  exact (expectation_le' _ _ _ hv).trans (hn () (Set.mem_univ _) t ht)

end Dynamic

/-! ### Static words (printed part (ii) / eq:words), unit-phase letters not included -/

section Static

variable {L κ : ℝ} [Fact (0 < L)]

def statOp (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge) (n : ℕ) : Letter → (HN L (n + 1) →L[ℂ] HN L (n + 1))
  | .cart a b => UniformStaticR49b.E (L := L) hκ q n (a, b)
  | .phase _ _ => 0
  | .count J f => countOp (Def044D1SpectralR51a.basis (L := L) hκ n) (FullWickO1.staticGauge q) J f
  | .wick f => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
      (FullWickO1.staticGauge q) f

def sOp (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge) (n : ℕ) (ℓ : WLetter) :
    HN L (n + 1) →L[ℂ] HN L (n + 1) :=
  if ℓ.star then (statOp hκ q n ℓ.base).adjoint else statOp hκ q n ℓ.base

/-- Static admissibility (unit-phase letters excluded). -/
def AdmS : Letter → Prop
  | .cart _ _ => True
  | .phase _ _ => False
  | .count J f => ContinuousOn f (cube J)
  | .wick f => Balanced f

lemma statOp_norm_le (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge) (n : ℕ) :
    ∀ ℓ : Letter, AdmS ℓ → ‖statOp (L := L) hκ q n ℓ‖ ≤ bnd ℓ
  | .cart a b, _ => by
      unfold statOp
      exact FullWickO2.norm_E_le hκ q n (a, b)
  | .phase _ _, h => absurd h (by simp [AdmS])
  | .count J f, h => by
      unfold statOp
      exact countOp_norm_le _ _ J (cntBnd_spec h).1 (cntBnd_spec h).2
  | .wick f, h => by
      unfold statOp
      exact FullWickH1.quantization_coeff_bound (Nat.succ_pos n) _ _ h

lemma sOp_norm_le (hκ : 0 < κ) (q : UniformStaticR49b.SectorGauge) (n : ℕ) (ℓ : WLetter) (h : AdmS ℓ.base) :
    ‖sOp (L := L) hκ q n ℓ‖ ≤ bnd ℓ.base ∧ ‖(sOp (L := L) hκ q n ℓ).adjoint‖ ≤ bnd ℓ.base := by
  have h0 := statOp_norm_le (L := L) hκ q n ℓ.base h
  unfold sOp
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [ContinuousLinearMap.adjoint.norm_map]; exact h0
    · rw [ContinuousLinearMap.adjoint_adjoint]; exact h0
  · exact ⟨h0, by rw [ContinuousLinearMap.adjoint.norm_map]; exact h0⟩

lemma static_symbol_eq (hκ : 0 < κ) (u : L2T L) (a b : ℤ) :
    UniformStaticR49b.symbol hκ u (a, b) =
      ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) a * conj (((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) b) :=
  (FullWickO2.symbol_eq_evaluate hκ u a b).trans (FullWickO1.evaluate_bilinearPoly a b _)

theorem stat_letter_pair (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) :
    ∀ ℓ : Letter, AdmS ℓ →
      HasUniformPairT (H := fun n => HN L (n + 1)) (fun n => statOp hκ q n ℓ)
        (fun n => (statOp hκ q n ℓ).adjoint) (UR (L := L) R) Tb
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) => baseSym ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) ℓ)
  | .cart a b, _ => by
      have h := FullWickO2.cartesian_uniform_pair hκ j q hU Tb R a b
      have e : (fun (u : L2T L) (_ : Θ) => UniformStaticR49b.symbol hκ u (a, b)) =
          (fun (u : L2T L) (_ : Θ) => ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) a *
            conj (((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) b)) := by
        funext u _
        exact static_symbol_eq hκ u a b
      rw [e] at h
      exact h
  | .phase _ _, h => absurd h (by simp [AdmS])
  | .wick f, h => FullWickH8.static_poly_pair hκ hU Tb R h
  | .count J f, h => by
      have hdiag : ∀ i : ℤ, HasUniformPairT (H := fun n => HN L (n + 1))
          (fun n => UniformStaticR49b.E (L := L) hκ q n (i, i))
          (fun n => (UniformStaticR49b.E (L := L) hκ q n (i, i)).adjoint) (UR (L := L) R) Tb
          (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
          (fun (u : L2T L) (_ : Θ) => ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) i *
            conj (((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) i)) := by
        intro i
        have h := FullWickO2.cartesian_uniform_pair hκ j q hU Tb R i i
        have e : (fun (u : L2T L) (_ : Θ) => UniformStaticR49b.symbol hκ u (i, i)) =
            (fun (u : L2T L) (_ : Θ) => ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) i *
              conj (((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) i)) := by
          funext u _
          exact static_symbol_eq hκ u i i
        rw [e] at h
        exact h
      have hψ1 : ∀ᶠ n : ℕ in atTop, ∀ u ∈ UR (L := L) R, ∀ _t ∈ Tb,
          ‖(UniformStaticR49b.product n u : HN L (n + 1))‖ = 1 :=
        Filter.Eventually.of_forall fun n u hu _ _ => FullWickO2.norm_product n u hu.1
      have hcube : ∀ u ∈ UR (L := L) R, ∀ _t ∈ Tb,
          aPt J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) ∈ cube J := by
        intro u hu t ht
        refine aPt_mem_cube fun i _ => ?_
        exact CountFunctionsS01Prod.symbol_le_of_strong
          (A := fun n => UniformStaticR49b.E (L := L) hκ q n (i, i))
          (C := 1) (Filter.Eventually.of_forall fun n => FullWickO2.norm_E_le hκ q n (i, i))
          hψ1 (hdiag i).1 u hu t ht
      have hB : ∀ i : ↥J, HasUniformStrongT (H := fun n => HN L (n + 1))
          (fun n => CartesianOccupationTransfer.physical (Def044D1SpectralR51a.basis (L := L) hκ n)
            (FullWickO1.staticGauge q) (i : ℤ) (i : ℤ)) (UR (L := L) R) Tb
          (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
          (fun (u : L2T L) (_ : Θ) =>
            ((aPt J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) i : ℝ) : ℂ)) := by
        intro i
        have e : (fun (u : L2T L) (_ : Θ) =>
            ((aPt J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) i : ℝ) : ℂ)) =
            (fun (u : L2T L) (_ : Θ) => ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) (i : ℤ) *
              conj (((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) (i : ℤ))) := by
          funext u _
          exact (mul_conj_eq _).symm
        rw [e]
        have h1 := (hdiag (i : ℤ)).1
        have e2 : (fun n => UniformStaticR49b.E (L := L) hκ q n ((i : ℤ), (i : ℤ))) =
            (fun n => CartesianOccupationTransfer.physical (Def044D1SpectralR51a.basis (L := L) hκ n)
              (FullWickO1.staticGauge q) (i : ℤ) (i : ℤ)) := by
          funext n
          exact UniformStaticBridgeR50b.cartesian_eq_projective_physical hκ q n ((i : ℤ), (i : ℤ))
        rw [e2] at h1
        exact h1
      exact count_pair (fun n => n + 1) (fun n => Def044D1SpectralR51a.basis (L := L) hκ n)
        (FullWickO1.staticGauge q) J h (UR (L := L) R) Tb
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) => aPt J ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ))
        hcube (hψ1.mono fun n hn u hu t ht => (hn u hu t ht).le) hB

theorem stat_wletter_pair (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (ℓ : WLetter) (h : AdmS ℓ.base) :
    HasUniformPairT (H := fun n => HN L (n + 1)) (fun n => sOp hκ q n ℓ)
        (fun n => (sOp hκ q n ℓ).adjoint) (UR (L := L) R) Tb
        (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) => wSym ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) ℓ) := by
  have h0 := stat_letter_pair hκ hU Tb R ℓ.base h
  unfold sOp wSym
  cases hs : ℓ.star
  · simpa using h0
  · simp only [ite_true]
    have h1 := pair_swap h0
    have e : (fun n => ((statOp (L := L) hκ q n ℓ.base).adjoint).adjoint) =
        fun n => statOp (L := L) hκ q n ℓ.base := by
      funext n
      exact ContinuousLinearMap.adjoint_adjoint _
    rw [e]
    exact h1

/-- **Static ordered words** (uniform on `𝒰_R`, at the gauge `staticGauge q` of the static input): the same product
symbol for every fixed word of Cartesian transfers, count functions, balanced Wick quantizations and adjoints. -/
theorem static_words (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (l : List WLetter)
    (hl : ∀ ℓ ∈ l, AdmS ℓ.base) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => (l.map fun ℓ => sOp hκ q n ℓ).prod)
      (fun n => ((l.map fun ℓ => (sOp hκ q n ℓ).adjoint).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) =>
        (l.map fun ℓ => wSym ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) ℓ).prod) := by
  refine CountFunctionsS01Prod.prod_of_pairs (H := fun n => HN L (n + 1))
    (fun ℓ n => sOp hκ q n ℓ) (fun ℓ n => (sOp hκ q n ℓ).adjoint)
    (fun ℓ (u : L2T L) (_ : Θ) => wSym ((Def021ChartR41b.chart L κ hκ).Φ u : ℤ → ℂ) ℓ)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
    (fun ℓ => bnd ℓ.base) l (fun ℓ _ => bnd_nonneg _)
    (fun ℓ hℓ => Filter.Eventually.of_forall fun n => (sOp_norm_le hκ q n ℓ (hl ℓ hℓ)).1)
    (fun ℓ hℓ => Filter.Eventually.of_forall fun n => (sOp_norm_le hκ q n ℓ (hl ℓ hℓ)).2)
    (fun ℓ hℓ => stat_wletter_pair hκ hU Tb R ℓ (hl ℓ hℓ))
    (Filter.Eventually.of_forall fun n u hu _ _ => FullWickO2.norm_product n u hu.1)

end Static

end QuantumNLS.CountFunctionsS01Words
