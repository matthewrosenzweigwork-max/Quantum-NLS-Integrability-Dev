import QuantumNLS.FullWickH14
import QuantumNLS.ReconstructionR33m

/-!
# MainTheoremR01Algebra: finite-algebra consequences used by parts (iii) and (v) of R-AF8F7562 `thm:main`

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex`, lines 44-51 (words, expectations, the scaled
commutator bound in eq:dirac-main) and 70-73 (positivity, trace one and the matrix-element formula for
`Γ_N(t)`); proof `correspondence_theorem.tex` lines 33-36 and 47-52, `canonical_algebra.tex` eq:words.

Derived here from accepted objects only (no new operator is defined):
* `orderedWord_eq_E`, `orderedWord_adj_eq_E`: the full-Wick ordered word of generators at a gauge is literally the
  ordered product of the Cartesian transfers `E^q_{N,ab}` of R-8362E5EB (`FullWickO1.gauge_conjugation_RD`);
* `cartesian_words`: the dynamic strong symbols of every fixed ordered word in the Cartesian transfers and their
  adjoints, with the product symbol (from the R-140AE34B dynamic word clause), and `cartesian_word_expectation`
  ("In particular, its expectation converges");
* `dirac_scaled_bound`: `sup_N ‖N[A_N, C_N]‖ < ∞` for balanced polynomial quantizations (Cartesian transfers are
  the bilinear case), from the R-140AE34B Stage 1 Dirac bound and coefficient bound;
* `density_facts`: `Γ_N[φ]` is positive, has trace one, and `Γ_N[φ]_{ab} = ⟨φ, E^q_{N,ab} φ⟩`.

No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.MainTheoremR01Algebra

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.WickSymbols (Sym Balanced coeffNorm)
open QuantumNLS.WickBounds (gensym wordSym labelsOf Cfg)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)
open QuantumNLS.OccupationUnitary (oneBasis)

variable {L κ : ℝ} [Fact (0 < L)]

theorem orderedWord_eq_E (hκ : 0 < κ) (g : Gauge) (n : ℕ) (w : List (ℤ × ℤ)) :
    FullWickS1.orderedWord (ReconstructionR33m.basis (L := L) hκ n) g w =
      (w.map fun p => ReconstructionR33m.E (L := L) hκ g n p.1 p.2).prod := by
  unfold FullWickS1.orderedWord
  congr 1
  exact List.map_congr_left fun p _ => FullWickO1.gauge_conjugation_RD hκ g n p.1 p.2

theorem orderedWord_adj_eq_E (hκ : 0 < κ) (g : Gauge) (n : ℕ) (w : List (ℤ × ℤ)) :
    ((w.map fun p => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) g (gensym p.2 p.1)).reverse).prod =
      ((w.map fun p => (ReconstructionR33m.E (L := L) hκ g n p.1 p.2).adjoint).reverse).prod := by
  congr 2
  exact List.map_congr_left fun p _ => by
    rw [FullWickO1.gauge_conjugation_RD_adjoint]

/-- **Dynamic ordered words in the Cartesian transfers** (printed part (iii), eq:words): for every fixed word
`(a_1,b_1) ⋯ (a_ℓ,b_ℓ)`, `E^q_{a_1b_1} ⋯ E^q_{a_ℓb_ℓ}` has, uniformly on the compact box and for every norm-close
preparation, the strong symbol `∏ c_{a_jb_j}(Φ_t u)`, and the reversed product of the adjoints has the conjugate
symbol. -/
theorem cartesian_words (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (w : List (ℤ × ℤ)) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (w.map fun p => ReconstructionR33m.E (L := L) hκ G n p.1 p.2).prod)
      (fun n => ((w.map fun p => (ReconstructionR33m.E (L := L) hκ G n p.1 p.2).adjoint).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        (w.map fun p => (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) p.1 *
          conj ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ) p.2)).prod) := by
  have h := FullWickH10.dynamic_word_clause L κ hκ F G D u hu R lo hi ψ hψ w
  simp only [orderedWord_eq_E, orderedWord_adj_eq_E, WickSpectralBridge.evalSym_wordSym] at h
  exact h

/-- The expectation of an operator with a strong symbol at a unit vector. -/
theorem expectation_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (A : E →L[ℂ] E)
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

/-- **Expectations of Cartesian words converge** uniformly on the box ("In particular, its expectation
converges"). -/
theorem cartesian_word_expectation (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (w : List (ℤ × ℤ)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ TimeBox R lo hi,
      ‖⟪ReconstructionR33m.U (L := L) hκ R t n (ψ n),
          (w.map fun p => ReconstructionR33m.E (L := L) hκ G n p.1 p.2).prod
            (ReconstructionR33m.U (L := L) hκ R t n (ψ n))⟫_ℂ -
        (w.map fun p => (ReconstructionR33m.w hκ F u R t : ℤ → ℂ) p.1 *
          conj ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ) p.2)).prod‖ ≤ ε := by
  intro ε hε
  have h := (cartesian_words hκ F G D u hu R lo hi ψ hψ w).1 ε hε
  filter_upwards [h] with n hn
  intro t ht
  have hv : ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hψ.1 n
  exact (expectation_le _ _ _ hv).trans (hn () (Set.mem_univ _) t ht)

/-- **The scaled commutator is uniformly bounded** (`sup_N ‖N[A_N, C_N]‖ < ∞`, eq:dirac-main) for the balanced
polynomial quantizations at any gauge, `N = 1+n`. -/
theorem dirac_scaled_bound (hκ : 0 < κ) (G : Gauge) {f h : Sym} (hf : Balanced f) (hh : Balanced h)
    {S : Finset ℤ} (hSf : labelsOf f ⊆ S) (hSh : labelsOf h ⊆ S) :
    ∃ M : ℝ, ∀ n : ℕ,
      ‖((1 + n : ℕ) : ℂ) •
        (BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f *
            BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G h -
          BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G h *
            BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f)‖ ≤ M := by
  refine ⟨coeffNorm (WickSymbols.pb S f h) + |Cfg f h + Cfg h f|, fun n => ?_⟩
  have hN : 0 < 1 + n := by omega
  set b := ReconstructionR33m.basis (L := L) hκ n
  set X := BalancedWickDefinition.quantization b G f * BalancedWickDefinition.quantization b G h -
    BalancedWickDefinition.quantization b G h * BalancedWickDefinition.quantization b G f
  have hD := FullWickH1.quantization_Dirac_bound hN b G hf hh hSf hSh
  have hc := FullWickH1.quantization_coeff_bound hN b G (WickBounds.balanced_pb S hf hh)
  have hrw : ((1 + n : ℕ) : ℂ) • X = Complex.I • ((-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X) := by
    rw [smul_smul]
    congr 1
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  have hnorm : ‖((1 + n : ℕ) : ℂ) • X‖ ≤ ‖(-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X‖ := by
    rw [hrw]
    calc ‖Complex.I • ((-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X)‖
        ≤ ‖Complex.I‖ * ‖(-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ = ‖(-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X‖ := by rw [Complex.norm_I, one_mul]
  have hinv : ((1 + n : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
  have hCf : (Cfg f h + Cfg h f) * ((1 + n : ℕ) : ℝ)⁻¹ ≤ |Cfg f h + Cfg h f| := by
    calc (Cfg f h + Cfg h f) * ((1 + n : ℕ) : ℝ)⁻¹ ≤ |Cfg f h + Cfg h f| * ((1 + n : ℕ) : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Cfg f h + Cfg h f| * 1 := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = |Cfg f h + Cfg h f| := mul_one _
  refine hnorm.trans ?_
  calc ‖(-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X‖
      = ‖((-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X -
          BalancedWickDefinition.quantization b G (WickSymbols.pb S f h)) +
        BalancedWickDefinition.quantization b G (WickSymbols.pb S f h)‖ := by rw [sub_add_cancel]
    _ ≤ ‖(-(Complex.I) * ((1 + n : ℕ) : ℂ)) • X -
          BalancedWickDefinition.quantization b G (WickSymbols.pb S f h)‖ +
        ‖BalancedWickDefinition.quantization b G (WickSymbols.pb S f h)‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ (Cfg f h + Cfg h f) * ((1 + n : ℕ) : ℝ)⁻¹ + coeffNorm (WickSymbols.pb S f h) := add_le_add hD hc
    _ ≤ coeffNorm (WickSymbols.pb S f h) + |Cfg f h + Cfg h f| := by linarith

/-- **`Γ_N[φ]` is positive with trace one, and `Γ_N[φ]_{ab} = ⟨φ, E^q_{N,ab} φ⟩`** (part (v)). -/
theorem density_facts (hκ : 0 < κ) (g : Gauge) (n : ℕ) (φ : HN L (1 + n)) (hφ : ‖φ‖ = 1) :
    (ReconstructionR33m.density hκ g n φ).IsPositive ∧
    TraceClass.posTrace (ReconstructionR33m.density hκ g n φ) = 1 ∧
    ∀ a b : ℤ, ⟪oneBasis a, ReconstructionR33m.density hκ g n φ (oneBasis b)⟫_ℂ =
      ⟪φ, ReconstructionR33m.E (L := L) hκ g n a b φ⟫_ℂ := by
  refine ⟨ExactDensity.gamma_isPositive _, ?_, fun a b => ?_⟩
  · unfold ReconstructionR33m.density PreparationStability.density
    rw [ExactDensity.posTrace_Gamma, LinearIsometryEquiv.norm_map, hφ]
    simp
  · have he := PreparationStability.density_entry (ReconstructionR33m.basis hκ n) g φ a b
    rw [AuxiliaryDensity.gammaEntry] at he
    exact he

end QuantumNLS.MainTheoremR01Algebra

#print axioms QuantumNLS.MainTheoremR01Algebra.cartesian_words
#print axioms QuantumNLS.MainTheoremR01Algebra.cartesian_word_expectation
#print axioms QuantumNLS.MainTheoremR01Algebra.dirac_scaled_bound
#print axioms QuantumNLS.MainTheoremR01Algebra.density_facts
