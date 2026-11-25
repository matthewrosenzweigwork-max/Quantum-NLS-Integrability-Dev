import QuantumNLS.FullWickH1
import QuantumNLS.FullWickH6
import QuantumNLS.FullWickH7
import QuantumNLS.FullWickH8
import QuantumNLS.FullWickH9

/-! FullWickH13 (haiku_inventory, R-140AE34B `thm:full-wick`, addendum 7: polynomial products).

Printed reading (source-text/chapters/core/wick_calculus.tex, lines 84-89): "Every fixed ordered product and the
scaled Dirac commutator in (eq:full-Dirac-bound) have the corresponding symbols in each of these two settings",
and "Uniformly norm-close preparations preserve the static uniform statements". The sentence does not restrict the
products to Cartesian generators, and the corresponding symbol of a product `W(f_1) ⋯ W(f_k)` of Wick-polynomial
operators is `f_1(w(u)) ⋯ f_k(w(u))`. The generator products are the special case in which every `f_i` is a
Cartesian generator (FullWickH10.StaticWordClause, DynamicWordClause).

Route. For one balanced polynomial `f`, the reference pair is the frozen per-polynomial pair
(`FullWickH8.static_poly_pair` on `𝒰_R`, `FullWickH9.dyn_poly_pair` along a trajectory). The operator bound is
`‖W(f)‖ ≤ coeffNorm f` (`FullWickH1.quantization_coeff_bound`, with the adjoint norm equal to the operator norm),
and the symbol bound is `coeffNorm f` (static: `FullWickH8.chart_evalSym_norm_le`; dynamic: the generic lemma
`symbol_le_of_strong_bound`, from the strong symbol and the unit norm of the time-evolved preparation). The constants
`C, K` of a finite list are the maxima over its factors (`exists_common_good`, by induction on the list), and the
ordered product is `FullWickH6.pair_list_prod`. The norm-close version uses `FullWickH7.hasUniformPairT_of_normClose`
with the list bounds `C^length`, `K^length`.

Dynamic index and gauge. The dynamic clause keeps the gauge `G` and the input `D : RD8362E5EBInput hκ F G` of the
frozen FullWickH10 dynamic clauses, and the index `1+n` of `ReconstructionR33m.basis`. The Q06 instance is in
FullWickH14 (FullWickO3.rd8362_at_Q06), not here.

Standard dependencies only (audit in FullWickH14).
-/

noncomputable section
open Filter Topology
open scoped ComplexConjugate BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH13

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickH6 (GoodFactor pair_list_prod)
open QuantumNLS.FullWickH7 (IsNormClosePrepT hasUniformPairT_of_normClose)
open QuantumNLS.FullWickO1 (staticGauge)
open QuantumNLS.FullWickO2 (UR)
open QuantumNLS.WickSymbols (Sym Balanced coeffNorm)
open QuantumNLS.WickSpectralBridge (evalSym)
open QuantumNLS.UniformStaticR49b (UniformStatic)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.ReconstructionR33m (RD8362E5EBInput Preparation TimeBox)

/-! ### Generic lemmas (no physical content) -/

section Generic

variable {H : ℕ → Type*} [∀ N, NormedAddCommGroup (H N)] [∀ N, NormedSpace ℂ (H N)]

lemma coeffNorm_nonneg' (f : Sym) : 0 ≤ coeffNorm f := by
  unfold coeffNorm
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- A good factor stays good when both constants are enlarged. -/
lemma goodFactor_mono {ι X Θ : Type*} {f f' : ι → ∀ N, H N →L[ℂ] H N} {s : ι → X → Θ → ℂ}
    {S : Set X} {Tb : Set Θ} {ψ : X → Θ → ∀ N, H N} {C K C' K' : ℝ} {i : ι}
    (hP : GoodFactor f f' s S Tb ψ C K i) (hC : C ≤ C') (hK : K ≤ K') :
    GoodFactor f f' s S Tb ψ C' K' i := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  exact ⟨h1.mono fun N h => h.trans hC, h2.mono fun N h => h.trans hC,
    fun u hu t ht => (h3 u hu t ht).trans hK, h4⟩

/-- Finitely many factors have common constants: the maxima of the individual constants. -/
theorem exists_common_good {ι X Θ : Type*} (f f' : ι → ∀ N, H N →L[ℂ] H N) (s : ι → X → Θ → ℂ)
    (S : Set X) (Tb : Set Θ) (ψ : X → Θ → ∀ N, H N) (l : List ι) :
    (∀ i ∈ l, ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ GoodFactor f f' s S Tb ψ C K i) →
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ i ∈ l, GoodFactor f f' s S Tb ψ C K i := by
  induction l with
  | nil => intro _; exact ⟨0, 0, le_rfl, le_rfl, by simp⟩
  | cons i rest ih =>
    intro h
    obtain ⟨C₁, K₁, hC₁, hK₁, hG₁⟩ := ih (fun j hj => h j (by simp [hj]))
    obtain ⟨C₂, K₂, hC₂, hK₂, hG₂⟩ := h i (by simp)
    refine ⟨max C₁ C₂, max K₁ K₂, le_max_of_le_left hC₁, le_max_of_le_left hK₁, ?_⟩
    intro j hj
    rcases List.mem_cons.1 hj with hj | hj
    · rw [hj]
      exact goodFactor_mono hG₂ (le_max_right _ _) (le_max_right _ _)
    · exact goodFactor_mono (hG₁ j hj) (le_max_left _ _) (le_max_left _ _)

/-- **Symbol bound from a strong symbol with an operator bound.** If `‖A_N‖ ≤ C` eventually, the preparations are
normalized on `S × Tb`, and `a` is a uniform strong symbol of `A`, then `|a| ≤ C` on `S × Tb`. (Generalizes
`FullWickH8.symbol_le_one_of_strong`, which is the case `C = 1`.) -/
theorem symbol_le_of_strong_bound {X Θ : Type*} {A : ∀ N, H N →L[ℂ] H N} {S : Set X} {Tb : Set Θ}
    {ψ : X → Θ → ∀ N, H N} {a : X → Θ → ℂ} {C : ℝ}
    (hA : ∀ᶠ N in atTop, ‖A N‖ ≤ C) (hψ : ∀ᶠ N in atTop, ∀ u ∈ S, ∀ t ∈ Tb, ‖ψ u t N‖ = 1)
    (h : HasUniformStrongT A S Tb ψ a) :
    ∀ u ∈ S, ∀ t ∈ Tb, ‖a u t‖ ≤ C := by
  intro u hu t ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hAN, hψN, hN⟩ := (hA.and (hψ.and (h ε hε))).exists
  have hp : ‖ψ u t N‖ = 1 := hψN u hu t ht
  have hd : ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ ≤ ε := hN u hu t ht
  have e1 : a u t • ψ u t N
      = A N (ψ u t N) - (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    abel
  have hAψ : ‖A N (ψ u t N)‖ ≤ C :=
    ((A N).le_opNorm _).trans (by rw [hp, mul_one]; exact hAN)
  calc ‖a u t‖ = ‖a u t • ψ u t N‖ := by rw [norm_smul, hp, mul_one]
    _ = ‖A N (ψ u t N) - (A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ := by
        rw [e1]
    _ ≤ ‖A N (ψ u t N)‖ + ‖(A N - a u t • ContinuousLinearMap.id ℂ (H N)) (ψ u t N)‖ :=
        norm_sub_le _ _
    _ ≤ C + ε := add_le_add hAψ hd

end Generic

/-! ### Static setting: one polynomial, one finite product (uniform on `𝒰_R`) -/

section Static

variable {L κ : ℝ} [Fact (0 < L)]

/-- One balanced polynomial `f` as a `GoodFactor` for the static setting, with constants `C = K = coeffNorm f`. -/
theorem static_poly_good (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) {f : Sym} (hf : Balanced f) :
    GoodFactor (H := fun n => HN L (n + 1))
      (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g)
      (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint)
      (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (coeffNorm f) (coeffNorm f) f := by
  refine ⟨Filter.Eventually.of_forall fun n => FullWickH1.quantization_coeff_bound (N := n + 1)
      (Nat.succ_pos n) (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) hf,
    Filter.Eventually.of_forall fun n => (FullWickH8.norm_adjoint_eq _).trans_le
      (FullWickH1.quantization_coeff_bound (N := n + 1) (Nat.succ_pos n)
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) hf),
    fun u hu t _ => FullWickH8.chart_evalSym_norm_le hκ hu.1 f,
    FullWickH8.static_poly_pair hκ hU Tb R hf⟩

/-- **Ordered product of balanced polynomials (static, on `𝒰_R`).** For a finite list `fs` of balanced polynomials,
`W^q_N(f_1) ⋯ W^q_N(f_k)` has the uniform strong symbol `f_1(w(u)) ⋯ f_k(w(u))` on `𝒰_R`, with adjoint the
reversed product of adjoints and the conjugate symbol. Constants: the maxima of `coeffNorm f_i`. -/
theorem static_prod_pair (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (fs : List Sym)
    (hfs : ∀ g ∈ fs, Balanced g) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => (fs.map fun g => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).prod)
      (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint).reverse).prod)
      (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
      (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod) := by
  obtain ⟨C, K, hC, hK, hgood⟩ := exists_common_good (H := fun n => HN L (n + 1))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint)
    (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) fs
    (fun g hg => ⟨coeffNorm g, coeffNorm g, coeffNorm_nonneg' g, coeffNorm_nonneg' g,
      static_poly_good hκ hU Tb R (hfs g hg)⟩)
  exact (pair_list_prod (H := fun n => HN L (n + 1))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint)
    (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) C K hC hK fs hgood).1

/-- **Norm-close ordered products of balanced polynomials (static).** Every uniformly norm-close normalized
preparation `ψ'` of the static product state keeps the static pair of the product, with the same product symbol. -/
theorem static_prod_normClose (hκ : 0 < κ) {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (fs : List Sym)
    (hfs : ∀ g ∈ fs, Balanced g) {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)}
    (hprep : IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
      (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => (fs.map fun g => BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).prod)
      (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
        (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint).reverse).prod)
      (UR (L := L) R) Tb ψ'
      (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod) := by
  obtain ⟨C, K, hC, hK, hgood⟩ := exists_common_good (H := fun n => HN L (n + 1))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint)
    (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) fs
    (fun g hg => ⟨coeffNorm g, coeffNorm g, coeffNorm_nonneg' g, coeffNorm_nonneg' g,
      static_poly_good hκ hU Tb R (hfs g hg)⟩)
  obtain ⟨hpair, hnorm, hadj, hsym⟩ := pair_list_prod (H := fun n => HN L (n + 1))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint)
    (fun (g : Sym) (u : L2T L) (_ : Θ) => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g)
    (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) C K hC hK fs hgood
  exact FullWickH7.hasUniformPairT_of_normClose (H := fun n => HN L (n + 1))
    (C := C ^ fs.length) (K := K ^ fs.length) hnorm hadj hsym hpair hprep.2

end Static

/-! ### Dynamic setting: one polynomial, one finite product (along a trajectory and a time box) -/

section Dynamic

variable {L κ : ℝ} [Fact (0 < L)]

/-- One balanced polynomial `f` as a `GoodFactor` for the dynamic setting, with constants `C = K = coeffNorm f`.
The symbol bound is derived from the strong symbol (`symbol_le_of_strong_bound`), since the time-evolved
preparations are normalized (`FullWickH9.dyn_prep_norm`). -/
theorem dyn_poly_good (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) {f : Sym} (hf : Balanced f) :
    GoodFactor (H := fun n => HN L (1 + n))
      (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G g)
      (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G g).adjoint)
      (fun (g : Sym) (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) g)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (coeffNorm f) (coeffNorm f) f := by
  have hpair := FullWickH9.dyn_poly_pair hκ F G D u hu R lo hi ψ hψ hf
  have hA : ∀ᶠ n : ℕ in atTop,
      ‖BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f‖ ≤ coeffNorm f :=
    Filter.Eventually.of_forall fun n => FullWickH1.quantization_coeff_bound (N := 1 + n) (by omega)
      (ReconstructionR33m.basis (L := L) hκ n) G hf
  have hA' : ∀ᶠ n : ℕ in atTop,
      ‖(BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) G f).adjoint‖
        ≤ coeffNorm f :=
    Filter.Eventually.of_forall fun n => (FullWickH8.norm_adjoint_eq _).trans_le
      (FullWickH1.quantization_coeff_bound (N := 1 + n) (by omega)
        (ReconstructionR33m.basis (L := L) hκ n) G hf)
  have hψN : ∀ᶠ n : ℕ in atTop, ∀ _ ∈ (Set.univ : Set Unit), ∀ t ∈ TimeBox R lo hi,
      ‖ReconstructionR33m.U (L := L) hκ R t n (ψ n)‖ = 1 :=
    Filter.Eventually.of_forall fun n _ _ t _ => FullWickH9.dyn_prep_norm hκ hψ R n t
  have hsym := symbol_le_of_strong_bound (H := fun n => HN L (1 + n))
    (A := fun n => BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G f)
    (ψ := fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
    (a := fun (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) f)
    hA hψN hpair.1
  exact ⟨hA, hA', fun _ hu' t ht => hsym () hu' t ht, hpair⟩

/-- **Ordered product of balanced polynomials (dynamic).** For a finite list `fs` of balanced polynomials, along the
fixed trajectory `u` and the time box `TimeBox R lo hi`, the ordered product `W^G_N(f_1) ⋯ W^G_N(f_k)` (index `1+n`)
has the uniform strong symbol `f_1(w(u,t)) ⋯ f_k(w(u,t))`, with the reversed product of adjoints and the conjugate
symbol. The gauge `G` and the input `D` are those of the frozen dynamic clauses. -/
theorem dyn_prod_pair (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge)
    (D : RD8362E5EBInput hκ F G) (u : Def033HierarchyR24m.Smooth L)
    (hu : ‖Def033HierarchyR24m.physical u‖ = 1) (R : Finset ℕ) (lo hi : ↥R → ℝ)
    (ψ : ∀ n : ℕ, HN L (1 + n)) (hψ : Preparation u ψ) (fs : List Sym) (hfs : ∀ g ∈ fs, Balanced g) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => (fs.map fun g => BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G g).prod)
      (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
        (ReconstructionR33m.basis (L := L) hκ n) G g).adjoint).reverse).prod)
      (Set.univ : Set Unit) (TimeBox R lo hi)
      (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
      (fun (_ : Unit) (t : ℕ → ℝ) =>
        (fs.map fun g => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) g).prod) := by
  obtain ⟨C, K, hC, hK, hgood⟩ := exists_common_good (H := fun n => HN L (1 + n))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G g).adjoint)
    (fun (g : Sym) (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) g)
    (Set.univ : Set Unit) (TimeBox R lo hi)
    (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n)) fs
    (fun g hg => ⟨coeffNorm g, coeffNorm g, coeffNorm_nonneg' g, coeffNorm_nonneg' g,
      dyn_poly_good hκ F G D u hu R lo hi ψ hψ (hfs g hg)⟩)
  exact (pair_list_prod (H := fun n => HN L (1 + n))
    (fun (g : Sym) (n : ℕ) => BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G g)
    (fun (g : Sym) (n : ℕ) => (BalancedWickDefinition.quantization
      (ReconstructionR33m.basis (L := L) hκ n) G g).adjoint)
    (fun (g : Sym) (_ : Unit) (t : ℕ → ℝ) => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) g)
    (Set.univ : Set Unit) (TimeBox R lo hi)
    (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n)) C K hC hK fs hgood).1

end Dynamic

/-! ### The three new Props (named as in FullWickH10, with the same named inputs) -/

section Clauses

variable (L κ : ℝ) [Fact (0 < L)]

/-- **Static polynomial products on `𝒰_R`** (printed wick_calculus.tex:86-88). For every finite list of balanced
polynomials `f_1, …, f_k`, the ordered product `W^q_N(f_1) ⋯ W^q_N(f_k)` has the uniform strong symbol
`f_1(w(u)) ⋯ f_k(w(u))` on `𝒰_R`, and its adjoint the conjugate. Parameter predicate `UniformStatic hκ j q`
(printed R-D2F4CE8F), as in `StaticClause`. -/
def StaticPolyProductClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (fs : List Sym), (∀ g ∈ fs, Balanced g) →
      HasUniformPairT (H := fun n => HN L (n + 1))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint).reverse).prod)
        (UR (L := L) R) Tb (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u)
        (fun (u : L2T L) (_ : Θ) =>
          (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod)

/-- **Norm-close static polynomial products** (printed wick_calculus.tex:88-89, "uniformly norm-close preparations
preserve the static uniform statements", applied to the ordered products). Same parameters as
`StaticPolyProductClause`, and the preparation `ψ'` is uniformly norm-close to the static product state. -/
def StaticPolyProductNormCloseClause (hκ : 0 < κ) : Prop :=
  ∀ {j : ℕ → ℕ} {q : UniformStaticR49b.SectorGauge}, UniformStatic (L := L) hκ j q →
    ∀ {Θ : Type} (Tb : Set Θ) (R : ℝ) (fs : List Sym), (∀ g ∈ fs, Balanced g) →
      ∀ {ψ' : L2T L → Θ → ∀ n : ℕ, HN L (n + 1)},
        IsNormClosePrepT (H := fun n => HN L (n + 1)) ψ'
          (fun (u : L2T L) (_ : Θ) n => UniformStaticR49b.product n u) (UR (L := L) R) Tb →
        HasUniformPairT (H := fun n => HN L (n + 1))
          (fun n => (fs.map fun g => BalancedWickDefinition.quantization
            (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).prod)
          (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
            (Def044D1SpectralR51a.basis (L := L) hκ n) (staticGauge q) g).adjoint).reverse).prod)
          (UR (L := L) R) Tb ψ'
          (fun (u : L2T L) (_ : Θ) => (fs.map fun g => evalSym ((Def021ChartR41b.chart L κ hκ).Φ u) g).prod)

/-- **Dynamic polynomial products along hierarchy trajectories** (printed wick_calculus.tex:84-88). For every smooth
trajectory `u` with `‖physical u‖ = 1`, every compact joint-time box `TimeBox R lo hi`, every norm-close
preparation `ψ` (`Preparation u ψ`), and every finite list of balanced polynomials, the ordered product
`W^G_N(f_1) ⋯ W^G_N(f_k)` has the strong symbol `f_1(w(u,t)) ⋯ f_k(w(u,t))` and its adjoint the conjugate. The gauge
`G` and the input `D : RD8362E5EBInput hκ F G` are those of the frozen FullWickH10 dynamic clauses. -/
def DynamicPolyProductClause (hκ : 0 < κ) : Prop :=
  ∀ (F : ActualModelTargetR53a.HigherFlows L κ) (G : Gauge) (D : RD8362E5EBInput hκ F G)
    (u : Def033HierarchyR24m.Smooth L), ‖Def033HierarchyR24m.physical u‖ = 1 →
    ∀ (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n)), Preparation u ψ →
    ∀ (fs : List Sym), (∀ g ∈ fs, Balanced g) →
      HasUniformPairT (H := fun n => HN L (1 + n))
        (fun n => (fs.map fun g => BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) G g).prod)
        (fun n => ((fs.map fun g => (BalancedWickDefinition.quantization
          (ReconstructionR33m.basis (L := L) hκ n) G g).adjoint).reverse).prod)
        (Set.univ : Set Unit) (TimeBox R lo hi)
        (fun (_ : Unit) (t : ℕ → ℝ) n => ReconstructionR33m.U (L := L) hκ R t n (ψ n))
        (fun (_ : Unit) (t : ℕ → ℝ) =>
          (fs.map fun g => evalSym ((ReconstructionR33m.w hκ F u R t : ℤ → ℂ)) g).prod)

theorem static_poly_product_clause (hκ : 0 < κ) : StaticPolyProductClause L κ hκ := by
  intro j q hU Θ Tb R fs hfs
  exact static_prod_pair hκ hU Tb R fs hfs

theorem static_poly_product_normClose_clause (hκ : 0 < κ) :
    StaticPolyProductNormCloseClause L κ hκ := by
  intro j q hU Θ Tb R fs hfs ψ' hprep
  exact static_prod_normClose hκ hU Tb R fs hfs hprep

theorem dynamic_poly_product_clause (hκ : 0 < κ) : DynamicPolyProductClause L κ hκ := by
  intro F G D u hu R lo hi ψ hψ fs hfs
  exact dyn_prod_pair hκ F G D u hu R lo hi ψ hψ fs hfs

end Clauses

end QuantumNLS.FullWickH13

#print axioms QuantumNLS.FullWickH13.static_poly_good
#print axioms QuantumNLS.FullWickH13.static_prod_pair
#print axioms QuantumNLS.FullWickH13.static_prod_normClose
#print axioms QuantumNLS.FullWickH13.dyn_poly_good
#print axioms QuantumNLS.FullWickH13.dyn_prod_pair
#print axioms QuantumNLS.FullWickH13.static_poly_product_clause
#print axioms QuantumNLS.FullWickH13.static_poly_product_normClose_clause
#print axioms QuantumNLS.FullWickH13.dynamic_poly_product_clause
