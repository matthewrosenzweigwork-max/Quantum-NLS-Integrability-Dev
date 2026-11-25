import QuantumNLS.FullWickO1
import QuantumNLS.FullWickH4
import QuantumNLS.FullWickH5

/-! FullWickO2 (opus_tensor, R-140AE34B `thm:full-wick`, Stage 3 item 4: uniformity over `𝒰_R`).

Source: `source-text/chapters/core/wick_calculus.tex:82-84`
  "For the Q06 gauge, the strong symbol and its adjoint are $f(w(u))$ and its conjugate, uniformly on
   every fixed $\mathcal U_R$."
and the proof, `wick_calculus.tex:186-188`: "Uniform generator and symbol bounds control every prefix.
Theorem~\ref{thm:uniform-static} therefore gives uniform strong symbols on $\mathcal U_R$."

The uniform clause comes from the static input, used as a predicate on the PARAMETERS `(j, q)`:
`UniformStaticR49b.UniformStatic hκ j q` (R-D2F4CE8F, printed `uniform_static.tex:2-32`; discharged at the
selected Q06 witnesses by `UniformStaticR49b.selected_uniform_static`, cf. `FullWickH5.static_discharged`).
Its errors are `cartesianError` / `phaseError` over `𝒰_R = RetargetRoughR48b.unitBall R` with the product
state `ψ = UniformStaticR49b.product n u = u^{⊗(n+1)}`. This module proves:

* `cartesianError_eq`, `phaseError_eq`: each static error is EXACTLY the sum of the two residuals of
  `FullWickH4.HasUniformStrongT` (operator and adjoint), at `ψ u t n = product n u`.
* `cartesian_uniform_pair`: from `UniformStatic hκ j q`, for every `R`, every pair `(a, b)`, every time type
  `Θ` and time set `Tb`, the pair `(E^q_{ab}, (E^q_{ab})^*)` is a `FullWickH4.HasUniformPairT` on `𝒰_R`
  with symbol `z_a conj(z_b)`, `z = w(u)` (the symbol does not depend on the time point).
* `phase_uniform_pair`: for `a ≠ b` and `α > 0`, the same for `(W^q_{ab}, (W^q_{ab})^*)` on
  `{u ∈ 𝒰_R | α ≤ |w_a(u)|², α ≤ |w_b(u)|²}` with symbol the printed phase, equal to
  `z_a conj(z_b) / sqrt(|z_a|² |z_b|²)` there (`phase_value_sqrt`).
* `wick_uniform_pair`: the item-2 form: `(W^q_N(c_{ab}), W^q_N(c_{ba}))` (DEF-032 quantization, gauge
  `FullWickO1.staticGauge q`) has the uniform strong symbol `f(w(u))` with `f = bilinearPoly a b`.
* Uniform bounds for the telescoping step (`FullWickH4.pair_mul`): `norm_E_le`, `norm_E_adjoint_le`,
  `norm_W_le`, `norm_W_adjoint_le`, `norm_symbol_le`, `norm_phase`.
* `wick_generator_pair_RD`: the R-8362E5EB dynamic generator pair (`FullWickH5.generator_pair`) rewritten
  through `FullWickO1.gauge_conjugation_RD` to the DEF-032 operators `W^q_N(c_{ab})`, `W^q_N(c_{ba})`.

Standard axioms only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.FullWickO2

open QuantumNLS.FullWickH4 (HasUniformStrongT HasUniformPairT)
open QuantumNLS.FullWickO1 (bilinear bilinearPoly staticGauge)
open QuantumNLS.UniformStaticR49b (SectorGauge UniformStatic cartesianError phaseError supMax
  maxWithZero pairs eligible symbol phase action product)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (BetheBasis HN)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed class `𝒰_R` of the static input (`‖u‖₂ = 1`, DEF-002 `H¹` norm at most `R`). -/
abbrev UR (R : ℝ) : Set (L2T L) := RetargetRoughR48b.unitBall (L := L) R

theorem UR_mono {R R' : ℝ} (h : R ≤ R') : UR (L := L) R ⊆ UR (L := L) R' := by
  rintro u ⟨hu, v, hv, hvR⟩
  exact ⟨hu, v, hv, hvR.trans h⟩

/-! ### The static errors are the `HasUniformStrongT` residuals -/

theorem residual_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V →L[ℂ] V)
    (z : ℂ) (v : V) : (A - z • ContinuousLinearMap.id ℂ V) v = A v - z • v := rfl

/-- `cartesianError` is exactly the operator residual plus the adjoint residual of
`HasUniformPairT` at the product state. -/
theorem cartesianError_eq (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) :
    cartesianError (L := L) hκ q n u p =
      ‖(UniformStaticR49b.E hκ q n p - symbol hκ u p • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1))
          (product n u)‖ +
        ‖((UniformStaticR49b.E hκ q n p).adjoint -
            conj (symbol hκ u p) • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u)‖ := by
  rw [residual_apply, residual_apply]
  rfl

/-- `phaseError` is exactly the operator residual plus the adjoint residual of `HasUniformPairT`. -/
theorem phaseError_eq (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) :
    phaseError (L := L) hκ q n u p =
      ‖(UniformStaticR49b.W hκ q n p - (phase hκ u p).1 • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1))
          (product n u)‖ +
        ‖((UniformStaticR49b.W hκ q n p).adjoint -
            conj (phase hκ u p).1 • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u)‖ := by
  rw [residual_apply, residual_apply]
  rfl

/-! ### Uniform bounds -/

theorem norm_product (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1) : ‖(product n u : HN L (n + 1))‖ = 1 :=
  UniformProjR01Bridge.norm_wvec u hu

theorem norm_E_le (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (p : ℤ × ℤ) :
    ‖UniformStaticR49b.E (L := L) hκ q n p‖ ≤ 1 := by
  rw [UniformStaticBridgeR50b.cartesian_eq_projective_physical]
  exact CartesianOccupationTransfer.physical_norm_le _ _ _ _

theorem norm_E_adjoint_le (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (p : ℤ × ℤ) :
    ‖(UniformStaticR49b.E (L := L) hκ q n p).adjoint‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_E_le hκ q n p

theorem norm_retarget_physical_le {N : ℕ} (B : BetheBasis L N)
    (A : OccupationHilbert.H N →L[ℂ] OccupationHilbert.H N) (hA : ‖A‖ ≤ 1) :
    ‖RetargetPhysicalR48b.physical B A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => ?_
  rw [RetargetPhysicalR48b.physical_apply, LinearIsometryEquiv.norm_map]
  calc ‖A (RetargetEdgeR48b.J B ψ)‖ ≤ ‖A‖ * ‖RetargetEdgeR48b.J B ψ‖ := A.le_opNorm _
    _ ≤ 1 * ‖RetargetEdgeR48b.J B ψ‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = 1 * ‖ψ‖ := by rw [LinearIsometryEquiv.norm_map]

theorem norm_W_le (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (p : ℤ × ℤ) :
    ‖UniformStaticR49b.W (L := L) hκ q n p‖ ≤ 1 :=
  norm_retarget_physical_le _ _ (FiniteCellGauge.W_norm_le _ _ _)

theorem norm_W_adjoint_le (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (p : ℤ × ℤ) :
    ‖(UniformStaticR49b.W (L := L) hκ q n p).adjoint‖ ≤ 1 := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_W_le hκ q n p

theorem norm_symbol_le (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (p : ℤ × ℤ) :
    ‖symbol hκ u p‖ ≤ 1 := by
  rw [symbol, norm_mul, Complex.norm_conj]
  calc _ ≤ 1 * 1 := mul_le_mul (RetargetStageR48b.coordinate_le_one hκ u hu p.1)
        (RetargetStageR48b.coordinate_le_one hκ u hu p.2) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_phase (hκ : 0 < κ) (u : L2T L) (p : ℤ × ℤ) : ‖(phase (L := L) hκ u p).1‖ = 1 :=
  (phase hκ u p).2

theorem residual_le_two {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (hA : ‖A‖ ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) (v : V) (hv : ‖v‖ = 1) :
    ‖A v - z • v‖ ≤ 2 := by
  calc ‖A v - z • v‖ ≤ ‖A v‖ + ‖z • v‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖v‖ + ‖z‖ * ‖v‖ := add_le_add (A.le_opNorm v) (norm_smul_le _ _)
    _ ≤ 1 * 1 + 1 * 1 := by rw [hv]; gcongr
    _ = 2 := by norm_num

theorem cartesianError_le_four (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1)
    (p : ℤ × ℤ) : cartesianError (L := L) hκ q n u p ≤ 4 := by
  have hz := norm_symbol_le hκ u hu p
  have hz' : ‖conj (symbol hκ u p)‖ ≤ 1 := by rw [Complex.norm_conj]; exact hz
  have h1 := residual_le_two _ (norm_E_le hκ q n p) _ hz _ (norm_product n u hu)
  have h2 := residual_le_two _ (norm_E_adjoint_le hκ q n p) _ hz' _ (norm_product n u hu)
  rw [cartesianError]
  linarith

theorem phaseError_le_four (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1)
    (p : ℤ × ℤ) : phaseError (L := L) hκ q n u p ≤ 4 := by
  have hz : ‖(phase hκ u p).1‖ ≤ 1 := (norm_phase hκ u p).le
  have hz' : ‖conj (phase hκ u p).1‖ ≤ 1 := by rw [Complex.norm_conj]; exact hz
  have h1 := residual_le_two _ (norm_W_le hκ q n p) _ hz _ (norm_product n u hu)
  have h2 := residual_le_two _ (norm_W_adjoint_le hκ q n p) _ hz' _ (norm_product n u hu)
  rw [phaseError]
  linarith

/-! ### Extracting uniform bounds from the static suprema -/

/-- Every member of a uniformly bounded family is dominated by the static `supMax`. -/
theorem le_supMax {X P : Type*} (S : Set X) (test : X → Finset P) (error : X → P → ℝ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ u ∈ S, ∀ p ∈ test u, error u p ≤ B) {u : X} (hu : u ∈ S) {p : P}
    (hp : p ∈ test u) : error u p ≤ supMax S test error := by
  have h1 : error u p ≤ maxWithZero (test u) (error u) :=
    Finset.le_sup' id (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))
  refine h1.trans (le_csSup ⟨B, ?_⟩ (Set.mem_insert_of_mem _ ⟨u, hu, rfl⟩))
  rintro x hx
  rcases Set.mem_insert_iff.1 hx with rfl | ⟨v, hv, rfl⟩
  · exact hB0
  · exact UniformStaticR49b.maxWithZero_le _ _ hB0 (hB v hv)

/-- From a vanishing bounded supremum to an eventual uniform bound on a subclass `T ⊆ S`, for a pair
that is eventually tested at every member of `T`. -/
theorem eventually_error_le {X P : Type*} {S T : Set X} (hTS : T ⊆ S) {test : ℕ → X → Finset P}
    {error : ℕ → X → P → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n, ∀ u ∈ S, ∀ p ∈ test n u, error n u p ≤ B)
    (h : Tendsto (fun n => supMax S (test n) (error n)) atTop (𝓝 0)) (p : P)
    (hp : ∀ᶠ n in atTop, ∀ u ∈ T, p ∈ test n u) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ T, error n u p ≤ ε := by
  intro ε hε
  filter_upwards [h.eventually (gt_mem_nhds hε), hp] with n h1 h2
  intro u hu
  exact (le_supMax S (test n) (error n) hB0 (hB n) (hTS hu) (h2 u hu)).trans h1.le

/-- A fixed pair is eventually in the active set `I_{j(N)} × I_{j(N)}`. -/
theorem eventually_mem_pairs {j : ℕ → ℕ} (hj : Tendsto j atTop atTop) (a b : ℤ) :
    ∀ᶠ n in atTop, (a, b) ∈ pairs (j (n + 1)) := by
  have hj' : Tendsto (fun n => j (n + 1)) atTop atTop := hj.comp (tendsto_add_atTop_nat 1)
  filter_upwards [tendsto_atTop.1 hj' (max a.natAbs b.natAbs)] with n hn
  have h1 : (a.natAbs : ℤ) ≤ (j (n + 1) : ℤ) := by exact_mod_cast le_trans (le_max_left _ _) hn
  have h2 : (b.natAbs : ℤ) ≤ (j (n + 1) : ℤ) := by exact_mod_cast le_trans (le_max_right _ _) hn
  have ha := abs_le.1 ((Int.abs_eq_natAbs a).trans_le h1)
  have hb := abs_le.1 ((Int.abs_eq_natAbs b).trans_le h2)
  exact UniformStaticR49b.mem_pairs.2 ⟨Finset.mem_Icc.2 ha, Finset.mem_Icc.2 hb⟩

/-- **Uniform Cartesian bound on `𝒰_R`** from the static input. -/
theorem cartesian_uniform (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge)
    (hU : UniformStatic (L := L) hκ j q) (R : ℝ) (a b : ℤ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ UR (L := L) R, cartesianError (L := L) hκ q n u (a, b) ≤ ε := by
  obtain ⟨-, hj, -, hcart, -⟩ := hU
  have hR : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine eventually_error_le (S := UR (L := L) (max R 1)) (UR_mono (le_max_left R 1))
    (test := fun n _ => pairs (j (n + 1))) (error := cartesianError hκ q) (B := 4)
    (by norm_num) (fun n u hu p _ => cartesianError_le_four hκ q n u hu.1 p) (hcart _ hR) (a, b) ?_
  filter_upwards [eventually_mem_pairs hj a b] with n hn
  exact fun _ _ => hn

/-- The phase class of the static input: `u ∈ 𝒰_R` with both actions at least `α`. -/
def phaseClass (hκ : 0 < κ) (R α : ℝ) (a b : ℤ) : Set (L2T L) :=
  {u | u ∈ UR (L := L) R ∧ α ≤ action hκ u a ∧ α ≤ action hκ u b}

/-- **Uniform phase bound on the phase class** from the static input (`a ≠ b`, `α > 0`). -/
theorem phase_uniform (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge)
    (hU : UniformStatic (L := L) hκ j q) (R α : ℝ) (hα : 0 < α) (a b : ℤ) (hab : a ≠ b) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ u ∈ phaseClass (L := L) hκ R α a b,
      phaseError (L := L) hκ q n u (a, b) ≤ ε := by
  obtain ⟨-, hj, -, -, hph⟩ := hU
  have hR : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hT : phaseClass (L := L) hκ R α a b ⊆ UR (L := L) (max R 1) :=
    fun u hu => UR_mono (le_max_left R 1) hu.1
  refine eventually_error_le (S := UR (L := L) (max R 1)) hT
    (test := fun n => eligible hκ (j (n + 1)) α) (error := phaseError hκ q) (B := 4) (by norm_num)
    (fun n u hu p _ => phaseError_le_four hκ q n u hu.1 p) (hph _ hR α hα).1 (a, b) ?_
  filter_upwards [eventually_mem_pairs hj a b] with n hn
  intro u hu
  exact Finset.mem_filter.2 ⟨hn, hab, hu.2.1, hu.2.2⟩

/-! ### The `HasUniformPairT` form (`FullWickH4`) -/

/-- **Item 4 (Cartesian generators).** From the static input on the parameters `(j, q)`: for every
`R`, pair `(a, b)`, time type `Θ` and time set `Tb`, `(E^q_{ab}, (E^q_{ab})^*)` is a uniform strong-symbol
pair on `𝒰_R` at the product state, with symbol `z_a conj(z_b)`, `z = w(u)`. -/
theorem cartesian_uniform_pair (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge)
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (a b : ℤ) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => UniformStaticR49b.E hκ q n (a, b)) (fun n => (UniformStaticR49b.E hκ q n (a, b)).adjoint)
      (UR (L := L) R) Tb (fun u (_ : Θ) n => product n u) (fun u (_ : Θ) => symbol hκ u (a, b)) := by
  have h := cartesian_uniform hκ j q hU R a b
  constructor
  · intro ε hε
    filter_upwards [h ε hε] with n hn
    intro u hu t _
    have e := cartesianError_eq hκ q n u (a, b)
    have h0 := hn u hu
    have h2 := norm_nonneg (((UniformStaticR49b.E hκ q n (a, b)).adjoint -
      conj (symbol hκ u (a, b)) • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u))
    change ‖(UniformStaticR49b.E hκ q n (a, b) -
      symbol hκ u (a, b) • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u)‖ ≤ ε
    linarith
  · intro ε hε
    filter_upwards [h ε hε] with n hn
    intro u hu t _
    have e := cartesianError_eq hκ q n u (a, b)
    have h0 := hn u hu
    have h1 := norm_nonneg ((UniformStaticR49b.E hκ q n (a, b) -
      symbol hκ u (a, b) • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u))
    change ‖((UniformStaticR49b.E hκ q n (a, b)).adjoint -
      conj (symbol hκ u (a, b)) • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u)‖ ≤ ε
    linarith

/-- **Item 4 (phase generators).** For `a ≠ b` and `α > 0`, `(W^q_{ab}, (W^q_{ab})^*)` is a uniform
strong-symbol pair on the phase class, with symbol the printed phase. -/
theorem phase_uniform_pair (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge)
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R α : ℝ) (hα : 0 < α) (a b : ℤ)
    (hab : a ≠ b) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => UniformStaticR49b.W hκ q n (a, b)) (fun n => (UniformStaticR49b.W hκ q n (a, b)).adjoint)
      (phaseClass (L := L) hκ R α a b) Tb (fun u (_ : Θ) n => product n u)
      (fun u (_ : Θ) => (phase hκ u (a, b)).1) := by
  have h := phase_uniform hκ j q hU R α hα a b hab
  constructor
  · intro ε hε
    filter_upwards [h ε hε] with n hn
    intro u hu t _
    have e := phaseError_eq hκ q n u (a, b)
    have h0 := hn u hu
    have h2 := norm_nonneg (((UniformStaticR49b.W hκ q n (a, b)).adjoint -
      conj (phase hκ u (a, b)).1 • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u))
    change ‖(UniformStaticR49b.W hκ q n (a, b) -
      (phase hκ u (a, b)).1 • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u)‖ ≤ ε
    linarith
  · intro ε hε
    filter_upwards [h ε hε] with n hn
    intro u hu t _
    have e := phaseError_eq hκ q n u (a, b)
    have h0 := hn u hu
    have h1 := norm_nonneg ((UniformStaticR49b.W hκ q n (a, b) -
      (phase hκ u (a, b)).1 • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u))
    change ‖((UniformStaticR49b.W hκ q n (a, b)).adjoint -
      conj (phase hκ u (a, b)).1 • ContinuousLinearMap.id ℂ (HN L (n + 1)) :
        HN L (n + 1) →L[ℂ] HN L (n + 1)) (product n u)‖ ≤ ε
    linarith

/-! ### Symbols in the printed form `f(w(u))` -/

/-- The static Cartesian symbol is `f(w(u))` for `f = z_a z̄_b` (DEF-032 evaluation, chart `w`). -/
theorem symbol_eq_evaluate (hκ : 0 < κ) (u : L2T L) (a b : ℤ) :
    symbol hκ u (a, b) =
      BalancedWickDefinition.evaluate (bilinearPoly a b) ((Def021ChartR41b.chart L κ hκ).Φ u) := by
  rw [FullWickO1.evaluate_bilinearPoly]
  rfl

/-- On the phase class the phase symbol is `z_a conj(z_b) / sqrt(|z_a|² |z_b|²)` (the form of the
R-8362E5EB phase clause). -/
theorem phase_value_sqrt (hκ : 0 < κ) (R α : ℝ) (hα : 0 < α) (a b : ℤ)
    {u : L2T L} (hu : u ∈ phaseClass (L := L) hκ R α a b) :
    (phase hκ u (a, b)).1 =
      symbol hκ u (a, b) /
        ((Real.sqrt (‖RetargetStageR48b.coordinate hκ u a‖ ^ 2 *
          ‖RetargetStageR48b.coordinate hκ u b‖ ^ 2) : ℝ) : ℂ) := by
  have hx : ‖RetargetStageR48b.coordinate hκ u a * RetargetStageR48b.coordinate hκ u b‖ =
      Real.sqrt (‖RetargetStageR48b.coordinate hκ u a‖ ^ 2 *
        ‖RetargetStageR48b.coordinate hκ u b‖ ^ 2) := by
    rw [norm_mul, ← Real.sqrt_sq (mul_nonneg (norm_nonneg (RetargetStageR48b.coordinate hκ u a))
      (norm_nonneg (RetargetStageR48b.coordinate hκ u b)))]
    congr 1
    ring
  rw [UniformStaticR49b.phase_value hκ u (a, b) (lt_of_lt_of_le hα hu.2.1) (lt_of_lt_of_le hα hu.2.2)]
  exact congrArg (fun r : ℝ => symbol hκ u (a, b) / (r : ℂ)) hx

/-- **Item 2 + item 4, Wick form.** The DEF-032 operators `W^q_N(c_{ab})` and `W^q_N(c_{ba})`
(`= W^q_N(c_{ab})^*`) in the static gauge have the uniform strong symbol `f(w(u))`, `f = z_a z̄_b`,
and its conjugate, on `𝒰_R` at the product state. -/
theorem wick_uniform_pair (hκ : 0 < κ) (j : ℕ → ℕ) (q : SectorGauge)
    (hU : UniformStatic (L := L) hκ j q) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (a b : ℤ) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
        (staticGauge q) (bilinear a b))
      (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
        (staticGauge q) (bilinear b a))
      (UR (L := L) R) Tb (fun u (_ : Θ) n => product n u)
      (fun u (_ : Θ) => BalancedWickDefinition.evaluate (bilinearPoly a b)
        ((Def021ChartR41b.chart L κ hκ).Φ u)) := by
  have hE : (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
      (staticGauge q) (bilinear a b)) = fun n => UniformStaticR49b.E hκ q n (a, b) :=
    funext fun n => FullWickO1.gauge_conjugation_static hκ q n (a, b)
  have hE' : (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
      (staticGauge q) (bilinear b a)) = fun n => (UniformStaticR49b.E hκ q n (a, b)).adjoint :=
    funext fun n => (FullWickO1.gauge_conjugation_static_adjoint hκ q n (a, b)).symm
  have hs : (fun u (_ : Θ) => BalancedWickDefinition.evaluate (bilinearPoly a b)
      ((Def021ChartR41b.chart L κ hκ).Φ u)) = fun u (_ : Θ) => symbol hκ u (a, b) :=
    funext fun u => funext fun _ => (symbol_eq_evaluate hκ u a b).symm
  rw [hE, hE', hs]
  exact cartesian_uniform_pair hκ j q hU Tb R a b

/-- Uniform norm bound for the static Wick generators (input to `FullWickH4.pair_mul`). -/
theorem norm_wick_bilinear_le (hκ : 0 < κ) (q : SectorGauge) (n : ℕ) (a b : ℤ) :
    ‖BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
      (staticGauge q) (bilinear a b)‖ ≤ 1 := by
  rw [FullWickO1.gauge_conjugation_static hκ q n (a, b)]
  exact norm_E_le hκ q n (a, b)

/-- Symbol bound on `𝒰_R` for `f(w(u))`, `f = z_a z̄_b` (input to `FullWickH4.pair_mul`). -/
theorem norm_evaluate_bilinear_le (hκ : 0 < κ) (R : ℝ) (a b : ℤ) {u : L2T L}
    (hu : u ∈ UR (L := L) R) :
    ‖BalancedWickDefinition.evaluate (bilinearPoly a b) ((Def021ChartR41b.chart L κ hκ).Φ u)‖ ≤ 1 := by
  rw [← symbol_eq_evaluate]
  exact norm_symbol_le hκ u hu.1 (a, b)

/-- The uniform Wick-generator pair at the selected Q06 witnesses
(`UniformStaticR49b.selected_uniform_static`, schedule `particleStage hκ`, gauge `sectorGauge hκ`).
This is a separate corollary: the theorems above use the static input only on parameters `(j, q)`. -/
theorem wick_uniform_pair_selected (hκ : 0 < κ) {Θ : Type*} (Tb : Set Θ) (R : ℝ) (a b : ℤ) :
    HasUniformPairT (H := fun n => HN L (n + 1))
      (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
        (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) (bilinear a b))
      (fun n => BalancedWickDefinition.quantization (Def044D1SpectralR51a.basis (L := L) hκ n)
        (staticGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) (bilinear b a))
      (UR (L := L) R) Tb (fun u (_ : Θ) n => product n u)
      (fun u (_ : Θ) => BalancedWickDefinition.evaluate (bilinearPoly a b)
        ((Def021ChartR41b.chart L κ hκ).Φ u)) :=
  wick_uniform_pair hκ _ _ (UniformStaticR49b.selected_uniform_static (L := L) hκ) Tb R a b

/-! ### The dynamic generator pair (R-8362E5EB) in Wick form -/

/-- `FullWickH5.generator_pair` rewritten through `FullWickO1.gauge_conjugation_RD`: on a fixed profile,
time box and preparation, `(W^q_N(c_{ab}), W^q_N(c_{ba}))` has the symbol `z_a conj(z_b)`, `z = w(u)(t)`. -/
theorem wick_generator_pair_RD (hκ : 0 < κ) (F : ActualModelTargetR53a.HigherFlows L κ)
    (g : BetheOccupationGauge.Gauge) (D : ReconstructionR33m.RD8362E5EBInput hκ F g)
    (u : Def033HierarchyR24m.Smooth L) (hu : ‖Def033HierarchyR24m.physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ↥R → ℝ) (ψ : ∀ n : ℕ, HN L (1 + n))
    (hψ : ReconstructionR33m.Preparation u ψ) (a b : ℤ) :
    HasUniformPairT (H := fun n => HN L (1 + n))
      (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) g
        (bilinear a b))
      (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) g
        (bilinear b a))
      (Set.univ : Set Unit) (ReconstructionR33m.TimeBox R lo hi)
      (fun (_ : Unit) t n => ReconstructionR33m.U hκ R t n (ψ n))
      (fun (_ : Unit) t => BalancedWickDefinition.evaluate (bilinearPoly a b)
        (ReconstructionR33m.w hκ F u R t)) := by
  have hE : (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) g
      (bilinear a b)) = fun n => ReconstructionR33m.E hκ g n a b :=
    funext fun n => FullWickO1.gauge_conjugation_RD hκ g n a b
  have hE' : (fun n => BalancedWickDefinition.quantization (ReconstructionR33m.basis (L := L) hκ n) g
      (bilinear b a)) = fun n => (ReconstructionR33m.E hκ g n a b).adjoint :=
    funext fun n => (FullWickO1.gauge_conjugation_RD_adjoint hκ g n a b).symm
  have hs : (fun (_ : Unit) t => BalancedWickDefinition.evaluate (bilinearPoly a b)
      (ReconstructionR33m.w hκ F u R t)) =
      fun (_ : Unit) t => ReconstructionR33m.w hκ F u R t a * conj (ReconstructionR33m.w hκ F u R t b) :=
    funext fun _ => funext fun t => FullWickO1.evaluate_bilinearPoly a b _
  rw [hE, hE', hs]
  exact FullWickH5.generator_pair hκ F g D u hu R lo hi ψ hψ a b

end QuantumNLS.FullWickO2

#print axioms QuantumNLS.FullWickO2.cartesianError_eq
#print axioms QuantumNLS.FullWickO2.phaseError_eq
#print axioms QuantumNLS.FullWickO2.norm_E_le
#print axioms QuantumNLS.FullWickO2.norm_E_adjoint_le
#print axioms QuantumNLS.FullWickO2.norm_W_le
#print axioms QuantumNLS.FullWickO2.norm_W_adjoint_le
#print axioms QuantumNLS.FullWickO2.norm_symbol_le
#print axioms QuantumNLS.FullWickO2.norm_phase
#print axioms QuantumNLS.FullWickO2.cartesianError_le_four
#print axioms QuantumNLS.FullWickO2.phaseError_le_four
#print axioms QuantumNLS.FullWickO2.le_supMax
#print axioms QuantumNLS.FullWickO2.eventually_error_le
#print axioms QuantumNLS.FullWickO2.eventually_mem_pairs
#print axioms QuantumNLS.FullWickO2.cartesian_uniform
#print axioms QuantumNLS.FullWickO2.phase_uniform
#print axioms QuantumNLS.FullWickO2.cartesian_uniform_pair
#print axioms QuantumNLS.FullWickO2.phase_uniform_pair
#print axioms QuantumNLS.FullWickO2.symbol_eq_evaluate
#print axioms QuantumNLS.FullWickO2.phase_value_sqrt
#print axioms QuantumNLS.FullWickO2.wick_uniform_pair
#print axioms QuantumNLS.FullWickO2.norm_wick_bilinear_le
#print axioms QuantumNLS.FullWickO2.norm_evaluate_bilinear_le
#print axioms QuantumNLS.FullWickO2.wick_uniform_pair_selected
#print axioms QuantumNLS.FullWickO2.wick_generator_pair_RD

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "QuantumNLS.FullWickO2." ||
        name.toString.startsWith "_private.QuantumNLS.FullWickO2." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          name.components.any (fun c => c.toString == "RegularCut") ||
          name == ``QuantumNLS.UniformStaticR31m.GaugeRetargetingRD51987CAInput ||
          name == ``QuantumNLS.UniformStaticR31m.uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.retarget_and_uniform_static_intermediate ||
          name == ``QuantumNLS.UniformStaticR49b.uniform_static_intermediate then
        throwError "Excluded dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"FullWickO2 aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only; no held identifiers."
