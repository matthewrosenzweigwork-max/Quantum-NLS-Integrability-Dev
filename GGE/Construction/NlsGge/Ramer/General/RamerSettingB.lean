import NlsGge.Ramer.General.RamerSettingA
import NlsGge.Sobolev.CMWeightComparison
import NlsGge.Sobolev.RealBasis
import NlsGge.Sobolev.CMInclusionBasisIndependent
import NlsGge.Sobolev.RectangularBasisChange
import NlsGge.Measure.CountableSupport
import NlsGge.Ramer.ActualHeadLawBridge

/-!
# The general Ramer setting with anisotropic `E` (G0, part B: sections 4-5)

See `NlsGge/Ramer/RAMER_GENERALIZATION_PLAN.md` (section "G0 FINAL SPEC").

* §4 the inclusion `incl : H →L[ℝ] E` (coordinate identity `coord n (incl h) = h_n`, bound,
  injectivity, dense range), the exact Hilbert–Schmidt identity
  `Σ_{(n,j)} ‖incl b_{n,j}‖² = Σ_n tr(M n)/(2 q n)` in the coordinate basis, the
  Hilbert–Schmidt property for every Hilbert basis of `H`, and the tail bound with
  `tailSup → 0` (the replacement of R5's explicit tail estimate).
* §5 the constructors `ofWeights` (isotropic `E`), `ofCoefficients` (the project's `E_s`),
  the coordinate preserving isometry `fullWeightedEquiv`, the regression statements, and
  the documented F05 instance `ofSobolevRates`.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators Topology
open Filter NlsGge.Pilot

namespace NlsGge.Ramer.General

namespace RamerSetting

variable (S : RamerSetting)

/-! ## §4  The inclusion `H → E` -/

theorem hasSum_H (h : S.H) :
    HasSum (fun n => S.cmWeight n * ‖S.hcoord h n‖ ^ 2) (‖h‖ ^ 2) :=
  weightedHilbert_hasSum S.cmWeight (show WeightedHilbert S.cmWeight from h)

theorem hcoord_add (h h' : S.H) (n : ℤ) : S.hcoord (h + h') n = S.hcoord h n + S.hcoord h' n :=
  rfl

theorem hcoord_smul (r : ℝ) (h : S.H) (n : ℤ) : S.hcoord (r • h) n = (r : ℂ) * S.hcoord h n :=
  rfl

theorem hcoord_ext {h h' : S.H} (e : ∀ n, S.hcoord h n = S.hcoord h' n) : h = h' := by
  change (show WeightedHilbert S.cmWeight from h) = (show WeightedHilbert S.cmWeight from h')
  exact Subtype.ext (funext e)

/-- The Hilbert–Schmidt ratio supremum `sup_n tr(M n)/(2 q n)` (finite since `hs`). -/
def ratioSup : ℝ := ⨆ n, S.ratio n

theorem ratio_le_tsum (n : ℤ) : S.ratio n ≤ ∑' m, S.ratio m :=
  S.summable_ratio.le_tsum n (fun m _ => (S.ratio_pos m).le)

theorem bddAbove_ratio : BddAbove (Set.range S.ratio) :=
  ⟨∑' m, S.ratio m, by rintro _ ⟨n, rfl⟩; exact S.ratio_le_tsum n⟩

theorem ratio_le_ratioSup (n : ℤ) : S.ratio n ≤ S.ratioSup :=
  le_ciSup S.bddAbove_ratio n

theorem ratioSup_nonneg : 0 ≤ S.ratioSup :=
  (S.ratio_pos 0).le.trans (S.ratio_le_ratioSup 0)

/-- Termwise bound: `M_n(z,z) ≤ C · 2q_n |z|²` as soon as `tr(M_n)/(2 q_n) ≤ C`. -/
theorem form_le_ratio_mul (n : ℤ) (z : ℂ) (C : ℝ) (hC : S.ratio n ≤ C) :
    (S.M n).form z z ≤ C * (S.cmWeight n * ‖z‖ ^ 2) := by
  have h1 := (S.M n).form_le_tr z
  have hw := S.cmWeight_pos n
  have hw' : S.cmWeight n = 2 * S.q n := rfl
  have e : (S.M n).tr * ‖z‖ ^ 2 = S.ratio n * (S.cmWeight n * ‖z‖ ^ 2) := by
    have hq := (S.q_pos n).ne'
    unfold ratio
    rw [← hw']
    field_simp
  calc (S.M n).form z z ≤ (S.M n).tr * ‖z‖ ^ 2 := h1
    _ = S.ratio n * (S.cmWeight n * ‖z‖ ^ 2) := e
    _ ≤ C * (S.cmWeight n * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg hw.le (sq_nonneg _))

theorem memE_hcoord (h : S.H) : S.memE (S.hcoord h) := by
  refine Summable.of_nonneg_of_le (fun n => (S.M n).form_nonneg _)
    (fun n => S.form_le_ratio_mul n _ _ (S.ratio_le_ratioSup n))
    ((S.hasSum_H h).summable.mul_left _)

/-- The coordinate identity `H → E` as a real linear map. -/
def inclLin : S.H →ₗ[ℝ] S.E where
  toFun h := S.ofSeq (S.hcoord h) (S.memE_hcoord h)
  map_add' h h' := by
    apply S.E_ext; intro n
    rw [S.coord_add]
    simp only [coord_ofSeq, hcoord_add]
  map_smul' r h := by
    apply S.E_ext; intro n
    rw [S.coord_smul]
    simp only [coord_ofSeq, hcoord_smul, RingHom.id_apply]

/-- Termwise-controlled norm bound: if `M_n(y_n,y_n) ≤ C · 2q_n |h_n|²` for all `n`, then
`‖y‖²_E ≤ C ‖h‖²_H`. -/
theorem norm_sq_le_of_termwise (y : S.E) (h : S.H) (C : ℝ)
    (hterm : ∀ n, (S.M n).form (S.coord n y) (S.coord n y) ≤
      C * (S.cmWeight n * ‖S.hcoord h n‖ ^ 2)) :
    ‖y‖ ^ 2 ≤ C * ‖h‖ ^ 2 := by
  rw [S.E_norm_sq, ← (S.hasSum_H h).tsum_eq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hterm (S.summable_form_coord y)
    ((S.hasSum_H h).summable.mul_left C)

theorem inclLin_norm_le (h : S.H) : ‖S.inclLin h‖ ≤ Real.sqrt S.ratioSup * ‖h‖ := by
  have hsq : ‖S.inclLin h‖ ^ 2 ≤ S.ratioSup * ‖h‖ ^ 2 :=
    S.norm_sq_le_of_termwise _ h _ (fun n => by
      simpa only [inclLin, LinearMap.coe_mk, AddHom.coe_mk, coord_ofSeq] using
        S.form_le_ratio_mul n (S.hcoord h n) _ (S.ratio_le_ratioSup n))
  have hr : (Real.sqrt S.ratioSup * ‖h‖) ^ 2 = S.ratioSup * ‖h‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt S.ratioSup_nonneg]
  exact le_of_sq_le_sq (hr ▸ hsq) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))

/-- The inclusion `incl : H →L[ℝ] E` (identity on Fourier coordinates). -/
def incl : S.H →L[ℝ] S.E :=
  S.inclLin.mkContinuous (Real.sqrt S.ratioSup) S.inclLin_norm_le

/-- `coord n (incl h) = h_n`. -/
@[simp] theorem coord_incl (h : S.H) (n : ℤ) : S.coord n (S.incl h) = S.hcoord h n :=
  S.coord_ofSeq (S.hcoord h) (S.memE_hcoord h) n

/-- `‖incl h‖ ≤ √(sup_n tr(M n)/(2 q n)) · ‖h‖`. -/
theorem incl_norm_le (h : S.H) : ‖S.incl h‖ ≤ Real.sqrt S.ratioSup * ‖h‖ :=
  S.inclLin_norm_le h

theorem incl_injective : Function.Injective S.incl := by
  intro h h' e
  apply S.hcoord_ext; intro n
  have := congrArg (S.coord n) e
  simpa only [coord_incl] using this

/-- An element of `H` with prescribed finitely supported coordinates. -/
def hOfFinSeq (z : ℤ → ℂ) (hz : {n | z n ≠ 0}.Finite) : S.H :=
  (⟨z, (weightedCoordinates_mem_l2_iff S.cmWeight (fun n => (S.cmWeight_pos n).le) z).2 (by
    apply summable_of_hasFiniteSupport
    refine hz.subset ?_
    intro n hn
    by_contra h
    apply hn
    have h0 : z n = 0 := by simpa using h
    show S.cmWeight n * ‖z n‖ ^ 2 = 0
    rw [h0]; simp)⟩ : WeightedHilbert S.cmWeight)

@[simp] theorem hcoord_hOfFinSeq (z : ℤ → ℂ) (hz : {n | z n ≠ 0}.Finite) (n : ℤ) :
    S.hcoord (S.hOfFinSeq z hz) n = z n := rfl

/-- `incl` has dense range. -/
theorem incl_denseRange : DenseRange S.incl := by
  intro x
  have hfin : ∀ N : ℕ, {n | (fun n => if n ∈ symmetricModes N then S.coord n x else 0) n ≠ 0}.Finite :=
    fun N => (symmetricModes N).finite_toSet.subset (fun n hn => by
      by_contra h
      apply hn
      simp only [Finset.mem_coe] at h
      simp [h])
  refine mem_closure_of_tendsto (S.projE_tendsto x) (Eventually.of_forall fun N => ?_)
  refine ⟨S.hOfFinSeq _ (hfin N), ?_⟩
  apply S.E_ext; intro n
  rw [coord_incl, coord_projE]
  rfl

/-! ### Hilbert–Schmidt -/

/-- The coordinates of the standard real Hilbert basis of `H`. -/
theorem hcoord_basis (p : ℤ × Fin 2) (m : ℤ) :
    S.hcoord (weightedRealHilbertBasis S.cmWeight p) m =
      (if m = p.1 then Complex.orthonormalBasisOneI p.2 else 0) /
        (Real.sqrt (S.cmWeight m) : ℂ) := by
  rw [weightedRealHilbertBasis_apply]
  exact weightedRealBasisVector_apply S.cmWeight p m

/-- Squared `E`-norm of the image of the basis vector `(n, j)`:
`M(1,1)/(2q_n)` for `j = 0` and `M(i,i)/(2q_n)` for `j = 1`. -/
theorem norm_sq_incl_basis (n : ℤ) (j : Fin 2) :
    ‖S.incl (weightedRealHilbertBasis S.cmWeight (n, j))‖ ^ 2 =
      (S.M n).form (Complex.orthonormalBasisOneI j) (Complex.orthonormalBasisOneI j) /
        S.cmWeight n := by
  rw [S.E_norm_sq, tsum_eq_single n]
  · rw [coord_incl, hcoord_basis]
    simp only [if_true]
    have hw := S.cmWeight_pos n
    have hs : (Real.sqrt (S.cmWeight n) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hw).ne'
    have : Complex.orthonormalBasisOneI j / (Real.sqrt (S.cmWeight n) : ℂ) =
        (((Real.sqrt (S.cmWeight n))⁻¹ : ℝ) : ℂ) * Complex.orthonormalBasisOneI j := by
      rw [div_eq_inv_mul]; push_cast; rfl
    rw [this, ModeForm.form_smul_left, ModeForm.form_smul_right]
    have h2 : ((Real.sqrt (S.cmWeight n))⁻¹) * (((Real.sqrt (S.cmWeight n))⁻¹) *
        (S.M n).form (Complex.orthonormalBasisOneI j) (Complex.orthonormalBasisOneI j)) =
        ((Real.sqrt (S.cmWeight n))⁻¹) ^ 2 * (S.M n).form (Complex.orthonormalBasisOneI j)
          (Complex.orthonormalBasisOneI j) := by ring
    rw [h2, inv_pow, Real.sq_sqrt hw.le]
    ring
  · intro m hm
    rw [coord_incl, hcoord_basis]
    simp [hm, S.form_zero_left]

theorem hasSum_norm_sq_incl_basis :
    HasSum (fun p : ℤ × Fin 2 =>
      ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ ^ 2) (∑' n, S.ratio n) := by
  have hnn : ∀ p : ℤ × Fin 2, 0 ≤ ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ ^ 2 :=
    fun _ => sq_nonneg _
  have hfib : ∀ n : ℤ, ∑' j : Fin 2,
      ‖S.incl (weightedRealHilbertBasis S.cmWeight (n, j))‖ ^ 2 = S.ratio n := by
    intro n
    rw [tsum_fintype, Fin.sum_univ_two, norm_sq_incl_basis, norm_sq_incl_basis]
    have h0 : Complex.orthonormalBasisOneI 0 = 1 := by simp
    have h1 : Complex.orthonormalBasisOneI 1 = Complex.I := by simp
    rw [h0, h1, ModeForm.form_one_one, ModeForm.form_I_I, ← add_div]
    rfl
  have hsum : Summable (fun p : ℤ × Fin 2 =>
      ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ ^ 2) := by
    rw [summable_prod_of_nonneg hnn]
    refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
    simpa only [hfib] using S.summable_ratio
  have := hsum.hasSum
  rwa [hsum.tsum_prod' (fun n => (hasSum_fintype _).summable),
    tsum_congr hfib] at this

/-- The exact coordinate-basis Hilbert–Schmidt identity:
`Σ_{(n,j)} ‖incl b_{n,j}‖² = Σ_n tr(M n)/(2 q n)`. -/
theorem incl_hs_coord :
    HasSum (fun p : ℤ × Fin 2 =>
      ‖S.incl (weightedRealHilbertBasis S.cmWeight p)‖ ^ 2)
      (∑' n, (S.M n).tr / (2 * S.q n)) :=
  S.hasSum_norm_sq_incl_basis

/-- Hilbert–Schmidt identity in every real Hilbert basis of `H`. -/
theorem incl_hs_hasSum {ι : Type*} (b : HilbertBasis ι ℝ S.H) :
    HasSum (fun i : ι => ‖S.incl (b i)‖ ^ 2) (∑' n, (S.M n).tr / (2 * S.q n)) := by
  have h := hasSum_norm_sq_apply_of_real_hilbertBasis (T := S.incl)
    (weightedRealHilbertBasis S.cmWeight) b S.incl_hs_coord.summable
  convert h using 1
  exact S.incl_hs_coord.tsum_eq.symm

/-- `incl : H → E` is Hilbert–Schmidt in every real Hilbert basis of `H`. -/
theorem incl_hs {ι : Type*} (b : HilbertBasis ι ℝ S.H) :
    Summable (fun i : ι => ‖S.incl (b i)‖ ^ 2) :=
  (S.incl_hs_hasSum b).summable

/-! ### Tail bound (replacement of R5's explicit estimate) -/

/-- The `H`-coordinate truncation `P_n : H → H` onto the modes `-n..n`. -/
def headProj (n : ℕ) : S.H →L[ℝ] S.H :=
  weightedRealProjectionContinuous S.cmWeight (symmetricModes n)

theorem hcoord_headProj (n : ℕ) (h : S.H) (m : ℤ) :
    S.hcoord (S.headProj n h) m = if m ∈ symmetricModes n then S.hcoord h m else 0 :=
  weightedRealProjection_apply S.cmWeight (symmetricModes n) h m

/-- `tailSup n = sup_{|m| > n} tr(M m)/(2 q m)`. -/
def tailSup (n : ℕ) : ℝ := ⨆ m : {m : ℤ // m ∉ symmetricModes n}, S.ratio m

theorem ratio_le_tailSup (n : ℕ) {m : ℤ} (hm : m ∉ symmetricModes n) :
    S.ratio m ≤ S.tailSup n :=
  le_ciSup (f := fun m : {m : ℤ // m ∉ symmetricModes n} => S.ratio m)
    ⟨S.ratioSup, by rintro _ ⟨k, rfl⟩; exact S.ratio_le_ratioSup k⟩ ⟨m, hm⟩

theorem tailSup_nonneg (n : ℕ) : 0 ≤ S.tailSup n :=
  Real.iSup_nonneg (fun m => (S.ratio_pos m).le)

/-- `‖incl h - incl (P_n h)‖²_E ≤ tailSup n · ‖h‖²_H`. -/
theorem tail_bound (n : ℕ) (h : S.H) :
    ‖S.incl h - S.incl (S.headProj n h)‖ ^ 2 ≤ S.tailSup n * ‖h‖ ^ 2 := by
  refine S.norm_sq_le_of_termwise _ h _ (fun m => ?_)
  have e : S.coord m (S.incl h - S.incl (S.headProj n h)) =
      S.hcoord h m - (if m ∈ symmetricModes n then S.hcoord h m else 0) := by
    rw [map_sub, coord_incl, coord_incl, hcoord_headProj]
  rw [e]
  by_cases hm : m ∈ symmetricModes n
  · simp only [if_pos hm, sub_self, S.form_zero_left]
    exact mul_nonneg (S.tailSup_nonneg n) (mul_nonneg (S.cmWeight_pos m).le (sq_nonneg _))
  · simp only [if_neg hm, sub_zero]
    exact S.form_le_ratio_mul m _ _ (S.ratio_le_tailSup n hm)

/-- `tailSup n → 0`. -/
theorem tailSup_tendsto : Tendsto S.tailSup atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun n => lt_of_lt_of_le ha (S.tailSup_nonneg n),
    fun a ha => ?_⟩
  have hev : ∀ᶠ m in cofinite, S.ratio m < a / 2 :=
    (S.summable_ratio.tendsto_cofinite_zero).eventually (gt_mem_nhds (by linarith))
  have hfin : {m : ℤ | ¬ S.ratio m < a / 2}.Finite := Filter.eventually_cofinite.1 hev
  have hN : ∀ᶠ N : ℕ in atTop, hfin.toFinset ≤ symmetricModes N :=
    symmetricModes_tendsto.eventually (eventually_ge_atTop _)
  filter_upwards [hN] with N hN
  have : S.tailSup N ≤ a / 2 := by
    refine Real.iSup_le (fun m => ?_) (by linarith)
    by_contra hlt
    rw [not_le] at hlt
    have hmem : (m : ℤ) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact fun h => absurd h (not_lt.2 hlt.le)
    exact m.2 (hN hmem)
  linarith

/-! ## §5  Constructors and regression -/

/-- Isotropic constructor: `E = {x : Σ w_n |x_n|² < ∞}` with `M n = w_n ‖·‖²`.
Note `tr(M n)/(2 q n) = w n / q n`. -/
def ofWeights (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hw : ∀ n, 0 < w n)
    (hs : Summable (fun n => w n / q n)) : RamerSetting where
  q := q
  q_pos := hq
  M := fun n => ModeForm.iso (w n) (hw n)
  hs := by
    refine hs.congr (fun n => ?_)
    show w n / q n = (ModeForm.iso (w n) (hw n)).tr / (2 * q n)
    rw [ModeForm.iso_tr]
    have := (hq n).ne'
    field_simp

theorem ofWeights_ratio (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hw : ∀ n, 0 < w n)
    (hs : Summable (fun n => w n / q n)) (n : ℤ) :
    (ofWeights q w hq hw hs).ratio n = w n / q n := by
  show (ModeForm.iso (w n) (hw n)).tr / (2 * q n) = w n / q n
  rw [ModeForm.iso_tr]
  have := (hq n).ne'
  field_simp

theorem ofWeights_form (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hw : ∀ n, 0 < w n)
    (hs : Summable (fun n => w n / q n)) (n : ℤ) (z : ℂ) :
    ((ofWeights q w hq hw hs).M n).form z z = w n * ‖z‖ ^ 2 :=
  ModeForm.iso_form _ _ _

theorem memE_ofWeights_iff (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hw : ∀ n, 0 < w n)
    (hs : Summable (fun n => w n / q n)) (z : ℤ → ℂ) :
    (ofWeights q w hq hw hs).memE z ↔ Summable (fun n => w n * ‖z n‖ ^ 2) := by
  unfold memE
  simp only [ofWeights_form]

theorem memE_ofWeights_of_weighted (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) [hwf : Fact (∀ n, 0 < w n)]
    (hs : Summable (fun n => w n / q n)) (x : WeightedRealHilbert w) :
    (ofWeights q w hq hwf.out hs).memE (fun n => (show WeightedHilbert w from x) n) := by
  rw [memE_ofWeights_iff]
  exact (weightedHilbert_hasSum w (show WeightedHilbert w from x)).summable

/-- For the isotropic setting, `E` is isometric to `WeightedRealHilbert w` through the
identity on Fourier coordinates. -/
def ofWeightsEquiv (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) [hwf : Fact (∀ n, 0 < w n)]
    (hs : Summable (fun n => w n / q n)) :
    WeightedRealHilbert w ≃ₗᵢ[ℝ] (ofWeights q w hq hwf.out hs).E where
  toLinearEquiv :=
    { toFun := fun x => (ofWeights q w hq hwf.out hs).ofSeq
        (fun n => (show WeightedHilbert w from x) n) (by
          rw [memE_ofWeights_iff]
          exact (weightedHilbert_hasSum w (show WeightedHilbert w from x)).summable)
      map_add' := fun x y => by
        apply (ofWeights q w hq hwf.out hs).E_ext; intro n
        rw [map_add]
        simp only [coord_ofSeq]; rfl
      map_smul' := fun r x => by
        apply (ofWeights q w hq hwf.out hs).E_ext; intro n
        rw [coord_smul]
        simp only [coord_ofSeq, RingHom.id_apply]; rfl
      invFun := fun y => (⟨fun n => (ofWeights q w hq hwf.out hs).coord n y,
        (weightedCoordinates_mem_l2_iff w (fun n => (hwf.out n).le) _).2
          ((memE_ofWeights_iff q w hq hwf.out hs _).1
            ((ofWeights q w hq hwf.out hs).memE_coord y))⟩ : WeightedHilbert w)
      left_inv := fun x => by
        apply Subtype.ext; funext n
        exact coord_ofSeq _ _ _ n
      right_inv := fun y => by
        apply (ofWeights q w hq hwf.out hs).E_ext; intro n
        exact coord_ofSeq _ _ _ n }
  norm_map' := fun x => by
    have h1 := ((ofWeights q w hq hwf.out hs).E_norm_sq_hasSum
      ((ofWeights q w hq hwf.out hs).ofSeq (fun n => (show WeightedHilbert w from x) n) (by
          rw [memE_ofWeights_iff]
          exact (weightedHilbert_hasSum w (show WeightedHilbert w from x)).summable)))
    have h2 := weightedHilbert_hasSum w (show WeightedHilbert w from x)
    have h3 : (fun n => ((ofWeights q w hq hwf.out hs).M n).form
        ((ofWeights q w hq hwf.out hs).coord n ((ofWeights q w hq hwf.out hs).ofSeq
          (fun n => (show WeightedHilbert w from x) n) (by
            rw [memE_ofWeights_iff]
            exact (weightedHilbert_hasSum w (show WeightedHilbert w from x)).summable)))
        ((ofWeights q w hq hwf.out hs).coord n ((ofWeights q w hq hwf.out hs).ofSeq
          (fun n => (show WeightedHilbert w from x) n) (by
            rw [memE_ofWeights_iff]
            exact (weightedHilbert_hasSum w (show WeightedHilbert w from x)).summable)))) =
        fun n => w n * ‖(show WeightedHilbert w from x) n‖ ^ 2 := by
      funext n
      rw [coord_ofSeq, ofWeights_form]
    rw [h3] at h1
    have h4 := h1.unique h2
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h4

theorem coord_ofWeightsEquiv (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) [hwf : Fact (∀ n, 0 < w n)]
    (hs : Summable (fun n => w n / q n)) (x : WeightedRealHilbert w) (n : ℤ) :
    (ofWeights q w hq hwf.out hs).coord n (ofWeightsEquiv q w hq hs x) =
      (show WeightedHilbert w from x) n := by
  apply coord_ofSeq
  exact memE_ofWeights_of_weighted q w hq hs x

section Coefficients

variable {lower upper : ℝ}

theorem summable_fullModeWeight_div_sourceRate (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    Summable (fun n : ℤ => fullModeWeight c s n / sourceRate c n) := by
  refine (NlsGge.Measure.summable_japaneseBracket_sobolev_decay s hs).congr (fun n => ?_)
  have := (sourceRate_pos c n).ne'
  unfold fullModeWeight
  field_simp

/-- The project's `E_s` setting: rates `q = sourceRate c`, weights `fullModeWeight c s`
(`= sourceRate c · ⟨n⟩^{-2s}`), isotropic `E`. -/
def ofCoefficients (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    RamerSetting :=
  ofWeights (sourceRate c) (fullModeWeight c s) (sourceRate_pos c) (fullModeWeight_pos c s)
    (summable_fullModeWeight_div_sourceRate c s hs)

/-- The Cameron–Martin space of `ofCoefficients` is the project's `ActualCM c` (definitionally). -/
example (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (ofCoefficients c s hs).H = ActualCM c := rfl

theorem ofCoefficients_H (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (ofCoefficients c s hs).H = NlsGge.Ramer.ActualCM c := rfl

theorem ofCoefficients_q (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    (ofCoefficients c s hs).q = sourceRate c := rfl

/-- The coordinate preserving isometry `FullWeightedHilbert c s ≃ₗᵢ[ℝ] E` of `ofCoefficients`. -/
def fullWeightedEquiv (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    FullWeightedHilbert c s ≃ₗᵢ[ℝ] (ofCoefficients c s hs).E :=
  ofWeightsEquiv (sourceRate c) (fullModeWeight c s) (sourceRate_pos c)
    (summable_fullModeWeight_div_sourceRate c s hs)

/-- `fullWeightedEquiv` preserves Fourier coordinates. -/
theorem coord_fullWeightedEquiv (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (x : FullWeightedHilbert c s) (n : ℤ) :
    (ofCoefficients c s hs).coord n (fullWeightedEquiv c s hs x) =
      (show WeightedHilbert (fullModeWeight c s) from x) n := by
  apply coord_ofSeq
  exact memE_ofWeights_of_weighted _ _ _ _ x

/-- `incl` of `ofCoefficients` is the project's `cmToFullWeightedHilbert`, transported by
`fullWeightedEquiv`. -/
theorem fullWeightedEquiv_cmToFull (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (h : NlsGge.Ramer.ActualCM c) :
    fullWeightedEquiv c s hs
        (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h) =
      (ofCoefficients c s hs).incl h := by
  apply (ofCoefficients c s hs).E_ext; intro n
  have := (ofCoefficients c s hs).coord_incl h n
  rw [coord_fullWeightedEquiv]
  exact this.symm

theorem norm_incl_eq_norm_cmToFull (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (h : NlsGge.Ramer.ActualCM c) :
    ‖(ofCoefficients c s hs).incl h‖ =
      ‖cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) h‖ := by
  rw [← fullWeightedEquiv_cmToFull c s hs h, LinearIsometryEquiv.norm_map]

theorem ofCoefficients_hs_sum (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    ∑' n, ((ofCoefficients c s hs).M n).tr / (2 * (ofCoefficients c s hs).q n) =
      ∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s) := by
  refine tsum_congr (fun n => ?_)
  have h := ofWeights_ratio (sourceRate c) (fullModeWeight c s) (sourceRate_pos c)
    (fullModeWeight_pos c s) (summable_fullModeWeight_div_sourceRate c s hs) n
  change (ofCoefficients c s hs).ratio n = _
  rw [show (ofCoefficients c s hs).ratio n = fullModeWeight c s n / sourceRate c n from h]
  have := (sourceRate_pos c n).ne'
  unfold fullModeWeight
  field_simp

/-- Regression probe: the general `incl_hs_hasSum` for `ofCoefficients` reproduces the
existing `cmToFullWeightedHilbert_any_sourceBasis_square_sum` (same summands, same sum). -/
theorem ofCoefficients_incl_hs_regression (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) {ι : Type*} (b : HilbertBasis ι ℝ (NlsGge.Ramer.ActualCM c)) :
    HasSum (fun i : ι => ‖(ofCoefficients c s hs).incl (b i)‖ ^ 2)
        (∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s)) ∧
      (fun i : ι => ‖(ofCoefficients c s hs).incl (b i)‖ ^ 2) =
        (fun i : ι => ‖cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) (b i)‖ ^ 2) ∧
      HasSum (fun i : ι =>
        ‖cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) (b i)‖ ^ 2)
        (∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s)) := by
  refine ⟨?_, ?_, cmToFullWeightedHilbert_any_sourceBasis_square_sum c s hs b⟩
  · rw [← ofCoefficients_hs_sum c s hs]
    exact (ofCoefficients c s hs).incl_hs_hasSum b
  · funext i
    rw [norm_incl_eq_norm_cmToFull]

end Coefficients

/-! ### The F05 instance

For F05 (v2 l.680): `E = h^{m-1}`, `q_n = a_{m,n} = W_m(2πn)`, `H = h^m`.  Take
`r = m - 1`, `q n = a m n`, and `S := ofSobolevRates q hq r hs`, where the required inputs, to be
supplied by F05 / `NlsGge.Weights`, are

* `hq : ∀ n, 0 < a m n`, and
* `hs : Summable (fun n => ⟨n⟩^{2(m-1)} / a m n)` (follows from `a m n ≥ c ⟨n⟩^{2m}`).

Then `S.E` is isometric to `SobolevHilbert (m-1) = WeightedRealHilbert (⟨n⟩^{2(m-1)})` by
`ofSobolevRatesEquiv` (coordinate preserving), `S.H = WeightedRealHilbert (2 a m n)`, and
`S.incl` is Hilbert–Schmidt (`incl_hs`) with `‖incl‖²_HS = Σ ⟨n⟩^{2(m-1)} / a m n`. -/

/-- F05 instance: Sobolev weight `⟨n⟩^{2r}` for `E`, arbitrary positive rates `q`. -/
def ofSobolevRates (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) (r : ℝ)
    (hs : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * r) / q n)) : RamerSetting :=
  ofWeights q (sobolevModeWeight r) hq
    (fun n => Real.rpow_pos_of_pos (japaneseBracket_pos n) _) hs

/-- The coordinate preserving isometry `SobolevHilbert r ≃ₗᵢ[ℝ] E` of `ofSobolevRates`. -/
def ofSobolevRatesEquiv (q : ℤ → ℝ) (hq : ∀ n, 0 < q n) (r : ℝ)
    (hs : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * r) / q n)) :
    SobolevHilbert r ≃ₗᵢ[ℝ] (ofSobolevRates q hq r hs).E :=
  ofWeightsEquiv q (sobolevModeWeight r) hq hs

end RamerSetting

end NlsGge.Ramer.General
