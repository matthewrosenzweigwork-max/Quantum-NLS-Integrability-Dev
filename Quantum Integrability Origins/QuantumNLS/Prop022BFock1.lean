import Mathlib
import QuantumNLS.Prop022BIso
import QuantumNLS.Prop022ACoherent
import QuantumNLS.Prop022ACovPhys

/-! PROP-022 route A, finite-dimensional case, stage B2b: the range of `Γ(J)` as the fixed space of
the rotations `1_{range J} ⊕ z`, and compression of unitaries commuting with them.

* `gamAdj J = Γ(J)*` (Hilbert adjoint of `fockMapI J`), sector formula, `Γ(J)* Γ(J) = 1`;
* `rot J z`: for `‖z‖ = 1` the unitary `Q + z (1 - Q)` of a Hilbert space `F`, `Q = J J*`;
* `sector_mem_range`: a vector `y ∈ Sym^n(L2T L)` fixed by `Γ_n(rot J z)` for all `‖z‖ = 1` lies in the range
  of `Γ_n(J)` (power-vector expansion `(a + z c)^{⊗n} = ∑_s z^{|s^c|} ⊗ …` and a polynomial in `z`
  that is constant on the circle);
* `fock_mem_range`, `range_fixed`: `range Γ(J) = {y : Γ(R) y = y for all unitaries R with R J = J}`;
* `compress J T hT`: a unitary `T` of `Fock(L2T L)` commuting with `Γ(R)` for all such `R`
  restricts to a unitary `Γ(J)* T Γ(J)` of `Fock(H)`, with `Γ(J) (compress x) = T (Γ(J) x)`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open ContinuousLinearMap

namespace QuantumNLS.Prop022BFock1
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022BIso Prop022ACoherent

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ### The Fock adjoint -/

/-- `Γ(J)*`. -/
def gamAdj (J : E →ₗᵢ[ℂ] F) : FockSpace F →L[ℂ] FockSpace E :=
  ContinuousLinearMap.adjoint (fockMapI J).toContinuousLinearMap

lemma gamAdj_gam (J : E →ₗᵢ[ℂ] F) (x : FockSpace E) : gamAdj J (fockMapI J x) = x := by
  apply ext_inner_right ℂ
  intro v
  rw [gamAdj, ContinuousLinearMap.adjoint_inner_left]
  exact (fockMapI J).inner_map_map x v

lemma fockMapI_single (J : E →ₗᵢ[ℂ] F) (n : ℕ) (x : SymSector ℂ E n) :
    fockMapI J (lp.single 2 n x : FockSpace E) = (lp.single 2 n (symI J n x) : FockSpace F) := by
  apply lp.ext
  funext k
  rw [fockMapI_apply]
  by_cases hk : k = n
  · subst hk
    rw [lp.single_apply_self, lp.single_apply_self]
    rfl
  · rw [lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hk]
    simp

lemma gamAdj_sector (J : E →ₗᵢ[ℂ] F) (y : FockSpace F) (n : ℕ) :
    (gamAdj J y) n = symAdj J n (y n) := by
  apply ext_inner_right ℂ
  intro v
  have h1 : ⟪(gamAdj J y) n, v⟫_ℂ = ⟪gamAdj J y, (lp.single 2 n v : FockSpace E)⟫_ℂ :=
    (lp.inner_single_right (𝕜 := ℂ) n v (gamAdj J y)).symm
  rw [h1, gamAdj, ContinuousLinearMap.adjoint_inner_left]
  have h2 : ((fockMapI J).toContinuousLinearMap (lp.single 2 n v : FockSpace E)) =
      (lp.single 2 n (symI J n v) : FockSpace F) := fockMapI_single J n v
  rw [h2, lp.inner_single_right (𝕜 := ℂ) n (symI J n v) y, inner_symAdj_left]

/-! ### The rotations -/

/-- `z x + (1 - z) J J* x = Q x + z (1 - Q) x`. -/
def rotCLM (J : E →ₗᵢ[ℂ] F) (z : ℂ) : F →L[ℂ] F :=
  z • ContinuousLinearMap.id ℂ F + (1 - z) • (J.toContinuousLinearMap ∘L Jadj J)

lemma rotCLM_apply (J : E →ₗᵢ[ℂ] F) (z : ℂ) (x : F) :
    rotCLM J z x = z • x + (1 - z) • J (Jadj J x) := rfl

lemma rot_eq (J : E →ₗᵢ[ℂ] F) (z : ℂ) (x : F) :
    rotCLM J z x = J (Jadj J x) + z • (x - J (Jadj J x)) := by
  rw [rotCLM_apply]; module

lemma inner_Q_orth (J : E →ₗᵢ[ℂ] F) (x : F) :
    ⟪J (Jadj J x), x - J (Jadj J x)⟫_ℂ = 0 := by
  rw [inner_sub_right, ← inner_Jadj_right, LinearIsometry.inner_map_map, sub_self]

lemma norm_rotCLM (J : E →ₗᵢ[ℂ] F) (z : ℂ) (hz : ‖z‖ = 1) (x : F) : ‖rotCLM J z x‖ = ‖x‖ := by
  set q := J (Jadj J x) with hq
  have h0 : ⟪q, x - q⟫_ℂ = 0 := inner_Q_orth J x
  have h1 : ‖q + z • (x - q)‖ ^ 2 = ‖q‖ ^ 2 + ‖x - q‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero q (z • (x - q))
      (by rw [inner_smul_right, h0, mul_zero])
    rw [norm_smul, hz, one_mul] at this
    rw [sq, sq, sq]
    exact this
  have h2 : ‖x‖ ^ 2 = ‖q‖ ^ 2 + ‖x - q‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero q (x - q) h0
    rw [add_sub_cancel] at this
    rw [sq, sq, sq]
    exact this
  rw [rot_eq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h1.trans h2.symm)

lemma rot_rot (J : E →ₗᵢ[ℂ] F) (z w : ℂ) (x : F) :
    rotCLM J z (rotCLM J w x) = rotCLM J (z * w) x := by
  simp only [rotCLM_apply, map_add, map_smul, Jadj_J]
  module

lemma rot_J (J : E →ₗᵢ[ℂ] F) (z : ℂ) (x : E) : rotCLM J z (J x) = J x := by
  rw [rotCLM_apply, Jadj_J]; module

lemma rot_one (J : E →ₗᵢ[ℂ] F) (x : F) : rotCLM J 1 x = x := by
  rw [rotCLM_apply]; simp

/-- The rotation `Q + z (1 - Q)` as a unitary. -/
def rot (J : E →ₗᵢ[ℂ] F) (z : ℂ) (hz : ‖z‖ = 1) : F ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (rotCLM J z : F →ₗ[ℂ] F), norm_map' := norm_rotCLM J z hz }
    (by
      intro y
      have hz0 : z ≠ 0 := by
        intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
      refine ⟨rotCLM J z⁻¹ y, ?_⟩
      change rotCLM J z (rotCLM J z⁻¹ y) = y
      rw [rot_rot, mul_inv_cancel₀ hz0, rot_one])

lemma rot_apply (J : E →ₗᵢ[ℂ] F) (z : ℂ) (hz : ‖z‖ = 1) (x : F) : rot J z hz x = rotCLM J z x := rfl

lemma rot_fixes (J : E →ₗᵢ[ℂ] F) (z : ℂ) (hz : ‖z‖ = 1) (x : E) : rot J z hz (J x) = J x :=
  rot_J J z x

/-! ### The unit circle is infinite -/

lemma infinite_unit_circle : {u : ℂ | ‖u‖ = 1}.Infinite := by
  have hne : ∀ r : ℝ, (1 - (r : ℂ) * Complex.I) ≠ 0 := by
    intro r h
    have := congrArg Complex.re h
    simp at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun r : ℝ => (1 + (r : ℂ) * Complex.I) / (1 - (r : ℂ) * Complex.I)) ?_ ?_
  · intro r s h
    have h' : (1 + (r : ℂ) * Complex.I) * (1 - (s : ℂ) * Complex.I) =
        (1 + (s : ℂ) * Complex.I) * (1 - (r : ℂ) * Complex.I) := by
      have := h
      simp only at this
      rwa [div_eq_div_iff (hne r) (hne s)] at this
    have him := congrArg Complex.im h'
    simp at him
    linarith
  · intro r
    show ‖(1 + (r : ℂ) * Complex.I) / (1 - (r : ℂ) * Complex.I)‖ = 1
    rw [norm_div, div_eq_one_iff_eq (by simpa using hne r)]
    have h1 : ‖(1 + (r : ℂ) * Complex.I)‖ ^ 2 = 1 + r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have h2 : ‖(1 - (r : ℂ) * Complex.I)‖ ^ 2 = 1 + r ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h1.trans h2.symm)

/-! ### Expansion of `(a + z c)^{⊗n}` -/

lemma ptprod_add_smul (n : ℕ) (a c : F) (z : ℂ) :
    (ptprod (fun _ : Fin n => a + z • c) : AlgTensorPower ℂ F n) =
      ∑ s : Finset (Fin n), z ^ (Finset.univ.filter (fun i => i ∉ s)).card •
        (ptprod (s.piecewise (fun _ => a) (fun _ => c)) : AlgTensorPower ℂ F n) := by
  classical
  have h := (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => F)).map_add_univ
    (fun _ => a) (fun _ => z • c)
  refine h.trans (Finset.sum_congr rfl (fun s _ => ?_))
  have hs : s.piecewise (fun _ => a) (fun _ => z • c) =
      fun i => (if i ∈ s then (1 : ℂ) else z) • s.piecewise (fun _ => a) (fun _ => c) i := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hs, MultilinearMap.map_smul_univ]
  congr 1
  simp [Finset.prod_ite]

lemma inner_htpow_add_smul (n : ℕ) (a c : F) (z : ℂ) (y : HilbertTensorPower ℂ F n) :
    ⟪y, (htpow n (a + z • c) : HilbertTensorPower ℂ F n)⟫_ℂ =
      ∑ s : Finset (Fin n), z ^ (Finset.univ.filter (fun i => i ∉ s)).card *
        ⟪y, ((ptprod (s.piecewise (fun _ => a) (fun _ => c)) : AlgTensorPower ℂ F n) :
          HilbertTensorPower ℂ F n)⟫_ℂ := by
  classical
  have h1 : (htpow n (a + z • c) : HilbertTensorPower ℂ F n) =
      ((∑ s : Finset (Fin n), z ^ (Finset.univ.filter (fun i => i ∉ s)).card •
        (ptprod (s.piecewise (fun _ => a) (fun _ => c)) : AlgTensorPower ℂ F n) :
          AlgTensorPower ℂ F n) : HilbertTensorPower ℂ F n) := by
    rw [htpow, ptprod_add_smul]
  have h2 := map_sum (UniformSpace.Completion.toComplL (S := ℂ) (α := AlgTensorPower ℂ F n))
    (fun s : Finset (Fin n) => z ^ (Finset.univ.filter (fun i => i ∉ s)).card •
        (ptprod (s.piecewise (fun _ => a) (fun _ => c)) : AlgTensorPower ℂ F n)) Finset.univ
  simp only [UniformSpace.Completion.coe_toComplL] at h2
  rw [h1, h2, inner_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [UniformSpace.Completion.coe_smul, inner_smul_right]

/-! ### Sector level: fixed vectors lie in the range -/

lemma symMap_powerH' {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] (R : E' ≃ₗᵢ[ℂ] F') (n : ℕ) (x : E') :
    symMap R n (powerH n x) = powerH n (R x) :=
  Subtype.ext (tensorMap_htpow R n x)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The key identity: a rotation-fixed `y` pairs with `w^{⊗n}` as with `(J J* w)^{⊗n}`. -/
theorem pair_power_eq (J : H →ₗᵢ[ℂ] L2T L) (n : ℕ) (y : SymSector ℂ (L2T L) n)
    (hy : ∀ (z : ℂ) (hz : ‖z‖ = 1), symMap (rot J z hz) n y = y) (w : L2T L) :
    ⟪y, powerH n w⟫_ℂ = ⟪y, powerH n (J (Jadj J w))⟫_ℂ := by
  classical
  set a := J (Jadj J w) with ha
  set c := w - a with hc
  have hw : w = a + (1 : ℂ) • c := by rw [hc, one_smul]; abel
  let cs : Finset (Fin n) → ℂ := fun s =>
    ⟪(y : HilbertTensorPower ℂ (L2T L) n), ((ptprod (s.piecewise (fun _ => a) (fun _ => c)) :
      AlgTensorPower ℂ (L2T L) n) : HilbertTensorPower ℂ (L2T L) n)⟫_ℂ
  let g : Polynomial ℂ := ∑ s : Finset (Fin n),
    Polynomial.C (cs s) * Polynomial.X ^ (Finset.univ.filter (fun i => i ∉ s)).card
  have hg : ∀ z : ℂ, ⟪y, powerH n (a + z • c)⟫_ℂ = g.eval z := by
    intro z
    have := inner_htpow_add_smul n a c z (y : HilbertTensorPower ℂ (L2T L) n)
    change ⟪(y : HilbertTensorPower ℂ (L2T L) n),
      (htpow n (a + z • c) : HilbertTensorPower ℂ (L2T L) n)⟫_ℂ = _ at this
    rw [show ⟪y, powerH n (a + z • c)⟫_ℂ = ⟪(y : HilbertTensorPower ℂ (L2T L) n),
      (htpow n (a + z • c) : HilbertTensorPower ℂ (L2T L) n)⟫_ℂ from rfl, this]
    simp only [g, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, cs]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  have hcirc : ∀ z : ℂ, ‖z‖ = 1 → g.eval z = g.eval 1 := by
    intro z hz
    rw [← hg, ← hg]
    have hrot : rot J z hz (a + (1 : ℂ) • c) = a + z • c := by
      rw [rot_apply, rot_eq]
      have h1 : Jadj J (a + (1 : ℂ) • c) = Jadj J w := by rw [← hw]
      rw [h1, ← ha, one_smul, show a + c - a = c by abel]
    have h2 : powerH n (a + z • c) = symMap (rot J z hz) n (powerH n (a + (1 : ℂ) • c)) := by
      rw [symMap_powerH', hrot]
    rw [h2]
    calc ⟪y, symMap (rot J z hz) n (powerH n (a + (1 : ℂ) • c))⟫_ℂ
        = ⟪symMap (rot J z hz) n y, symMap (rot J z hz) n (powerH n (a + (1 : ℂ) • c))⟫_ℂ := by
          rw [hy z hz]
      _ = ⟪y, powerH n (a + (1 : ℂ) • c)⟫_ℂ := LinearIsometryEquiv.inner_map_map _ _ _
  have hconst : g = Polynomial.C (g.eval 1) := by
    have := Polynomial.eq_of_infinite_eval_eq g (Polynomial.C (g.eval 1))
      (Set.Infinite.mono (fun u hu => by
        simp only [Set.mem_setOf_eq, Polynomial.eval_C]
        exact hcirc u hu) infinite_unit_circle)
    exact this
  have h0 : g.eval 0 = g.eval 1 := by
    have := congrArg (Polynomial.eval 0) hconst
    rw [Polynomial.eval_C] at this
    exact this
  have e1 := hg 1
  have e0 := hg 0
  rw [← hw] at e1
  rw [zero_smul, add_zero] at e0
  rw [e1, ← h0, ← e0]

theorem sector_mem_range (J : H →ₗᵢ[ℂ] L2T L) (n : ℕ) (y : SymSector ℂ (L2T L) n)
    (hy : ∀ (z : ℂ) (hz : ‖z‖ = 1), symMap (rot J z hz) n y = y) :
    symI J n (symAdj J n y) = y := by
  have hd : y - symI J n (symAdj J n y) = 0 := by
    apply powers_total
    intro g
    rw [inner_sub_right]
    have h1 : ⟪powerH n g, symI J n (symAdj J n y)⟫_ℂ = ⟪powerH n (J (Jadj J g)), y⟫_ℂ := by
      rw [← inner_symAdj_left, symAdj_power, inner_symAdj_right, symI_power]
    have h2 : ⟪powerH n g, y⟫_ℂ = ⟪powerH n (J (Jadj J g)), y⟫_ℂ := by
      rw [← inner_conj_symm (powerH n g) y, ← inner_conj_symm (powerH n (J (Jadj J g))) y,
        pair_power_eq J n y hy g]
    change ⟪powerH n g, y⟫_ℂ - ⟪powerH n g, symI J n (symAdj J n y)⟫_ℂ = 0
    rw [h1, h2, sub_self]
  exact (sub_eq_zero.mp hd).symm

/-! ### Fock level -/

/-- A unitary of `L2T L` fixing `range J` pointwise. -/
def Fixes (J : H →ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) : Prop := ∀ v, R (J v) = J v

lemma fock_fixed_of_range (J : H →ₗᵢ[ℂ] L2T L) (R : L2T L ≃ₗᵢ[ℂ] L2T L) (hR : Fixes J R)
    (x : FockSpace H) : fockMap R (fockMapI J x) = fockMapI J x := by
  have h1 : R.toLinearIsometry.comp J = J := LinearIsometry.ext (fun v => hR v)
  rw [← fockMapI_equiv, ← fockMapI_comp, h1]

theorem fock_mem_range (J : H →ₗᵢ[ℂ] L2T L) (y : Fock L)
    (hy : ∀ R, Fixes J R → fockMap R y = y) : fockMapI J (gamAdj J y) = y := by
  apply lp.ext
  funext n
  rw [fockMapI_apply, gamAdj_sector]
  apply sector_mem_range
  intro z hz
  have h := hy (rot J z hz) (fun v => rot_fixes J z hz v)
  have h' := congrArg (fun w : Fock L => w n) h
  exact h'

/-- Commutation of a unitary of `Fock(L2T L)` with `Γ(R)` for every `R` fixing `range J`. -/
def Commutes (J : H →ₗᵢ[ℂ] L2T L) (T : Fock L ≃ₗᵢ[ℂ] Fock L) : Prop :=
  ∀ R, Fixes J R → ∀ z, fockMap R (T z) = T (fockMap R z)

lemma Commutes.symm {J : H →ₗᵢ[ℂ] L2T L} {T : Fock L ≃ₗᵢ[ℂ] Fock L} (hT : Commutes J T) :
    Commutes J T.symm := by
  intro R hR z
  apply T.injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← hT R hR, LinearIsometryEquiv.apply_symm_apply]

lemma comm_range {J : H →ₗᵢ[ℂ] L2T L} {T : Fock L ≃ₗᵢ[ℂ] Fock L} (hT : Commutes J T)
    (x : FockSpace H) :
    fockMapI J (gamAdj J (T (fockMapI J x))) = T (fockMapI J x) := by
  apply fock_mem_range
  intro R hR
  rw [hT R hR, fock_fixed_of_range J R hR]

/-- The compression `Γ(J)* T Γ(J)` as a linear isometry. -/
def compressLI (J : H →ₗᵢ[ℂ] L2T L) (T : Fock L ≃ₗᵢ[ℂ] Fock L) (hT : Commutes J T) :
    FockSpace H →ₗᵢ[ℂ] FockSpace H where
  toFun x := gamAdj J (T (fockMapI J x))
  map_add' x y := by simp
  map_smul' c x := by simp
  norm_map' x := by
    have h := comm_range hT x
    calc ‖gamAdj J (T (fockMapI J x))‖
        = ‖fockMapI J (gamAdj J (T (fockMapI J x)))‖ := ((fockMapI J).norm_map _).symm
      _ = ‖T (fockMapI J x)‖ := by rw [h]
      _ = ‖x‖ := by rw [T.norm_map, (fockMapI J).norm_map]

/-- The compression `Γ(J)* T Γ(J)` as a unitary of `Fock(H)`. -/
def compress (J : H →ₗᵢ[ℂ] L2T L) (T : Fock L ≃ₗᵢ[ℂ] Fock L) (hT : Commutes J T) :
    FockSpace H ≃ₗᵢ[ℂ] FockSpace H :=
  LinearIsometryEquiv.ofSurjective (compressLI J T hT) (by
    intro y
    refine ⟨gamAdj J (T.symm (fockMapI J y)), ?_⟩
    change gamAdj J (T (fockMapI J (gamAdj J (T.symm (fockMapI J y))))) = y
    rw [comm_range hT.symm, LinearIsometryEquiv.apply_symm_apply, gamAdj_gam])

lemma compress_apply (J : H →ₗᵢ[ℂ] L2T L) (T : Fock L ≃ₗᵢ[ℂ] Fock L) (hT : Commutes J T)
    (x : FockSpace H) : compress J T hT x = gamAdj J (T (fockMapI J x)) := rfl

/-- `Γ(J) (Γ(J)* T Γ(J) x) = T Γ(J) x`. -/
theorem gam_compress (J : H →ₗᵢ[ℂ] L2T L) (T : Fock L ≃ₗᵢ[ℂ] Fock L) (hT : Commutes J T)
    (x : FockSpace H) : fockMapI J (compress J T hT x) = T (fockMapI J x) :=
  comm_range hT x

theorem gam_compress_symm (J : H →ₗᵢ[ℂ] L2T L) (T : Fock L ≃ₗᵢ[ℂ] Fock L) (hT : Commutes J T)
    (y : FockSpace H) :
    fockMapI J ((compress J T hT).symm y) = T.symm (fockMapI J y) := by
  have h := gam_compress J T hT ((compress J T hT).symm y)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h, LinearIsometryEquiv.symm_apply_apply]

lemma gam_injective (J : H →ₗᵢ[ℂ] L2T L) : Function.Injective (fockMapI J) :=
  (fockMapI J).injective

end QuantumNLS.Prop022BFock1
