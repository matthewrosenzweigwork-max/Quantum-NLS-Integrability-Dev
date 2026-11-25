import QuantumNLS.EnergyContactTrace
import QuantumNLS.ProductEnergyPreparation
import QuantumNLS.ProductSecondDerivatives

/-!
# ENERGY-002 `lem:A1-trace` (`source-text/chapters/energy_prepared/cubic_charge.tex:74`): the
# finite-rank smooth-kernel commutator clause, bosonic restriction, and the assembled statement

Owner: review record.  Imports (read-only, frozen by other authors or earlier checkpoints):
`EnergyContactTrace` (this author, frozen `69f1e9d9`: `traceCLM`/`productTrace`, `traceHalf`, `traceInv`,
`Bsand`, `bform`, `Sop`, `commutator_sandwich_isCompact`), `ProductEnergyPreparation`,
`ProductSecondDerivatives`, and transitively `CollisionIdentification`, `ProductWeakDerivatives`,
`PhysicalEnergy`.

Parts: 1-2 slicewise tensor operator `A ⊗ 1` on `ℓ²(ℤ^{k+1}) = ℓ²(ℤ^k) ⊗ ℓ²(ℤ)` and the `H¹`
energy bound for `J = |F⟩⟨G|`; 3 the smoothing-trace bound `eq:A1-smoothing-trace` (Young, Fourier
form); 4 abstract assembly `Bsand K − K'^* Bsand` compact; 5 `K̃ = A^{1/2}(|F⟩⟨G|⊗1)A^{-1/2}` and
`V = D_ij T_ij K̃`; 6 smooth lattice-periodic profiles have Wiener-summable Fourier coefficients;
7 `J ⊗ Id` on the actual carrier `L²(𝕋_L^{k+1})` (matrix elements on elementary tensors,
uniqueness, adjoint); 8 external commutator; 9 internal commutator; 10 bosonic restriction;
11 the printed statement `energy002`.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal
open MeasureTheory

namespace QuantumNLS.EnergyContactCommutator

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace QuantumNLS.Fourier
  QuantumNLS.CollisionIdentification QuantumNLS.PhysicalTensor QuantumNLS.EnergyContactTrace

/-! ## Part 1: the splitting `ℤ^{k+1} = ℤ^k × ℤ` and the slicewise tensor operator `A ⊗ 1` -/

section Tensor

variable {k : ℕ}

/-- The first `k` coordinates. -/
def initM (w : Mom (k + 1)) : Mom k := fun l => w l.castSucc

/-- The last coordinate (the variable `k+1`). -/
def lastM (w : Mom (k + 1)) : ℤ := w (Fin.last k)

theorem initM_snoc (c : Mom k) (b : ℤ) : initM (Fin.snoc c b : Mom (k + 1)) = c := by
  funext l; simp [initM]

theorem lastM_snoc (c : Mom k) (b : ℤ) : lastM (Fin.snoc c b : Mom (k + 1)) = b := by
  simp [lastM]

theorem snoc_initM_lastM (w : Mom (k + 1)) : (Fin.snoc (initM w) (lastM w) : Mom (k + 1)) = w := by
  funext l
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp [lastM]
  · simp [initM]

/-- `ℤ × ℤ^k ≃ ℤ^{k+1}`, `(b, c) ↦ (c, b)`. -/
def snocE (k : ℕ) : ℤ × Mom k ≃ Mom (k + 1) where
  toFun p := Fin.snoc p.2 p.1
  invFun w := (lastM w, initM w)
  left_inv p := by
    obtain ⟨b, c⟩ := p
    simp [initM_snoc, lastM_snoc]
  right_inv w := snoc_initM_lastM w

theorem snoc_injective (b : ℤ) : Function.Injective (fun c : Mom k => (Fin.snoc c b : Mom (k + 1))) := by
  intro c c' h
  have := congrArg initM h
  simpa [initM_snoc] using this

/-- Re-summation over the splitting `ℤ^{k+1} = ℤ^k × ℤ`. -/
theorem sum_snoc {G : Mom (k + 1) → ℝ} (hG : Summable G) :
    Summable (fun b : ℤ => ∑' c : Mom k, G (Fin.snoc c b)) ∧
      ∑' w, G w = ∑' b : ℤ, ∑' c : Mom k, G (Fin.snoc c b) := by
  have hs : Summable (G ∘ snocE k) := (snocE k).summable_iff.2 hG
  refine ⟨hs.prod, ?_⟩
  rw [← (snocE k).tsum_eq G]
  exact hs.tsum_prod

/-- Product sums over `ℤ^{k+1}`: `Σ_w u(init w) v(last w) = (Σ u)(Σ v)` for summable `u, v ≥ 0`. -/
theorem hasSum_init_last {u : Mom k → ℝ} {v : ℤ → ℝ} (hu0 : ∀ c, 0 ≤ u c) (hv0 : ∀ b, 0 ≤ v b)
    (hu : Summable u) (hv : Summable v) :
    HasSum (fun w : Mom (k + 1) => u (initM w) * v (lastM w)) ((∑' c, u c) * ∑' b, v b) := by
  have hm : Summable (fun p : ℤ × Mom k => v p.1 * u p.2) :=
    Summable.mul_of_nonneg hv hu hv0 hu0
  have h := hv.hasSum.mul hu.hasSum hm
  have hcomp : HasSum ((fun w : Mom (k + 1) => u (initM w) * v (lastM w)) ∘ snocE k)
      ((∑' b, v b) * ∑' c, u c) := by
    convert h using 1
    funext p
    simp [snocE, initM_snoc, lastM_snoc, mul_comm]
  have h2 := ((snocE k).hasSum_iff).1 hcomp
  rw [mul_comm]
  exact h2

/-- The slice `c(·, b)` of an array on `ℤ^{k+1}`, an element of `ℓ²(ℤ^k)`. -/
def slice (c : L2 (Mom (k + 1))) (b : ℤ) : L2 (Mom k) :=
  ⟨fun c' => (c : Mom (k + 1) → ℂ) (Fin.snoc c' b),
    memL2_iff.2 ((summable_sq c).comp_injective (snoc_injective b))⟩

theorem slice_apply (c : L2 (Mom (k + 1))) (b : ℤ) (c' : Mom k) :
    (slice c b : Mom k → ℂ) c' = (c : Mom (k + 1) → ℂ) (Fin.snoc c' b) := rfl

theorem summable_slice_norm (c : L2 (Mom (k + 1))) :
    Summable (fun b : ℤ => ‖slice c b‖ ^ 2) ∧ ∑' b : ℤ, ‖slice c b‖ ^ 2 = ‖c‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := sum_snoc (summable_sq c)
  have e : ∀ b : ℤ, ‖slice c b‖ ^ 2 = ∑' c' : Mom k, ‖(c : Mom (k + 1) → ℂ) (Fin.snoc c' b)‖ ^ 2 :=
    fun b => norm_sq_eq_tsum (slice c b)
  refine ⟨?_, ?_⟩
  · simp_rw [e]; exact h1
  · simp_rw [e]; rw [← h2, norm_sq_eq_tsum]

theorem slice_add (c d : L2 (Mom (k + 1))) (b : ℤ) : slice (c + d) b = slice c b + slice d b := by
  apply Subtype.ext; funext c'; rfl

theorem slice_smul (a : ℂ) (c : L2 (Mom (k + 1))) (b : ℤ) : slice (a • c) b = a • slice c b := by
  apply Subtype.ext; funext c'; rfl

/-- The slicewise tensor operator: `(A ⊗ 1) c (·, b) = A (c(·, b))`. -/
def tensorFun (A : L2 (Mom k) →L[ℂ] L2 (Mom k)) (c : L2 (Mom (k + 1))) : Mom (k + 1) → ℂ :=
  fun w => (A (slice c (lastM w)) : Mom k → ℂ) (initM w)

theorem memL2_tensorFun (A : L2 (Mom k) →L[ℂ] L2 (Mom k)) (c : L2 (Mom (k + 1))) :
    Memℓp (tensorFun A c) 2 ∧ ∑' w, ‖tensorFun A c w‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖c‖ ^ 2 := by
  have hs : Summable (fun p : ℤ × Mom k => ‖(A (slice c p.1) : Mom k → ℂ) p.2‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun p => sq_nonneg _)]
    refine ⟨fun b => summable_sq (A (slice c b)), ?_⟩
    have hb : ∀ b : ℤ, ∑' a : Mom k, ‖(A (slice c b) : Mom k → ℂ) a‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖slice c b‖ ^ 2 := fun b => by
      rw [← norm_sq_eq_tsum, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    exact Summable.of_nonneg_of_le (fun b => tsum_nonneg fun a => sq_nonneg _) hb
      ((summable_slice_norm c).1.mul_left _)
  have hs' : Summable (fun w : Mom (k + 1) => ‖tensorFun A c w‖ ^ 2) := by
    have := (snocE k).symm.summable_iff.2 hs
    refine this.congr fun w => ?_
    simp [snocE, tensorFun]
  refine ⟨memL2_iff.2 hs', ?_⟩
  have hsum := (snocE k).tsum_eq (fun w : Mom (k + 1) => ‖tensorFun A c w‖ ^ 2)
  have e1 : ∑' w, ‖tensorFun A c w‖ ^ 2 = ∑' p : ℤ × Mom k, ‖(A (slice c p.1) : Mom k → ℂ) p.2‖ ^ 2 := by
    rw [← hsum]
    refine tsum_congr fun p => ?_
    simp [snocE, tensorFun, initM_snoc, lastM_snoc]
  rw [e1, hs.tsum_prod']
  · calc ∑' b : ℤ, ∑' a : Mom k, ‖(A (slice c b) : Mom k → ℂ) a‖ ^ 2
        ≤ ∑' b : ℤ, ‖A‖ ^ 2 * ‖slice c b‖ ^ 2 := by
          refine Summable.tsum_le_tsum (fun b => ?_) ?_ ((summable_slice_norm c).1.mul_left _)
          · rw [← norm_sq_eq_tsum, ← mul_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
          · have hb : ∀ b : ℤ, ∑' a : Mom k, ‖(A (slice c b) : Mom k → ℂ) a‖ ^ 2 ≤
                ‖A‖ ^ 2 * ‖slice c b‖ ^ 2 := fun b => by
              rw [← norm_sq_eq_tsum, ← mul_pow]
              exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
            exact Summable.of_nonneg_of_le (fun b => tsum_nonneg fun a => sq_nonneg _) hb
              ((summable_slice_norm c).1.mul_left _)
      _ = ‖A‖ ^ 2 * ‖c‖ ^ 2 := by
          rw [tsum_mul_left, (summable_slice_norm c).2]
  · intro b; exact summable_sq (A (slice c b))

/-- The slicewise tensor operator `A ⊗ 1` on `ℓ²(ℤ^{k+1}) = ℓ²(ℤ^k) ⊗ ℓ²(ℤ)`. -/
def tensorOp (A : L2 (Mom k) →L[ℂ] L2 (Mom k)) : L2 (Mom (k + 1)) →L[ℂ] L2 (Mom (k + 1)) :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨tensorFun A c, (memL2_tensorFun A c).1⟩
      map_add' := fun c d => by
        apply Subtype.ext; funext w
        simp only [tensorFun, slice_add, map_add, lp.coeFn_add, Pi.add_apply]
      map_smul' := fun a c => by
        apply Subtype.ext; funext w
        simp only [tensorFun, slice_smul, map_smul, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply] }
    ‖A‖ (fun c => by
      refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 ?_
      rw [mul_pow, norm_sq_eq_tsum]
      exact (memL2_tensorFun A c).2)

theorem tensorOp_apply (A : L2 (Mom k) →L[ℂ] L2 (Mom k)) (c : L2 (Mom (k + 1))) (w : Mom (k + 1)) :
    (tensorOp A c : Mom (k + 1) → ℂ) w = (A (slice c (lastM w)) : Mom k → ℂ) (initM w) := rfl

theorem tensorOp_add (A B : L2 (Mom k) →L[ℂ] L2 (Mom k)) (c : L2 (Mom (k + 1))) :
    tensorOp (A + B) c = tensorOp A c + tensorOp B c := by
  apply Subtype.ext; funext w
  simp only [tensorOp_apply, add_apply, lp.coeFn_add, Pi.add_apply]

/-- Rank-one operator `|F⟩⟨G|` on `ℓ²(ℤ^k)`. -/
abbrev rk (F G : L2 (Mom k)) : L2 (Mom k) →L[ℂ] L2 (Mom k) :=
  InnerProductSpace.rankOne ℂ F G

theorem tensorOp_rk_apply (F G : L2 (Mom k)) (c : L2 (Mom (k + 1))) (w : Mom (k + 1)) :
    (tensorOp (rk F G) c : Mom (k + 1) → ℂ) w =
      ((slice c (lastM w)) |> fun σ => ⟪G, σ⟫_ℂ) * (F : Mom k → ℂ) (initM w) := by
  rw [tensorOp_apply]
  simp [InnerProductSpace.rankOne_apply]

end Tensor

/-! ## Part 2: kinetic-energy estimates for the tensor operator -/

section Energy

variable {L : ℝ} {k : ℕ}

theorem kinWeight_snoc (c : Mom k) (b : ℤ) :
    kinWeight L (k + 1) (Fin.snoc c b : Mom (k + 1)) = kinWeight L k c + freq L b ^ 2 := by
  unfold kinWeight
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc]
  ring

theorem kinWeight_init_last (w : Mom (k + 1)) :
    kinWeight L (k + 1) w = kinWeight L k (initM w) + freq L (lastM w) ^ 2 := by
  conv_lhs => rw [← snoc_initM_lastM w]
  exact kinWeight_snoc _ _

/-- Wiener-type weighted summability of a coefficient array on `ℤ^k`:
`Σ_c (1 + Σ_l |2πc_l/L|) |F(c)| < ∞` (holds for smooth profiles, see below). -/
def Wien (L : ℝ) (F : L2 (Mom k)) : Prop :=
  Summable fun c : Mom k => (1 + ∑ l, |freq L (c l)|) * ‖(F : Mom k → ℂ) c‖

theorem wien_omega_pos (c : Mom k) : 1 ≤ 1 + ∑ l, |freq L (c l)| := by
  have : 0 ≤ ∑ l, |freq L (c l)| := Finset.sum_nonneg fun l _ => abs_nonneg _
  linarith

theorem Wien.l1 {F : L2 (Mom k)} (h : Wien L F) : Summable fun c : Mom k => ‖(F : Mom k → ℂ) c‖ := by
  refine Summable.of_nonneg_of_le (fun c => norm_nonneg _) (fun c => ?_) h
  have := wien_omega_pos (L := L) c
  nlinarith [norm_nonneg ((F : Mom k → ℂ) c)]

theorem Wien.l1_freq {F : L2 (Mom k)} (h : Wien L F) (i : Fin k) :
    Summable fun c : Mom k => |freq L (c i)| * ‖(F : Mom k → ℂ) c‖ := by
  refine Summable.of_nonneg_of_le (fun c => by positivity) (fun c => ?_) h
  have : |freq L (c i)| ≤ 1 + ∑ l, |freq L (c l)| := by
    have := Finset.single_le_sum (f := fun l => |freq L (c l)|) (fun l _ => abs_nonneg _)
      (Finset.mem_univ i)
    linarith
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem Wien.kin {F : L2 (Mom k)} (h : Wien L F) :
    Summable fun c : Mom k => kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2 := by
  set x : Mom k → ℝ := fun c => (1 + ∑ l, |freq L (c l)|) * ‖(F : Mom k → ℂ) c‖ with hx
  have hbd : ∀ c, x c ≤ ∑' c, x c := fun c => h.le_tsum c (fun c' _ => by
    simp only [hx]; have := wien_omega_pos (L := L) c'; positivity)
  refine Summable.of_nonneg_of_le (fun c => by
    unfold kinWeight; have : 0 ≤ ∑ j, freq L (c j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    positivity) (fun c => ?_) (h.mul_left (∑' c, x c))
  have hk : kinWeight L k c ≤ (1 + ∑ l, |freq L (c l)|) ^ 2 := by
    unfold kinWeight
    have h1 : ∑ l, freq L (c l) ^ 2 ≤ (∑ l, |freq L (c l)|) ^ 2 := by
      calc ∑ l, freq L (c l) ^ 2 = ∑ l, |freq L (c l)| ^ 2 := by simp [sq_abs]
        _ ≤ (∑ l, |freq L (c l)|) ^ 2 :=
          Finset.sum_sq_le_sq_sum_of_nonneg (fun l _ => abs_nonneg _)
    nlinarith [Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => abs_nonneg (freq L (c l)))]
  have : kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2 ≤ x c ^ 2 := by
    simp only [hx, mul_pow]
    exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)
  calc kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2 ≤ x c ^ 2 := this
    _ = x c * x c := sq _
    _ ≤ (∑' c, x c) * x c := mul_le_mul_of_nonneg_right (hbd c) (by
        simp only [hx]; have := wien_omega_pos (L := L) c; positivity)

/-- The `b`-th slice pairing `h(b) = ⟨G, Φ(·, b)⟩ = Σ_{c'} conj G(c') Φ(c', b)`; with `H¹` weight it
is controlled by `‖G‖ ‖Φ‖_{H¹}` (the bound `‖h‖_{H¹(𝕋)} ≤ ‖g‖₂‖ψ‖_{H¹}` of the source). -/
theorem h_bounds (G : L2 (Mom k)) (Φ : L2 (Mom (k + 1)))
    (hΦ : Summable fun w : Mom (k + 1) => kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2) :
    Summable (fun b : ℤ => (1 + freq L b ^ 2) * ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2) ∧
      ∑' b : ℤ, (1 + freq L b ^ 2) * ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2 ≤
        ‖G‖ ^ 2 * ∑' w : Mom (k + 1), kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2 := by
  obtain ⟨hT, hTe⟩ := sum_snoc hΦ
  have hsl : ∀ b : ℤ, Summable fun c' : Mom k => ‖(Φ : Mom (k + 1) → ℂ) (Fin.snoc c' b)‖ ^ 2 :=
    fun b => summable_sq (slice Φ b)
  have hpt : ∀ b : ℤ, (1 + freq L b ^ 2) * ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2 ≤
      ‖G‖ ^ 2 * ∑' c' : Mom k, kinWeight L (k + 1) (Fin.snoc c' b : Mom (k + 1)) *
        ‖(Φ : Mom (k + 1) → ℂ) (Fin.snoc c' b)‖ ^ 2 := fun b => by
    have h1 : ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2 ≤ ‖G‖ ^ 2 * ‖slice Φ b‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
    have h2 : (1 + freq L b ^ 2) * ‖slice Φ b‖ ^ 2 ≤ ∑' c' : Mom k,
        kinWeight L (k + 1) (Fin.snoc c' b : Mom (k + 1)) *
          ‖(Φ : Mom (k + 1) → ℂ) (Fin.snoc c' b)‖ ^ 2 := by
      rw [norm_sq_eq_tsum, ← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun c' => ?_) ((hsl b).mul_left _)
        (hΦ.comp_injective (snoc_injective b))
      rw [kinWeight_snoc]
      have hk1 : 1 ≤ kinWeight L k c' := by
        unfold kinWeight
        have : 0 ≤ ∑ j, freq L (c' j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
        linarith
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    calc (1 + freq L b ^ 2) * ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2
        ≤ (1 + freq L b ^ 2) * (‖G‖ ^ 2 * ‖slice Φ b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖G‖ ^ 2 * ((1 + freq L b ^ 2) * ‖slice Φ b‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hnn : ∀ b : ℤ, 0 ≤ (1 + freq L b ^ 2) * ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2 := fun b => by positivity
  have hsum : Summable (fun b : ℤ => (1 + freq L b ^ 2) * ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2) :=
    Summable.of_nonneg_of_le hnn hpt (hT.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' b : ℤ, (1 + freq L b ^ 2) * ‖⟪G, slice Φ b⟫_ℂ‖ ^ 2
      ≤ ∑' b : ℤ, ‖G‖ ^ 2 * ∑' c' : Mom k, kinWeight L (k + 1) (Fin.snoc c' b : Mom (k + 1)) *
        ‖(Φ : Mom (k + 1) → ℂ) (Fin.snoc c' b)‖ ^ 2 := hsum.tsum_le_tsum hpt (hT.mul_left _)
    _ = ‖G‖ ^ 2 * ∑' w : Mom (k + 1), kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2 := by
        rw [tsum_mul_left, hTe]

/-- **`(J⊗1)` preserves `H¹` for `J = |F⟩⟨G|` with Wiener `F`**: finite energy of `Ψ = (|F⟩⟨G|⊗1)Φ`
with the explicit bound `E(Ψ) ≤ (E_F + ‖F‖²)‖G‖² E(Φ)`. -/
theorem energy_rk {F G : L2 (Mom k)} (hF : Wien L F) (Φ : L2 (Mom (k + 1)))
    (hΦ : Summable fun w : Mom (k + 1) => kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2) :
    Summable (fun w : Mom (k + 1) => kinWeight L (k + 1) w *
        ‖(tensorOp (rk F G) Φ : Mom (k + 1) → ℂ) w‖ ^ 2) ∧
      ∑' w : Mom (k + 1), kinWeight L (k + 1) w * ‖(tensorOp (rk F G) Φ : Mom (k + 1) → ℂ) w‖ ^ 2 ≤
        ((∑' c : Mom k, kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2) +
          ∑' c : Mom k, ‖(F : Mom k → ℂ) c‖ ^ 2) *
          (‖G‖ ^ 2 * ∑' w : Mom (k + 1), kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2) := by
  obtain ⟨hhs, hhe⟩ := h_bounds G Φ hΦ
  set h : ℤ → ℂ := fun b => ⟪G, slice Φ b⟫_ℂ with hh
  have hk0 : ∀ c : Mom k, 1 ≤ kinWeight L k c := fun c => by
    unfold kinWeight; have : 0 ≤ ∑ j, freq L (c j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  have hu1 : Summable fun c : Mom k => kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2 := hF.kin
  have hu2 : Summable fun c : Mom k => ‖(F : Mom k → ℂ) c‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun c => sq_nonneg _) (fun c => by
      have := hk0 c; nlinarith [sq_nonneg ‖(F : Mom k → ℂ) c‖]) hu1
  have hv1 : Summable fun b : ℤ => ‖h b‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun b => sq_nonneg _) (fun b => by
      have : 0 ≤ freq L b ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg ‖h b‖]) hhs
  have hv2 : Summable fun b : ℤ => freq L b ^ 2 * ‖h b‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun b => by positivity) (fun b => by
      nlinarith [sq_nonneg ‖h b‖]) hhs
  have hA := hasSum_init_last (u := fun c : Mom k => kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2)
    (v := fun b : ℤ => ‖h b‖ ^ 2)
    (fun c => mul_nonneg (by linarith [hk0 c]) (sq_nonneg _)) (fun b => sq_nonneg _) hu1 hv1
  have hB := hasSum_init_last (u := fun c : Mom k => ‖(F : Mom k → ℂ) c‖ ^ 2)
    (v := fun b : ℤ => freq L b ^ 2 * ‖h b‖ ^ 2)
    (fun c => sq_nonneg _) (fun b => by positivity) hu2 hv2
  have hAB := hA.add hB
  have heq : ∀ w : Mom (k + 1), kinWeight L (k + 1) w *
      ‖(tensorOp (rk F G) Φ : Mom (k + 1) → ℂ) w‖ ^ 2 =
      kinWeight L k (initM w) * ‖(F : Mom k → ℂ) (initM w)‖ ^ 2 * ‖h (lastM w)‖ ^ 2 +
        ‖(F : Mom k → ℂ) (initM w)‖ ^ 2 * (freq L (lastM w) ^ 2 * ‖h (lastM w)‖ ^ 2) := fun w => by
    rw [tensorOp_rk_apply, kinWeight_init_last, norm_mul, mul_pow]
    ring
  have hfun : (fun w : Mom (k + 1) => kinWeight L (k + 1) w *
      ‖(tensorOp (rk F G) Φ : Mom (k + 1) → ℂ) w‖ ^ 2) =
      fun w => (kinWeight L k (initM w) * ‖(F : Mom k → ℂ) (initM w)‖ ^ 2 * ‖h (lastM w)‖ ^ 2 +
        ‖(F : Mom k → ℂ) (initM w)‖ ^ 2 * (freq L (lastM w) ^ 2 * ‖h (lastM w)‖ ^ 2)) :=
    funext heq
  rw [hfun]
  refine ⟨hAB.summable, ?_⟩
  rw [hAB.tsum_eq]
  have e1 : ∑' b : ℤ, ‖h b‖ ^ 2 ≤ ‖G‖ ^ 2 * ∑' w : Mom (k + 1), kinWeight L (k + 1) w *
      ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2 := by
    refine le_trans (Summable.tsum_le_tsum (fun b => ?_) hv1 hhs) hhe
    have : 0 ≤ freq L b ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg ‖h b‖]
  have e2 : ∑' b : ℤ, freq L b ^ 2 * ‖h b‖ ^ 2 ≤ ‖G‖ ^ 2 * ∑' w : Mom (k + 1),
      kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2 := by
    refine le_trans (Summable.tsum_le_tsum (fun b => ?_) hv2 hhs) hhe
    nlinarith [sq_nonneg ‖h b‖]
  have hE1 : 0 ≤ ∑' c : Mom k, kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2 :=
    tsum_nonneg fun c => mul_nonneg (by linarith [hk0 c]) (sq_nonneg _)
  have hE2 : 0 ≤ ∑' c : Mom k, ‖(F : Mom k → ℂ) c‖ ^ 2 := tsum_nonneg fun c => sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left e1 hE1, mul_le_mul_of_nonneg_left e2 hE2]

end Energy

/-! ## Part 3: the smoothing-trace bound (`eq:A1-smoothing-trace`), Fourier form -/

section Conv

/-- **Young-type bound for the fibre convolutions** (generic): for `α ≥ 0` summable on `ℤ × ι` and `β ≥ 0`
square-summable on `ℤ`, the functions `t = (s, ℓ) ↦ Σ_a α(a,ℓ) β(s−a)` are square summable on `ℤ × ι`
with `Σ_t (…)² ≤ (Σ α)² Σ β²`. (Per `ℓ` this is `young_l1_l2`; then `Σ_ℓ x_ℓ² ≤ (Σ x_ℓ)²`.) -/
theorem conv_sum {ι : Type*} {α : ℤ → ι → ℝ} {β : ℤ → ℝ} (hα0 : ∀ a ℓ, 0 ≤ α a ℓ)
    (hβ0 : ∀ b, 0 ≤ β b) (hα : Summable fun p : ℤ × ι => α p.1 p.2)
    (hβ : Summable fun b => β b ^ 2) :
    Summable (fun t : ℤ × ι => (∑' a, α a t.2 * β (t.1 - a)) ^ 2) ∧
      ∑' t : ℤ × ι, (∑' a, α a t.2 * β (t.1 - a)) ^ 2 ≤
        (∑' p : ℤ × ι, α p.1 p.2) ^ 2 * ∑' b, β b ^ 2 ∧
      ∀ (s : ℤ) (ℓ : ι), Summable fun a => α a ℓ * β (s - a) := by
  have hαs : Summable fun q : ι × ℤ => α q.2 q.1 := hα.prod_symm
  have hαℓ : ∀ ℓ : ι, Summable fun a => α a ℓ := fun ℓ => hαs.prod_factor ℓ
  set x : ι → ℝ := fun ℓ => ∑' a, α a ℓ with hx
  have hx0 : ∀ ℓ, 0 ≤ x ℓ := fun ℓ => tsum_nonneg fun a => hα0 a ℓ
  have hxs : Summable x := hαs.prod
  have hxt : ∑' ℓ, x ℓ = ∑' p : ℤ × ι, α p.1 p.2 := by
    rw [← (Equiv.prodComm ι ℤ).tsum_eq (fun p : ℤ × ι => α p.1 p.2)]
    exact hαs.tsum_prod.symm
  set B : ℝ := ∑' b, β b ^ 2 with hB
  have hB0 : 0 ≤ B := tsum_nonneg fun b => sq_nonneg _
  -- per-ℓ Young
  have hY : ∀ ℓ : ι, Summable (fun s : ℤ => (∑' a, α a ℓ * β (s - a)) ^ 2) ∧
      ∑' s : ℤ, (∑' a, α a ℓ * β (s - a)) ^ 2 ≤ x ℓ ^ 2 * B := fun ℓ => by
    obtain ⟨-, h2, h3⟩ := young_l1_l2 (α := fun a => α a ℓ) (hα0 · ℓ) hβ0 (hαℓ ℓ) hβ
    exact ⟨h2, h3⟩
  have hX2 : Summable fun ℓ => x ℓ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun ℓ => sq_nonneg _) (fun ℓ => ?_) (hxs.mul_left (∑' ℓ, x ℓ))
    have : x ℓ ≤ ∑' ℓ, x ℓ := hxs.le_tsum ℓ (fun j _ => hx0 j)
    nlinarith [hx0 ℓ]
  have hX2t : ∑' ℓ, x ℓ ^ 2 ≤ (∑' ℓ, x ℓ) ^ 2 := by
    calc ∑' ℓ, x ℓ ^ 2 ≤ ∑' ℓ, (∑' ℓ, x ℓ) * x ℓ := by
          refine Summable.tsum_le_tsum (fun ℓ => ?_) hX2 (hxs.mul_left _)
          have : x ℓ ≤ ∑' ℓ, x ℓ := hxs.le_tsum ℓ (fun j _ => hx0 j)
          nlinarith [hx0 ℓ]
      _ = (∑' ℓ, x ℓ) ^ 2 := by rw [tsum_mul_left]; ring
  set f' : ι × ℤ → ℝ := fun q => (∑' a, α a q.1 * β (q.2 - a)) ^ 2 with hf'
  have hf'0 : ∀ q, 0 ≤ f' q := fun q => sq_nonneg _
  have hf's : Summable f' := by
    rw [summable_prod_of_nonneg hf'0]
    refine ⟨fun ℓ => (hY ℓ).1, ?_⟩
    exact Summable.of_nonneg_of_le (fun ℓ => tsum_nonneg fun s => hf'0 _)
      (fun ℓ => (hY ℓ).2) (hX2.mul_right B)
  refine ⟨?_, ?_, ?_⟩
  · have := hf's.prod_symm
    exact this
  · have e : ∑' t : ℤ × ι, (∑' a, α a t.2 * β (t.1 - a)) ^ 2 = ∑' q : ι × ℤ, f' q := by
      rw [← (Equiv.prodComm ι ℤ).tsum_eq (fun t : ℤ × ι => (∑' a, α a t.2 * β (t.1 - a)) ^ 2)]
      rfl
    rw [e, hf's.tsum_prod' (fun ℓ => (hY ℓ).1)]
    calc ∑' ℓ, ∑' s, f' (ℓ, s) ≤ ∑' ℓ, x ℓ ^ 2 * B :=
          Summable.tsum_le_tsum (fun ℓ => (hY ℓ).2)
            (Summable.of_nonneg_of_le (fun ℓ => tsum_nonneg fun s => hf'0 _)
              (fun ℓ => (hY ℓ).2) (hX2.mul_right B)) (hX2.mul_right B)
      _ = (∑' ℓ, x ℓ ^ 2) * B := by rw [tsum_mul_right]
      _ ≤ (∑' ℓ, x ℓ) ^ 2 * B := mul_le_mul_of_nonneg_right hX2t hB0
      _ = _ := by rw [hxt]
  · intro s ℓ
    exact (young_l1_l2 (α := fun a => α a ℓ) (hα0 · ℓ) hβ0 (hαℓ ℓ) hβ).1 s

end Conv

section Fib

variable {L : ℝ} [Fact (0 < L)] {k : ℕ} (i : Fin k)

/-- The external contact `(i, k+1)`: the pair `(castSucc i, last)` in `Fin (k+1)`. -/
theorem ext_ne (i : Fin k) : i.castSucc ≠ Fin.last k := (Fin.castSucc_lt_last i).ne

/-- The `x`-coordinates `ℤ^k` seen from the antidiagonal fibre: `(a, ℓ) ↦ init (fib (0,ℓ) a)`. -/
def kap (a : ℤ) (ℓ : Rest (k + 1) i.castSucc (Fin.last k) → ℤ) : Mom k :=
  fun l => fib i.castSucc (Fin.last k) (ext_ne i) (0, ℓ) a l.castSucc

theorem initM_fib (t : TIdx (k + 1) i.castSucc (Fin.last k)) (a : ℤ) :
    initM (fib i.castSucc (Fin.last k) (ext_ne i) t a) = kap i a t.2 := by
  funext l
  have hne : l.castSucc ≠ Fin.last k := (Fin.castSucc_lt_last l).ne
  simp only [initM, kap, fib, splitEquiv, Equiv.coe_fn_symm_mk]
  by_cases h1 : l.castSucc = i.castSucc
  · simp [h1]
  · simp [h1, hne]

theorem lastM_fib (t : TIdx (k + 1) i.castSucc (Fin.last k)) (a : ℤ) :
    lastM (fib i.castSucc (Fin.last k) (ext_ne i) t a) = t.1 - a :=
  fib_j _ _ _ _ _

theorem kap_i (a : ℤ) (ℓ : Rest (k + 1) i.castSucc (Fin.last k) → ℤ) : kap i a ℓ i = a := by
  have := fib_i i.castSucc (Fin.last k) (ext_ne i) (0, ℓ) a
  simpa [kap] using this

theorem kap_injective :
    Function.Injective (fun p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ) => kap i p.1 p.2) := by
  rintro ⟨a, ℓ⟩ ⟨a', ℓ'⟩ h
  have h1 : a = a' := by
    have := congrFun h i
    simpa [kap_i] using this
  subst h1
  refine Prod.ext rfl ?_
  funext r
  obtain ⟨r, hr1, hr2⟩ := r
  obtain ⟨l, rfl⟩ : ∃ l : Fin k, l.castSucc = r := by
    refine ⟨r.castPred hr2, ?_⟩; simp
  have hl := congrFun h l
  have e1 : kap i a ℓ l = ℓ ⟨l.castSucc, hr1, hr2⟩ :=
    fib_rest (ext_ne i) ((0 : ℤ), ℓ) a ⟨l.castSucc, hr1, hr2⟩
  have e2 : kap i a ℓ' l = ℓ' ⟨l.castSucc, hr1, hr2⟩ :=
    fib_rest (ext_ne i) ((0 : ℤ), ℓ') a ⟨l.castSucc, hr1, hr2⟩
  have hl' : kap i a ℓ l = kap i a ℓ' l := hl
  rw [e1, e2] at hl'
  exact hl'

/-- The slice pairing `h(b) = ⟨G, Φ(·,b)⟩`. -/
def hh (G : L2 (Mom k)) (Φ : L2 (Mom (k + 1))) (b : ℤ) : ℂ := ⟪G, slice Φ b⟫_ℂ

omit [Fact (0 < L)] in
theorem freq_add_sub (s a : ℤ) : freq L a + freq L (s - a) = freq L s := by
  unfold freq; push_cast; ring

/-- The collision trace of `(|F⟩⟨G|⊗1)Φ` along the antidiagonal fibre. -/
theorem coef_formula (F G : L2 (Mom k)) (Φ : L2 (Mom (k + 1)))
    (t : TIdx (k + 1) i.castSucc (Fin.last k)) :
    traceCoeff L i.castSucc (Fin.last k) (ext_ne i) (⇑(tensorOp (rk F G) Φ)) t =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∑' a : ℤ, (hh G Φ (t.1 - a) * (F : Mom k → ℂ) (kap i a t.2)) := by
  unfold traceCoeff
  congr 1
  refine tsum_congr fun a => ?_
  rw [tensorOp_rk_apply, lastM_fib, initM_fib]
  rfl

/-- **The smoothing-trace bound** (`eq:A1-smoothing-trace`, Fourier form).  For `F` of Wiener type and
`Φ` of finite `H¹` energy, `D_ij T_ij (|F⟩⟨G|⊗1)Φ ∈ ℓ²` with
`Σ_{(s,ℓ)} λ_s² |T(…)(s,ℓ)|² ≤ (2/L)(‖λ_iF‖₁² + ‖F‖₁²)‖G‖² ‖Φ‖²_{H¹}`. -/
theorem vkey {F : L2 (Mom k)} (hF : Wien L F) (G : L2 (Mom k)) (Φ : L2 (Mom (k + 1)))
    (hΦ : Summable fun w : Mom (k + 1) => kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2) :
    Summable (fun t : TIdx (k + 1) i.castSucc (Fin.last k) =>
      ‖(freq L t.1 : ℂ) * traceCoeff L i.castSucc (Fin.last k) (ext_ne i) (⇑(tensorOp (rk F G) Φ)) t‖ ^ 2) ∧
    ∑' t : TIdx (k + 1) i.castSucc (Fin.last k),
        ‖(freq L t.1 : ℂ) * traceCoeff L i.castSucc (Fin.last k) (ext_ne i) (⇑(tensorOp (rk F G) Φ)) t‖ ^ 2 ≤
      (2 / L) * ((∑' c : Mom k, |freq L (c i)| * ‖(F : Mom k → ℂ) c‖) ^ 2 +
        (∑' c : Mom k, ‖(F : Mom k → ℂ) c‖) ^ 2) *
        (‖G‖ ^ 2 * ∑' w : Mom (k + 1), kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2) := by
  have hL : 0 < L := Fact.out
  obtain ⟨hhs, hhe⟩ := h_bounds G Φ hΦ
  set E : ℝ := ∑' w : Mom (k + 1), kinWeight L (k + 1) w * ‖(Φ : Mom (k + 1) → ℂ) w‖ ^ 2 with hE
  set β1 : ℤ → ℝ := fun b => ‖hh G Φ b‖ with hβ1
  set β2 : ℤ → ℝ := fun b => |freq L b| * ‖hh G Φ b‖ with hβ2
  have hβ1s : Summable fun b => β1 b ^ 2 :=
    Summable.of_nonneg_of_le (fun b => sq_nonneg _) (fun b => by
      have : 0 ≤ freq L b ^ 2 := sq_nonneg _
      simp only [hβ1, hh]; nlinarith [sq_nonneg ‖⟪G, slice Φ b⟫_ℂ‖]) hhs
  have hβ2s : Summable fun b => β2 b ^ 2 :=
    Summable.of_nonneg_of_le (fun b => sq_nonneg _) (fun b => by
      simp only [hβ2, hh, mul_pow, sq_abs]
      nlinarith [sq_nonneg ‖⟪G, slice Φ b⟫_ℂ‖]) hhs
  have hB1 : ∑' b, β1 b ^ 2 ≤ ‖G‖ ^ 2 * E := by
    refine le_trans (Summable.tsum_le_tsum (fun b => ?_) hβ1s hhs) hhe
    have : 0 ≤ freq L b ^ 2 := sq_nonneg _
    simp only [hβ1, hh]; nlinarith [sq_nonneg ‖⟪G, slice Φ b⟫_ℂ‖]
  have hB2 : ∑' b, β2 b ^ 2 ≤ ‖G‖ ^ 2 * E := by
    refine le_trans (Summable.tsum_le_tsum (fun b => ?_) hβ2s hhs) hhe
    simp only [hβ2, hh, mul_pow, sq_abs]
    nlinarith [sq_nonneg ‖⟪G, slice Φ b⟫_ℂ‖]
  set g1 : Mom k → ℝ := fun c => |freq L (c i)| * ‖(F : Mom k → ℂ) c‖ with hg1
  set g2 : Mom k → ℝ := fun c => ‖(F : Mom k → ℂ) c‖ with hg2
  set α1 : ℤ → (Rest (k + 1) i.castSucc (Fin.last k) → ℤ) → ℝ :=
    fun a ℓ => |freq L a| * ‖(F : Mom k → ℂ) (kap i a ℓ)‖ with hα1
  set α2 : ℤ → (Rest (k + 1) i.castSucc (Fin.last k) → ℤ) → ℝ :=
    fun a ℓ => ‖(F : Mom k → ℂ) (kap i a ℓ)‖ with hα2
  have hα1e : ∀ p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α1 p.1 p.2 = g1 (kap i p.1 p.2) :=
    fun p => by simp only [hα1, hg1, kap_i]
  have hα2e : ∀ p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α2 p.1 p.2 = g2 (kap i p.1 p.2) :=
    fun p => rfl
  have hg1s : Summable g1 := hF.l1_freq i
  have hg2s : Summable g2 := hF.l1
  have hα1s : Summable fun p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ) => α1 p.1 p.2 := by
    simp_rw [hα1e]; exact hg1s.comp_injective (kap_injective i)
  have hα2s : Summable fun p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ) => α2 p.1 p.2 := by
    simp_rw [hα2e]; exact hg2s.comp_injective (kap_injective i)
  have hA1 : ∑' p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α1 p.1 p.2 ≤ ∑' c, g1 c := by
    simp_rw [hα1e]
    exact (hg1s.comp_injective (kap_injective i)).tsum_le_tsum_of_inj
      (fun p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ) => kap i p.1 p.2) (kap_injective i)
      (fun c _ => by simp only [hg1]; positivity) (fun _ => le_rfl) hg1s
  have hA2 : ∑' p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α2 p.1 p.2 ≤ ∑' c, g2 c := by
    simp_rw [hα2e]
    exact (hg2s.comp_injective (kap_injective i)).tsum_le_tsum_of_inj
      (fun p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ) => kap i p.1 p.2) (kap_injective i)
      (fun c _ => norm_nonneg _) (fun _ => le_rfl) hg2s
  obtain ⟨hC1s, hC1e, hC1t⟩ := conv_sum (α := α1) (β := β1)
    (fun a ℓ => by simp only [hα1]; positivity) (fun b => norm_nonneg _) hα1s hβ1s
  obtain ⟨hC2s, hC2e, hC2t⟩ := conv_sum (α := α2) (β := β2)
    (fun a ℓ => norm_nonneg _) (fun b => by simp only [hβ2]; positivity) hα2s hβ2s
  set P1 : TIdx (k + 1) i.castSucc (Fin.last k) → ℝ := fun t => ∑' a, α1 a t.2 * β1 (t.1 - a) with hP1
  set P2 : TIdx (k + 1) i.castSucc (Fin.last k) → ℝ := fun t => ∑' a, α2 a t.2 * β2 (t.1 - a) with hP2
  -- pointwise bound
  have hpt : ∀ t : TIdx (k + 1) i.castSucc (Fin.last k),
      ‖(freq L t.1 : ℂ) * traceCoeff L i.castSucc (Fin.last k) (ext_ne i) (⇑(tensorOp (rk F G) Φ)) t‖ ^ 2 ≤
        (2 / L) * (P1 t ^ 2 + P2 t ^ 2) := by
    intro t
    rw [coef_formula]
    set c : ℤ → ℂ := fun a => hh G Φ (t.1 - a) * (F : Mom k → ℂ) (kap i a t.2) with hc
    have hdom : ∀ a, ‖(freq L t.1 : ℂ) * c a‖ ≤ α1 a t.2 * β1 (t.1 - a) + α2 a t.2 * β2 (t.1 - a) := by
      intro a
      have : (freq L t.1 : ℝ) = freq L a + freq L (t.1 - a) := (freq_add_sub t.1 a).symm
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hc, norm_mul, this]
      simp only [hα1, hα2, hβ1, hβ2]
      have h1 := abs_add_le (freq L a) (freq L (t.1 - a))
      have h2 : 0 ≤ ‖hh G Φ (t.1 - a)‖ * ‖(F : Mom k → ℂ) (kap i a t.2)‖ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    have hsum1 := hC1t t.1 t.2
    have hsum2 := hC2t t.1 t.2
    have hsn : Summable fun a => ‖(freq L t.1 : ℂ) * c a‖ :=
      Summable.of_nonneg_of_le (fun a => norm_nonneg _) hdom (hsum1.add hsum2)
    have h3 : ‖(freq L t.1 : ℂ) * ∑' a, c a‖ ≤ P1 t + P2 t := by
      rw [← tsum_mul_left]
      calc ‖∑' a, (freq L t.1 : ℂ) * c a‖ ≤ ∑' a, ‖(freq L t.1 : ℂ) * c a‖ :=
            norm_tsum_le_tsum_norm hsn
        _ ≤ ∑' a, (α1 a t.2 * β1 (t.1 - a) + α2 a t.2 * β2 (t.1 - a)) :=
            hsn.tsum_le_tsum hdom (hsum1.add hsum2)
        _ = P1 t + P2 t := hsum1.tsum_add hsum2
    have hP0 : 0 ≤ P1 t + P2 t := le_trans (norm_nonneg _) h3
    have e : ‖(freq L t.1 : ℂ) * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∑' a, c a)‖ =
        (Real.sqrt L)⁻¹ * ‖(freq L t.1 : ℂ) * ∑' a, c a‖ := by
      rw [show (freq L t.1 : ℂ) * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∑' a, c a) =
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ((freq L t.1 : ℂ) * ∑' a, c a) by ring, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    rw [e, mul_pow, inv_pow, Real.sq_sqrt hL.le]
    have h4 : ‖(freq L t.1 : ℂ) * ∑' a, c a‖ ^ 2 ≤ (P1 t + P2 t) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
    calc L⁻¹ * ‖(freq L t.1 : ℂ) * ∑' a, c a‖ ^ 2 ≤ L⁻¹ * (P1 t + P2 t) ^ 2 :=
          mul_le_mul_of_nonneg_left h4 hLi
      _ ≤ L⁻¹ * (2 * (P1 t ^ 2 + P2 t ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hLi
          nlinarith [sq_nonneg (P1 t - P2 t)]
      _ = (2 / L) * (P1 t ^ 2 + P2 t ^ 2) := by field_simp
  have hnn : ∀ t : TIdx (k + 1) i.castSucc (Fin.last k),
      0 ≤ ‖(freq L t.1 : ℂ) * traceCoeff L i.castSucc (Fin.last k) (ext_ne i) (⇑(tensorOp (rk F G) Φ)) t‖ ^ 2 :=
    fun t => sq_nonneg _
  have hmaj : Summable fun t : TIdx (k + 1) i.castSucc (Fin.last k) => (2 / L) * (P1 t ^ 2 + P2 t ^ 2) :=
    (hC1s.add hC2s).mul_left _
  refine ⟨Summable.of_nonneg_of_le hnn hpt hmaj, ?_⟩
  have hS1 : ∑' t : TIdx (k + 1) i.castSucc (Fin.last k), P1 t ^ 2 ≤
      (∑' c, g1 c) ^ 2 * (‖G‖ ^ 2 * E) := by
    refine hC1e.trans ?_
    have h0 : 0 ≤ ∑' p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α1 p.1 p.2 :=
      tsum_nonneg fun p => by simp only [hα1]; positivity
    calc (∑' p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α1 p.1 p.2) ^ 2 * ∑' b, β1 b ^ 2
        ≤ (∑' c, g1 c) ^ 2 * ∑' b, β1 b ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hA1 2) (tsum_nonneg fun b => sq_nonneg _)
      _ ≤ (∑' c, g1 c) ^ 2 * (‖G‖ ^ 2 * E) := mul_le_mul_of_nonneg_left hB1 (sq_nonneg _)
  have hS2 : ∑' t : TIdx (k + 1) i.castSucc (Fin.last k), P2 t ^ 2 ≤
      (∑' c, g2 c) ^ 2 * (‖G‖ ^ 2 * E) := by
    refine hC2e.trans ?_
    have h0 : 0 ≤ ∑' p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α2 p.1 p.2 :=
      tsum_nonneg fun p => norm_nonneg _
    calc (∑' p : ℤ × (Rest (k + 1) i.castSucc (Fin.last k) → ℤ), α2 p.1 p.2) ^ 2 * ∑' b, β2 b ^ 2
        ≤ (∑' c, g2 c) ^ 2 * ∑' b, β2 b ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hA2 2) (tsum_nonneg fun b => sq_nonneg _)
      _ ≤ (∑' c, g2 c) ^ 2 * (‖G‖ ^ 2 * E) := mul_le_mul_of_nonneg_left hB2 (sq_nonneg _)
  calc ∑' t : TIdx (k + 1) i.castSucc (Fin.last k),
        ‖(freq L t.1 : ℂ) * traceCoeff L i.castSucc (Fin.last k) (ext_ne i) (⇑(tensorOp (rk F G) Φ)) t‖ ^ 2
      ≤ ∑' t : TIdx (k + 1) i.castSucc (Fin.last k), (2 / L) * (P1 t ^ 2 + P2 t ^ 2) :=
        (Summable.of_nonneg_of_le hnn hpt hmaj).tsum_le_tsum hpt hmaj
    _ = (2 / L) * (∑' t : TIdx (k + 1) i.castSucc (Fin.last k), P1 t ^ 2 +
          ∑' t : TIdx (k + 1) i.castSucc (Fin.last k), P2 t ^ 2) := by
        rw [tsum_mul_left, hC1s.tsum_add hC2s]
    _ ≤ (2 / L) * ((∑' c, g1 c) ^ 2 * (‖G‖ ^ 2 * E) + (∑' c, g2 c) ^ 2 * (‖G‖ ^ 2 * E)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = _ := by ring

end Fib

/-! ## Part 4: abstract assembly (`A^{-1/2}[B,K]A^{-1/2}` compact from the smoothing bounds) -/

section Assembly

variable {L : ℝ} [Fact (0 < L)] {m : ℕ} {i j : Fin m}

theorem traceInv_eq_symm_Sop (hij : i ≠ j) :
    traceInv (L := L) hij =
      ((collisionProductUnitary (L := L) i j).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (Sop hij) := by
  ext y t
  show (traceInv hij y : TIdx m i j → ℂ) t = _
  have : ((collisionProductUnitary (L := L) i j).symm (Sop hij y) : L2 (TIdx m i j)) = traceInv hij y := by
    show (collisionProductUnitary (L := L) i j).symm ((collisionProductUnitary (L := L) i j)
      (traceInv hij y)) = _
    exact LinearIsometryEquiv.symm_apply_apply _ _
  rw [← this]; rfl

theorem traceInv_adjoint_isCompact (hij : i ≠ j) :
    IsCompactOperator (ContinuousLinearMap.adjoint (traceInv (L := L) hij)) := by
  rw [traceInv_eq_symm_Sop hij, ContinuousLinearMap.adjoint_comp]
  exact (Sop_adjoint_isCompact hij).comp_clm _

/-- `A^{-1/2} B_ij K` equals `(T_ij A^{-1/2})^* V` once `V = D_ij T_ij K A^{-1/2}` is a bounded
operator into `ℓ²` (the source's "`D_ij T_ij (J⊗1) A^{-1/2}` is bounded"). -/
theorem Bsand_comp_eq (hij : i ≠ j) (K : L2TN L m →L[ℂ] L2TN L m)
    (V : L2TN L m →L[ℂ] L2 (TIdx m i j))
    (hV : ∀ (y : L2TN L m) (t : TIdx m i j),
      (freq L t.1 : ℂ) * (traceInv hij (K y) : TIdx m i j → ℂ) t = (V y : TIdx m i j → ℂ) t) :
    (Bsand hij).comp K = (ContinuousLinearMap.adjoint (traceInv hij)).comp V := by
  ext y : 1
  apply ext_inner_left ℂ
  intro x
  show ⟪x, Bsand hij (K y)⟫_ℂ = ⟪x, (ContinuousLinearMap.adjoint (traceInv hij)) (V y)⟫_ℂ
  rw [← Bsand_symm, Bsand_inner, ContinuousLinearMap.adjoint_inner_right, inner_eq_tsum']
  refine tsum_congr fun t => ?_
  rw [← hV y t]

/-- **Assembly of the commutator clause.** If `V, V'` are the bounded smoothing operators of `K, K'`
(`D_ij T_ij K A^{-1/2} = V`, `D_ij T_ij K' A^{-1/2} = V'`), then the sandwiched commutator
`A^{-1/2}B_ij K A^{-1/2} − (A^{-1/2}B_ij K' A^{-1/2})^{*}`-form, i.e. `Bsand K − K'^* Bsand`, is
compact. -/
theorem comm_isCompact (hij : i ≠ j) (K K' : L2TN L m →L[ℂ] L2TN L m)
    (V V' : L2TN L m →L[ℂ] L2 (TIdx m i j))
    (hV : ∀ (y : L2TN L m) (t : TIdx m i j),
      (freq L t.1 : ℂ) * (traceInv hij (K y) : TIdx m i j → ℂ) t = (V y : TIdx m i j → ℂ) t)
    (hV' : ∀ (y : L2TN L m) (t : TIdx m i j),
      (freq L t.1 : ℂ) * (traceInv hij (K' y) : TIdx m i j → ℂ) t = (V' y : TIdx m i j → ℂ) t) :
    IsCompactOperator ((Bsand hij).comp K - (ContinuousLinearMap.adjoint K').comp (Bsand hij)) := by
  have h1 := Bsand_comp_eq hij K V hV
  have h2 := Bsand_comp_eq hij K' V' hV'
  have h3 : (ContinuousLinearMap.adjoint K').comp (Bsand hij) =
      (ContinuousLinearMap.adjoint V').comp (traceInv hij) := by
    have := congrArg ContinuousLinearMap.adjoint h2
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      (Bsand_isSelfAdjoint hij).adjoint_eq, ContinuousLinearMap.adjoint_adjoint] at this
    exact this
  rw [h1, h3]
  exact ((traceInv_adjoint_isCompact hij).comp_clm V).sub
    ((traceInv_isCompact hij).clm_comp (ContinuousLinearMap.adjoint V'))

end Assembly

/-! ## Part 5: `K̃ = A^{1/2}(|F⟩⟨G|⊗1)A^{-1/2}` and `V = D_ij T_ij K̃` for an external contact -/

section External

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- The coefficient array of `A^{-1/2} y` (an element of `H¹(𝕋_L^{k+1})`). -/
def Phi (y : L2TN L (k + 1)) : L2 (Mom (k + 1)) :=
  momUnitary L (k + 1) (PhysH1.valCLM ((PhysH1.unitary (L := L) (k := k + 1)).symm y))

theorem Phi_apply (y : L2TN L (k + 1)) (w : Mom (k + 1)) :
    (Phi y : Mom (k + 1) → ℂ) w = coeffFun ((PhysH1.unitary (L := L) (k := k + 1)).symm y) w := rfl

theorem Phi_add (y y' : L2TN L (k + 1)) : Phi (y + y') = Phi y + Phi y' := by
  unfold Phi; rw [map_add, map_add, map_add]

theorem Phi_smul (c : ℂ) (y : L2TN L (k + 1)) : Phi (c • y) = c • Phi y := by
  unfold Phi; rw [map_smul, map_smul, map_smul]

theorem Phi_energy (y : L2TN L (k + 1)) :
    Summable (fun w : Mom (k + 1) => kinWeight L (k + 1) w * ‖(Phi y : Mom (k + 1) → ℂ) w‖ ^ 2) ∧
      ∑' w : Mom (k + 1), kinWeight L (k + 1) w * ‖(Phi y : Mom (k + 1) → ℂ) w‖ ^ 2 = ‖y‖ ^ 2 := by
  have h1 := summable_coeffFun_form ((PhysH1.unitary (L := L) (k := k + 1)).symm y)
  have h2 := tsum_coeffFun_form ((PhysH1.unitary (L := L) (k := k + 1)).symm y)
  rw [norm_unitary_symm] at h2
  exact ⟨h1, h2⟩

variable {F G : L2 (Mom k)}

theorem memL2_Ktil (hF : Wien L F) (y : L2TN L (k + 1)) :
    Memℓp (fun w : Mom (k + 1) => (kinSqrt L (k + 1) w : ℂ) *
      (tensorOp (rk F G) (Phi y) : Mom (k + 1) → ℂ) w) 2 := by
  rw [memL2_iff]
  refine (energy_rk (G := G) hF (Phi y) (Phi_energy y).1).1.congr fun w => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, kinSqrt_sq]

/-- `K̃ = A^{1/2}(|F⟩⟨G|⊗1)A^{-1/2}` on `L²(𝕋_L^{k+1})`, bounded because `(|F⟩⟨G|⊗1)` preserves
`H¹` (`energy_rk`). -/
def Ktil (G : L2 (Mom k)) (hF : Wien L F) : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1) :=
  LinearMap.mkContinuous
    { toFun := fun y => (momUnitary L (k + 1)).symm
        ⟨fun w => (kinSqrt L (k + 1) w : ℂ) * (tensorOp (rk F G) (Phi y) : Mom (k + 1) → ℂ) w,
          memL2_Ktil hF y⟩
      map_add' := fun y y' => by
        rw [← map_add]; congr 1
        apply Subtype.ext; funext w
        simp only [Phi_add, map_add, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c y => by
        rw [← map_smul]; congr 1
        apply Subtype.ext; funext w
        simp only [Phi_smul, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    (Real.sqrt (((∑' c : Mom k, kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2) +
          ∑' c : Mom k, ‖(F : Mom k → ℂ) c‖ ^ 2) * ‖G‖ ^ 2)) (fun y => by
      have hE := Phi_energy y
      obtain ⟨-, hbd⟩ := energy_rk (G := G) hF (Phi y) hE.1
      rw [hE.2] at hbd
      have h0 : 0 ≤ ((∑' c : Mom k, kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2) +
          ∑' c : Mom k, ‖(F : Mom k → ℂ) c‖ ^ 2) * ‖G‖ ^ 2 := by
        have hk0 : ∀ c : Mom k, 1 ≤ kinWeight L k c := fun c => by
          unfold kinWeight
          have : 0 ≤ ∑ j, freq L (c j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
          linarith
        have a1 : 0 ≤ ∑' c : Mom k, kinWeight L k c * ‖(F : Mom k → ℂ) c‖ ^ 2 :=
          tsum_nonneg fun c => mul_nonneg (by linarith [hk0 c]) (sq_nonneg _)
        have a2 : 0 ≤ ∑' c : Mom k, ‖(F : Mom k → ℂ) c‖ ^ 2 := tsum_nonneg fun c => sq_nonneg _
        positivity
      refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 ?_
      rw [mul_pow, Real.sq_sqrt h0]
      show ‖(momUnitary L (k + 1)).symm (⟨fun w => (kinSqrt L (k + 1) w : ℂ) *
        (tensorOp (rk F G) (Phi y) : Mom (k + 1) → ℂ) w, memL2_Ktil hF y⟩ : L2 (Mom (k + 1)))‖ ^ 2 ≤ _
      rw [LinearIsometryEquiv.norm_map, norm_sq_eq_tsum]
      rw [mul_assoc]
      refine le_trans (le_of_eq (tsum_congr fun w => ?_)) hbd
      show ‖(kinSqrt L (k + 1) w : ℂ) * (tensorOp (rk F G) (Phi y) : Mom (k + 1) → ℂ) w‖ ^ 2 = _
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, kinSqrt_sq])

theorem momUnitary_Ktil (hF : Wien L F) (y : L2TN L (k + 1)) (w : Mom (k + 1)) :
    (momUnitary L (k + 1) (Ktil G hF y) : Mom (k + 1) → ℂ) w =
      (kinSqrt L (k + 1) w : ℂ) * (tensorOp (rk F G) (Phi y) : Mom (k + 1) → ℂ) w := by
  show ((momUnitary L (k + 1)) ((momUnitary L (k + 1)).symm _) : Mom (k + 1) → ℂ) w = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- The coefficients of `A^{-1/2} K̃ y` are those of `(|F⟩⟨G|⊗1) A^{-1/2} y`. -/
theorem coeffFun_Ktil (hF : Wien L F) (y : L2TN L (k + 1)) (w : Mom (k + 1)) :
    coeffFun ((PhysH1.unitary (L := L) (k := k + 1)).symm (Ktil G hF y)) w =
      (tensorOp (rk F G) (Phi y) : Mom (k + 1) → ℂ) w := by
  have h := PhysH1.unitary_coeff ((PhysH1.unitary (L := L) (k := k + 1)).symm (Ktil G hF y)) w
  rw [LinearIsometryEquiv.apply_symm_apply, momUnitary_Ktil] at h
  have hne : (kinSqrt L (k + 1) w : ℂ) ≠ 0 := by
    have := one_le_kinSqrt L (k + 1) w
    exact_mod_cast (by linarith : kinSqrt L (k + 1) w ≠ 0)
  exact (mul_left_cancel₀ hne h).symm

theorem traceInv_Ktil (hF : Wien L F) (i : Fin k) (y : L2TN L (k + 1))
    (t : TIdx (k + 1) i.castSucc (Fin.last k)) :
    (traceInv (ext_ne i) (Ktil G hF y) : TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t =
      traceCoeff L i.castSucc (Fin.last k) (ext_ne i) (⇑(tensorOp (rk F G) (Phi y))) t := by
  show traceCoeff L _ _ _ (coeffFun ((PhysH1.unitary (L := L) (k := k + 1)).symm (Ktil G hF y))) t = _
  congr 1
  funext w
  exact coeffFun_Ktil hF y w

theorem memL2_Vop (hF : Wien L F) (i : Fin k) (y : L2TN L (k + 1)) :
    Memℓp (fun t : TIdx (k + 1) i.castSucc (Fin.last k) => (freq L t.1 : ℂ) *
      (traceInv (ext_ne i) (Ktil G hF y) : TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t) 2 := by
  rw [memL2_iff]
  refine (vkey i hF G (Phi y) (Phi_energy y).1).1.congr fun t => ?_
  rw [traceInv_Ktil hF i y t]

/-- `V = D_ij T_ij (|F⟩⟨G|⊗1) A^{-1/2}` for the external contact `(i, k+1)`: bounded from
`L²(𝕋_L^{k+1})` into `ℓ²(TIdx)` (the smoothing bound `eq:A1-smoothing-trace`). -/
def Vop (G : L2 (Mom k)) (hF : Wien L F) (i : Fin k) :
    L2TN L (k + 1) →L[ℂ] L2 (TIdx (k + 1) i.castSucc (Fin.last k)) :=
  LinearMap.mkContinuous
    { toFun := fun y => ⟨fun t => (freq L t.1 : ℂ) *
        (traceInv (ext_ne i) (Ktil G hF y) : TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t,
        memL2_Vop hF i y⟩
      map_add' := fun y y' => by
        apply Subtype.ext; funext t
        simp only [map_add, lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c y => by
        apply Subtype.ext; funext t
        simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
    (Real.sqrt ((2 / L) * ((∑' c : Mom k, |freq L (c i)| * ‖(F : Mom k → ℂ) c‖) ^ 2 +
        (∑' c : Mom k, ‖(F : Mom k → ℂ) c‖) ^ 2) * ‖G‖ ^ 2)) (fun y => by
      have hL : 0 < L := Fact.out
      have hE := Phi_energy y
      obtain ⟨-, hbd⟩ := vkey i hF G (Phi y) hE.1
      rw [hE.2] at hbd
      have h0 : 0 ≤ (2 / L) * ((∑' c : Mom k, |freq L (c i)| * ‖(F : Mom k → ℂ) c‖) ^ 2 +
          (∑' c : Mom k, ‖(F : Mom k → ℂ) c‖) ^ 2) * ‖G‖ ^ 2 := by positivity
      refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1 ?_
      rw [mul_pow, Real.sq_sqrt h0, norm_sq_eq_tsum, mul_assoc]
      refine le_trans (le_of_eq (tsum_congr fun t => ?_)) hbd
      show ‖(freq L t.1 : ℂ) * (traceInv (ext_ne i) (Ktil G hF y) :
        TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t‖ ^ 2 = _
      rw [traceInv_Ktil hF i y t])

theorem Vop_spec (hF : Wien L F) (i : Fin k) (y : L2TN L (k + 1))
    (t : TIdx (k + 1) i.castSucc (Fin.last k)) :
    (freq L t.1 : ℂ) * (traceInv (ext_ne i) (Ktil G hF y) :
        TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t =
      (Vop G hF i y : TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t := rfl

end External

open QuantumNLS.WeakDerivatives QuantumNLS.ProductWeakDerivatives
  QuantumNLS.ProductSecondDerivatives

/-! ## Part 6: smooth profiles have Wiener-summable Fourier coefficients -/

section Smooth

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- The `L²(𝕋_L^k)` class of a smooth lattice-periodic function. -/
def cls {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) : L2TN L k :=
  (memLp_liftK hφ.smooth.continuous).toLp _

theorem coe_cls {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    (cls hφ : (Fin k → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L k] liftK φ :=
  MemLp.coeFn_toLp _

theorem momUnitary_cls {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) (w : Mom k) :
    (momUnitary L k (cls hφ) : Mom k → ℂ) w = pairK (L := L) (liftK φ) (-w) := by
  rw [momUnitary_apply_eq_inner, MeasureTheory.L2.inner_def]
  unfold pairK
  refine integral_congr_ae ?_
  filter_upwards [coeFn_prodMode (L := L) w, coe_cls hφ] with y h1 h2
  rw [RCLike.inner_apply', h1, h2, map_prod]
  simp only [conj_mode, Pi.neg_apply]

theorem momUnitary_cls_pderiv {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) (j : Fin k) (w : Mom k) :
    (momUnitary L k (cls (pderiv_isTest hφ j)) : Mom k → ℂ) w =
      ikn L (w j) * (momUnitary L k (cls hφ) : Mom k → ℂ) w := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := j.pos; omega⟩
  rw [momUnitary_cls, momUnitary_cls, pairK_pderiv j hφ (-w)]
  simp only [Pi.neg_apply, ikn, freq_neg]
  push_cast
  ring

theorem test_sub {φ ψ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hψ : IsTorusTest L ψ) :
    IsTorusTest L (fun x => φ x - ψ x) :=
  ⟨hφ.smooth.sub hψ.smooth, fun x m => by simp only [hφ.periodic x m, hψ.periodic x m]⟩

theorem cls_sub {φ ψ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) (hψ : IsTorusTest L ψ) :
    cls (test_sub hφ hψ) = cls hφ - cls hψ := by
  apply Lp.ext
  filter_upwards [coe_cls (test_sub hφ hψ), coe_cls hφ, coe_cls hψ,
    Lp.coeFn_sub (cls hφ) (cls hψ)] with y h h1 h2 h3
  rw [h, h3]
  simp only [Pi.sub_apply, h1, h2]
  rfl

theorem exists_weight_mul {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) (S : Finset (Fin k)) :
    ∃ (g : (Fin k → ℝ) → ℂ) (hg : IsTorusTest L g), ∀ w : Mom k,
      (momUnitary L k (cls hg) : Mom k → ℂ) w =
        (((∏ l ∈ S, (1 + freq L (w l) ^ 2) : ℝ)) : ℂ) * (momUnitary L k (cls hφ) : Mom k → ℂ) w := by
  induction S using Finset.induction_on with
  | empty => exact ⟨φ, hφ, fun w => by simp⟩
  | insert l S hl ih =>
    obtain ⟨g, hg, hcoef⟩ := ih
    refine ⟨fun x => g x - pderiv l (pderiv l g) x,
      test_sub hg (pderiv_isTest (pderiv_isTest hg l) l), fun w => ?_⟩
    rw [cls_sub hg (pderiv_isTest (pderiv_isTest hg l) l), map_sub, lp.coeFn_sub, Pi.sub_apply,
      momUnitary_cls_pderiv (pderiv_isTest hg l) l w, momUnitary_cls_pderiv hg l w, hcoef w,
      Finset.prod_insert hl]
    have : ikn L (w l) * ikn L (w l) = -((freq L (w l) : ℂ)) ^ 2 := by
      unfold ikn
      linear_combination ((freq L (w l) : ℂ) ^ 2) * Complex.I_sq
    push_cast
    linear_combination (-(∏ l ∈ S, (1 + (freq L (w l) : ℂ) ^ 2)) *
      (momUnitary L k (cls hφ) : Mom k → ℂ) w) * this

theorem one_add_sum_le_prod {ι : Type*} (S : Finset ι) (a : ι → ℝ) (ha : ∀ l, 0 ≤ a l) :
    1 + ∑ l ∈ S, a l ≤ ∏ l ∈ S, (1 + a l) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert l S hl ih =>
    rw [Finset.sum_insert hl, Finset.prod_insert hl]
    have h0 : 0 ≤ ∑ l ∈ S, a l := Finset.sum_nonneg fun l _ => ha l
    nlinarith [ha l]

theorem wien_weight_sq (c : Mom k) :
    (1 + ∑ l, |freq L (c l)|) ^ 2 ≤ 2 * ((k : ℝ) + 1) * (1 + ∑ l, freq L (c l) ^ 2) := by
  have h1 : (∑ l, |freq L (c l)|) ^ 2 ≤ (k : ℝ) * ∑ l, |freq L (c l)| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k)))
      (f := fun l => |freq L (c l)|)
    simpa using this
  have h2 : ∑ l, |freq L (c l)| ^ 2 = ∑ l, freq L (c l) ^ 2 := by simp [sq_abs]
  rw [h2] at h1
  have h3 : 0 ≤ ∑ l, freq L (c l) ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have h4 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [sq_nonneg (∑ l, |freq L (c l)| - 1), mul_nonneg h4 h3]

/-- **Smooth lattice-periodic profiles have Wiener-weighted summable Fourier coefficients**
(`Σ_c (1 + Σ_l |2πc_l/L|) |φ̂(c)| < ∞`): `∏_l (1 − ∂_l²) φ` is smooth, hence in `L²`. -/
theorem wien_cls {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    Wien L (momUnitary L k (cls hφ)) := by
  have hL : 0 < L := Fact.out
  obtain ⟨g, hg, hcoef⟩ := exists_weight_mul hφ Finset.univ
  set Fh := momUnitary L k (cls hφ) with hFh
  set B : Mom k → ℝ := fun w => ∏ l, (1 + freq L (w l) ^ 2) with hB
  have hBpos : ∀ w, 0 < B w := fun w => Finset.prod_pos fun l _ => by positivity
  have hy : Summable fun w : Mom k => (B w * ‖(Fh : Mom k → ℂ) w‖) ^ 2 := by
    refine (summable_sq (momUnitary L k (cls hg))).congr fun w => ?_
    rw [hcoef w, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hBpos w).le]
  have hx : Summable fun w : Mom k => 2 * ((k : ℝ) + 1) * (∏ l, (1 + freq L (w l) ^ 2)⁻¹) := by
    have := (QuantumNLS.ProductEnergyPreparation.prod_hasSum_fintype (ι := Fin k)
      (fun _ n => (1 + freq L n ^ 2)⁻¹) (fun _ n => by positivity)
      (fun _ => summable_f04 hL)).summable
    exact this.mul_left _
  have hxsq : ∀ w : Mom k, ((1 + ∑ l, |freq L (w l)|) / B w) ^ 2 ≤
      2 * ((k : ℝ) + 1) * (∏ l, (1 + freq L (w l) ^ 2)⁻¹) := by
    intro w
    have hp : (∏ l, (1 + freq L (w l) ^ 2)⁻¹) = (B w)⁻¹ := by
      rw [hB]; simp only [Finset.prod_inv_distrib]
    rw [hp, div_pow]
    have h1 := wien_weight_sq (L := L) w
    have h2 := one_add_sum_le_prod (Finset.univ : Finset (Fin k)) (fun l => freq L (w l) ^ 2)
      (fun l => sq_nonneg _)
    have hBp := hBpos w
    have h5 : (1 + ∑ l, |freq L (w l)|) ^ 2 ≤ 2 * ((k : ℝ) + 1) * B w := by
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [div_le_iff₀ (by positivity)]
    calc (1 + ∑ l, |freq L (w l)|) ^ 2 ≤ 2 * ((k : ℝ) + 1) * B w := h5
      _ = 2 * ((k : ℝ) + 1) * (B w)⁻¹ * B w ^ 2 := by field_simp
  have hxs : Summable fun w : Mom k => ((1 + ∑ l, |freq L (w l)|) / B w) ^ 2 :=
    Summable.of_nonneg_of_le (fun w => sq_nonneg _) hxsq hx
  unfold Wien
  refine Summable.of_nonneg_of_le (fun w => by
    have := wien_omega_pos (L := L) w; positivity) (fun w => ?_) ((hxs.add hy).mul_left (1 / 2 : ℝ))
  have hBp := hBpos w
  have e : (1 + ∑ l, |freq L (w l)|) * ‖(Fh : Mom k → ℂ) w‖ =
      ((1 + ∑ l, |freq L (w l)|) / B w) * (B w * ‖(Fh : Mom k → ℂ) w‖) := by
    field_simp
  rw [e]
  nlinarith [sq_nonneg (((1 + ∑ l, |freq L (w l)|) / B w) - (B w * ‖(Fh : Mom k → ℂ) w‖))]

end Smooth


/-! ## Part 7: `J ⊗ Id` on the actual carrier `L²(𝕋_L^{k+1})` -/

section JI

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- Complex-valued re-summation over `ℤ^{k+1} = ℤ^k × ℤ`. -/
theorem sum_snocC {G : Mom (k + 1) → ℂ} (hG : Summable G) :
    Summable (fun b : ℤ => ∑' c : Mom k, G (Fin.snoc c b)) ∧
      ∑' w, G w = ∑' b : ℤ, ∑' c : Mom k, G (Fin.snoc c b) := by
  have hs : Summable (G ∘ snocE k) := (snocE k).summable_iff.2 hG
  refine ⟨hs.prod, ?_⟩
  rw [← (snocE k).tsum_eq G]
  exact hs.tsum_prod

theorem slice_apply' (c : L2 (Mom (k + 1))) (b : ℤ) (c' : Mom k) :
    (slice c b : Mom k → ℂ) c' = (c : Mom (k + 1) → ℂ) (Fin.snoc c' b) := rfl

/-- Parseval along the splitting: `⟨u, v⟩ = Σ_b ⟨u(·,b), v(·,b)⟩`. -/
theorem inner_slices (u v : L2 (Mom (k + 1))) :
    ⟪u, v⟫_ℂ = ∑' b : ℤ, ⟪slice u b, slice v b⟫_ℂ := by
  have h := sum_snocC (hasSum_inner' u v).summable
  rw [inner_eq_tsum', h.2]
  refine tsum_congr fun b => ?_
  rw [inner_eq_tsum']
  rfl

theorem slice_tensorOp (A : L2 (Mom k) →L[ℂ] L2 (Mom k)) (c : L2 (Mom (k + 1))) (b : ℤ) :
    slice (tensorOp A c) b = A (slice c b) := by
  apply Subtype.ext; funext c'
  rw [slice_apply', tensorOp_apply, lastM_snoc, initM_snoc]

/-- `⟨x, (A ⊗ 1) y⟩ = ⟨(A^* ⊗ 1) x, y⟩`. -/
theorem tensorOp_adjoint (A : L2 (Mom k) →L[ℂ] L2 (Mom k)) (x y : L2 (Mom (k + 1))) :
    ⟪x, tensorOp A y⟫_ℂ = ⟪tensorOp (ContinuousLinearMap.adjoint A) x, y⟫_ℂ := by
  rw [inner_slices, inner_slices]
  refine tsum_congr fun b => ?_
  rw [slice_tensorOp, slice_tensorOp, ContinuousLinearMap.adjoint_inner_left]

/-- The coefficient-level operator `J` on `ℓ²(ℤ^k)` corresponding to `J` on `L²(𝕋_L^k)`. -/
def Jell (J : L2TN L k →L[ℂ] L2TN L k) : L2 (Mom k) →L[ℂ] L2 (Mom k) :=
  ((momUnitary L k).toContinuousLinearEquiv : L2TN L k →L[ℂ] L2 (Mom k)).comp
    (J.comp ((momUnitary L k).symm.toContinuousLinearEquiv : L2 (Mom k) →L[ℂ] L2TN L k))

theorem Jell_momUnitary (J : L2TN L k →L[ℂ] L2TN L k) (x : L2TN L k) :
    Jell J (momUnitary L k x) = momUnitary L k (J x) := by
  simp [Jell]

/-- **`J ⊗ Id` on `L²(𝕋_L^{k+1}) = L²(𝕋_L^k) ⊗ L²(𝕋_L)`** (the last variable is the untouched one),
realised through the Fourier carrier unitary: `JI J = U⁻¹ (Jℓ ⊗ 1) U`, with
`(Jℓ ⊗ 1) c (·, b) = Jℓ (c(·, b))`. -/
def JI (J : L2TN L k →L[ℂ] L2TN L k) : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1) :=
  ((momUnitary L (k + 1)).symm.toContinuousLinearEquiv : L2 (Mom (k + 1)) →L[ℂ] _).comp
    ((tensorOp (Jell J)).comp
      ((momUnitary L (k + 1)).toContinuousLinearEquiv : L2TN L (k + 1) →L[ℂ] _))

theorem momUnitary_JI (J : L2TN L k →L[ℂ] L2TN L k) (x : L2TN L (k + 1)) :
    momUnitary L (k + 1) (JI J x) = tensorOp (Jell J) (momUnitary L (k + 1) x) := by
  simp [JI]

/-- The elementary tensor `f_1 ⊗ … ⊗ f_k ⊗ u` of `L²(𝕋_L^{k+1})`. -/
def elem (f : Fin k → L2T L) (u : L2T L) : L2TN L (k + 1) := prodLp (Fin.snoc f u : Fin (k + 1) → L2T L)

theorem momUnitary_elem (f : Fin k → L2T L) (u : L2T L) (w : Mom (k + 1)) :
    (momUnitary L (k + 1) (elem f u) : Mom (k + 1) → ℂ) w =
      (momUnitary L k (prodLp f) : Mom k → ℂ) (initM w) * fourierL2 L u (lastM w) := by
  rw [elem, momUnitary_prodLp, momUnitary_prodLp, Fin.prod_univ_castSucc]
  simp [initM, lastM]

theorem slice_elem (f : Fin k → L2T L) (u : L2T L) (b : ℤ) :
    slice (momUnitary L (k + 1) (elem f u)) b = fourierL2 L u b • momUnitary L k (prodLp f) := by
  apply Subtype.ext; funext c'
  rw [slice_apply', momUnitary_elem, initM_snoc, lastM_snoc]
  simp [mul_comm]

/-- **Matrix elements of `J ⊗ Id` on elementary tensors**:
`⟨a ⊗ u, (J ⊗ Id)(a' ⊗ u')⟩ = ⟨a, J a'⟩ ⟨u, u'⟩`. -/
theorem JI_matrix (J : L2TN L k →L[ℂ] L2TN L k) (f f' : Fin k → L2T L) (u u' : L2T L) :
    ⟪elem f u, JI J (elem f' u')⟫_ℂ = ⟪prodLp f, J (prodLp f')⟫_ℂ * ⟪u, u'⟫_ℂ := by
  rw [← (momUnitary L (k + 1)).inner_map_map, momUnitary_JI, inner_slices]
  have h1 : ∀ b : ℤ, ⟪slice (momUnitary L (k + 1) (elem f u)) b,
      slice (tensorOp (Jell J) (momUnitary L (k + 1) (elem f' u'))) b⟫_ℂ =
      (conj (fourierL2 L u b : ℂ) * fourierL2 L u' b) * ⟪prodLp f, J (prodLp f')⟫_ℂ := by
    intro b
    rw [slice_tensorOp, slice_elem, slice_elem, map_smul, inner_smul_left, inner_smul_right,
      Jell_momUnitary, (momUnitary L k).inner_map_map]
    ring
  rw [tsum_congr h1, tsum_mul_right, ← (fourierL2 L).inner_map_map u u',
    inner_eq_tsum' (fourierL2 L u) (fourierL2 L u')]
  ring

theorem Jell_adjoint (J : L2TN L k →L[ℂ] L2TN L k) :
    ContinuousLinearMap.adjoint (Jell J) = Jell (ContinuousLinearMap.adjoint J) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff (Jell (ContinuousLinearMap.adjoint J)) (Jell J)).2
    fun x y => ?_).symm
  obtain ⟨a, rfl⟩ := (momUnitary L k).surjective x
  obtain ⟨b, rfl⟩ := (momUnitary L k).surjective y
  rw [Jell_momUnitary, Jell_momUnitary, (momUnitary L k).inner_map_map,
    (momUnitary L k).inner_map_map, ContinuousLinearMap.adjoint_inner_left]

/-- **`(J ⊗ Id)^* = J^* ⊗ Id`** on the actual carrier. -/
theorem JI_adjoint (J : L2TN L k →L[ℂ] L2TN L k) (x y : L2TN L (k + 1)) :
    ⟪x, JI J y⟫_ℂ = ⟪JI (ContinuousLinearMap.adjoint J) x, y⟫_ℂ := by
  rw [← (momUnitary L (k + 1)).inner_map_map, momUnitary_JI, tensorOp_adjoint,
    ← (momUnitary L (k + 1)).inner_map_map (JI _ x) y, momUnitary_JI, Jell_adjoint]

theorem JI_add (J K : L2TN L k →L[ℂ] L2TN L k) : JI (J + K) = JI J + JI K := by
  ext1 x
  apply (momUnitary L (k + 1)).injective
  rw [add_apply, map_add, momUnitary_JI, momUnitary_JI, momUnitary_JI]
  have : Jell (J + K) = Jell J + Jell K := by
    ext1 v
    simp [Jell]
  rw [this, tensorOp_add]

/-- Elementary tensors determine a continuous linear map (`prodLp` is total). -/
theorem clm_ext_prodLp {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T S : L2TN L N →L[ℂ] E} (h : ∀ g : Fin N → L2T L, T (prodLp g) = S (prodLp g)) : T = S := by
  ext1 x
  obtain ⟨ψ, rfl⟩ := (physUnitary (L := L) (N := N)).surjective x
  induction ψ using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (T.continuous.comp physUnitary.continuous)
      (S.continuous.comp physUnitary.continuous)
  | ih a =>
    induction a using QuantumNLS.TensorCarrier.AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      rw [UniformSpace.Completion.coe_smul, map_smul, map_smul, map_smul,
        physUnitary_ptprod]
      congr 1
      exact h f
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add, map_add, map_add, map_add, hx, hy]

theorem elem_surj (g : Fin (k + 1) → L2T L) : prodLp g = elem (Fin.init g) (g (Fin.last k)) := by
  rw [elem, Fin.snoc_init_self]

/-- **`J ⊗ Id` is determined by its matrix elements on elementary tensors**
`⟨a ⊗ u, T (a' ⊗ u')⟩ = ⟨a, J a'⟩⟨u, u'⟩`, and `JI J` is the unique bounded operator with them. -/
theorem JI_unique (J : L2TN L k →L[ℂ] L2TN L k) (T : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1))
    (hT : ∀ (f f' : Fin k → L2T L) (u u' : L2T L),
      ⟪elem f u, T (elem f' u')⟫_ℂ = ⟪prodLp f, J (prodLp f')⟫_ℂ * ⟪u, u'⟫_ℂ) : T = JI J := by
  refine clm_ext_prodLp fun g' => ?_
  set d := T (prodLp g') - JI J (prodLp g') with hd
  have h0 : ∀ g : Fin (k + 1) → L2T L, ⟪prodLp g, d⟫_ℂ = 0 := by
    intro g
    rw [hd, inner_sub_right, elem_surj g, elem_surj g', hT, JI_matrix, sub_self]
  have h1 : (innerSL ℂ d : L2TN L (k + 1) →L[ℂ] ℂ) = 0 := by
    refine clm_ext_prodLp fun g => ?_
    simp only [innerSL_apply_apply, zero_apply]
    rw [← inner_conj_symm, h0 g, map_zero]
  have h2 : ⟪d, d⟫_ℂ = 0 := by
    have := congrArg (fun F => F d) h1
    simpa using this
  have := inner_self_eq_zero.1 h2
  exact sub_eq_zero.1 this

end JI


section JIsum

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

theorem tensorOp_zero : tensorOp (0 : L2 (Mom k) →L[ℂ] L2 (Mom k)) = 0 := by
  ext1 c
  apply Subtype.ext; funext w
  simp [tensorOp_apply]

theorem JI_zero : JI (0 : L2TN L k →L[ℂ] L2TN L k) = 0 := by
  ext1 x
  apply (momUnitary L (k + 1)).injective
  rw [momUnitary_JI]
  have : Jell (0 : L2TN L k →L[ℂ] L2TN L k) = 0 := by ext1 v; simp [Jell]
  rw [this, tensorOp_zero]
  simp

theorem JI_sum {ι : Type*} (s : Finset ι) (J : ι → L2TN L k →L[ℂ] L2TN L k) :
    JI (∑ r ∈ s, J r) = ∑ r ∈ s, JI (J r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using JI_zero
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.sum_insert hr, JI_add, ih]

theorem Jell_rankOne (a b : L2TN L k) :
    Jell (InnerProductSpace.rankOne ℂ a b) =
      rk (momUnitary L k a) (momUnitary L k b) := by
  ext1 v
  obtain ⟨c, rfl⟩ := (momUnitary L k).surjective v
  rw [Jell_momUnitary]
  simp [InnerProductSpace.rankOne_apply, (momUnitary L k).inner_map_map]

end JIsum

/-! ## Part 8: finite-rank smooth-kernel operators and the external commutator -/

section ExternalCommutator

variable {L : ℝ} [Fact (0 < L)] {k n : ℕ}
variable (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
  (hg : ∀ r, IsTorusTest L (g r))

/-- **Finite-rank operator with smooth kernel** `J = Σ_r |f_r⟩⟨g_r|`, `f_r, g_r` smooth lattice-periodic
(kernel `Σ_r f_r(x) \overline{g_r(x')}`). -/
def Jsum : L2TN L k →L[ℂ] L2TN L k :=
  ∑ r, InnerProductSpace.rankOne ℂ (cls (hf r)) (cls (hg r))

theorem adjoint_Jsum :
    ContinuousLinearMap.adjoint (Jsum f g hf hg) = Jsum g f hg hf := by
  unfold Jsum
  rw [map_sum]
  simp [InnerProductSpace.adjoint_rankOne]

/-- `K = A^{1/2}(J ⊗ Id)A^{-1/2}` (finite sum of the rank-one operators of Part 5). -/
def KT : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1) :=
  ∑ r, Ktil (momUnitary L k (cls (hg r))) (wien_cls (hf r))

/-- `V = D_ij T_ij (J ⊗ Id) A^{-1/2}` for the external contact `(i, k+1)`. -/
def VT (i : Fin k) : L2TN L (k + 1) →L[ℂ] L2 (TIdx (k + 1) i.castSucc (Fin.last k)) :=
  ∑ r, Vop (momUnitary L k (cls (hg r))) (wien_cls (hf r)) i

theorem hV_KT (i : Fin k) (y : L2TN L (k + 1)) (t : TIdx (k + 1) i.castSucc (Fin.last k)) :
    (freq L t.1 : ℂ) * (traceInv (ext_ne i) (KT f g hf hg y) :
        TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t =
      (VT f g hf hg i y : TIdx (k + 1) i.castSucc (Fin.last k) → ℂ) t := by
  unfold KT VT
  simp only [sum_apply, map_sum, lp.coeFn_sum, Finset.sum_apply,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => Vop_spec (wien_cls (hf r)) i y t

/-- The energy-space operator `K_H = A^{-1/2} K A^{1/2}` on `H¹(𝕋_L^{k+1})`. -/
def KH (φ : PhysH1 L (k + 1)) : PhysH1 L (k + 1) :=
  (PhysH1.unitary (L := L) (k := k + 1)).symm (KT f g hf hg (PhysH1.unitary φ))

/-- **Identification of `K_H` with the actual `J ⊗ Id`:** the `L²` function represented by `K_H φ` is
`(J ⊗ Id) φ`. -/
theorem val_KH (φ : PhysH1 L (k + 1)) :
    (KH f g hf hg φ).val = JI (Jsum f g hf hg) φ.val := by
  apply (momUnitary L (k + 1)).injective
  apply Subtype.ext; funext w
  show coeffFun (KH f g hf hg φ) w = _
  have hv : ∀ X : Fin n → PhysH1 L (k + 1), (∑ r, X r).val = ∑ r, (X r).val := fun X => by
    simpa only [PhysH1.valCLM_apply] using
      map_sum (PhysH1.valCLM (L := L) (k := k + 1)) X Finset.univ
  rw [Jsum, JI_sum, sum_apply, map_sum, lp.coeFn_sum, Finset.sum_apply]
  have h1 : coeffFun (KH f g hf hg φ) w = ∑ r, coeffFun
      ((PhysH1.unitary (L := L) (k := k + 1)).symm
        (Ktil (momUnitary L k (cls (hg r))) (wien_cls (hf r)) (PhysH1.unitary φ))) w := by
    unfold KH KT
    simp only [sum_apply, map_sum]
    unfold coeffFun
    rw [hv, map_sum, lp.coeFn_sum, Finset.sum_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [coeffFun_Ktil, momUnitary_JI, Jell_rankOne]
  have : Phi (PhysH1.unitary φ) = momUnitary L (k + 1) φ.val := by
    unfold Phi
    simp
  rw [this]

/-- `K_H^{(g,f)} = (K_H^{(f,g)})^*` for the `L²` pairing: `K_H^{(g,f)}` is the energy-space operator of
`J^* ⊗ Id = (J ⊗ Id)^*`. -/
theorem KH_adjoint (φ ψ : PhysH1 L (k + 1)) :
    ⟪φ.val, (KH f g hf hg ψ).val⟫_ℂ = ⟪(KH g f hg hf φ).val, ψ.val⟫_ℂ := by
  rw [val_KH, val_KH, JI_adjoint, adjoint_Jsum]

/-- **The external commutator clause.** For `J = Σ_r |f_r⟩⟨g_r|` and the external contact
`(i, k+1)`, `i ≤ k`: there is a compact operator `C = A^{-1/2}[B_{i,k+1}, J ⊗ Id]A^{-1/2}` on
`L²(𝕋_L^{k+1})`, determined by the commutator form
`⟨A^{-1/2}φ', C A^{-1/2}ψ'⟩ = b_{i,k+1}(φ, (J⊗Id)ψ) − b_{i,k+1}((J⊗Id)^*φ, ψ)` for `φ, ψ ∈ H¹`
(`φ' = A^{1/2}φ`), where `(J ⊗ Id)ψ` and `(J ⊗ Id)^*φ` are the actual operators of Part 7. -/
theorem external_commutator (i : Fin k) :
    ∃ C : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1), IsCompactOperator C ∧
      ∀ φ ψ : PhysH1 L (k + 1),
        ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ =
          bform (ext_ne i) φ (KH f g hf hg ψ) - bform (ext_ne i) (KH g f hg hf φ) ψ := by
  refine ⟨(Bsand (ext_ne i)).comp (KT f g hf hg) -
    (ContinuousLinearMap.adjoint (KT g f hg hf)).comp (Bsand (ext_ne i)),
    comm_isCompact (ext_ne i) (KT f g hf hg) (KT g f hg hf) (VT f g hf hg i) (VT g f hg hf i)
      (hV_KT f g hf hg i) (hV_KT g f hg hf i), fun φ ψ => ?_⟩
  have e1 : PhysH1.unitary (KH f g hf hg ψ) = KT f g hf hg (PhysH1.unitary ψ) := by
    unfold KH; simp
  have e2 : PhysH1.unitary (KH g f hg hf φ) = KT g f hg hf (PhysH1.unitary φ) := by
    unfold KH; simp
  rw [bform_eq, bform_eq, e1, e2]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← Bsand_symm (ext_ne i) (PhysH1.unitary φ) (KT f g hf hg (PhysH1.unitary ψ)),
    ← Bsand_symm (ext_ne i) (KT g f hg hf (PhysH1.unitary φ)) (PhysH1.unitary ψ)]

end ExternalCommutator


/-! ## Part 9: abstract form assembly and the internal contact -/

section InternalContact

variable {L : ℝ} [Fact (0 < L)] {m : ℕ} {i j : Fin m}

/-- **Form assembly.** For bounded `K, K'` with bounded smoothing operators `V, V'`, the operator
`C = Bsand K − K'^* Bsand` is compact and its form is
`⟨A^{1/2}φ, C A^{1/2}ψ⟩ = b(φ, K_H ψ) − b(K'_H φ, ψ)` with `K_H = A^{-1/2} K A^{1/2}` on `H¹`. -/
theorem comm_form (hij : i ≠ j) (K K' : L2TN L m →L[ℂ] L2TN L m)
    (V V' : L2TN L m →L[ℂ] L2 (TIdx m i j))
    (hV : ∀ (y : L2TN L m) (t : TIdx m i j),
      (freq L t.1 : ℂ) * (traceInv hij (K y) : TIdx m i j → ℂ) t = (V y : TIdx m i j → ℂ) t)
    (hV' : ∀ (y : L2TN L m) (t : TIdx m i j),
      (freq L t.1 : ℂ) * (traceInv hij (K' y) : TIdx m i j → ℂ) t = (V' y : TIdx m i j → ℂ) t) :
    ∃ C : L2TN L m →L[ℂ] L2TN L m, IsCompactOperator C ∧
      ∀ φ ψ : PhysH1 L m,
        ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ =
          bform hij φ ((PhysH1.unitary (L := L) (k := m)).symm (K (PhysH1.unitary ψ))) -
          bform hij ((PhysH1.unitary (L := L) (k := m)).symm (K' (PhysH1.unitary φ))) ψ := by
  refine ⟨(Bsand hij).comp K - (ContinuousLinearMap.adjoint K').comp (Bsand hij),
    comm_isCompact hij K K' V V' hV hV', fun φ ψ => ?_⟩
  rw [bform_eq, bform_eq]
  simp only [LinearIsometryEquiv.apply_symm_apply, sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  rw [← Bsand_symm hij (PhysH1.unitary φ) (K (PhysH1.unitary ψ)),
    ← Bsand_symm hij (K' (PhysH1.unitary φ)) (PhysH1.unitary ψ)]

/-- `ℓ¹ ⇒ ℓ²` for nonnegative families. -/
theorem sq_summable_of_summable {ι : Type*} {x : ι → ℝ} (h0 : ∀ a, 0 ≤ x a) (hx : Summable x) :
    Summable fun a => x a ^ 2 := by
  refine Summable.of_nonneg_of_le (fun a => sq_nonneg _) (fun a => ?_) (hx.mul_left (∑' a, x a))
  have : x a ≤ ∑' a, x a := hx.le_tsum a (fun b _ => h0 b)
  nlinarith [h0 a]

/-- For `F` of Wiener type, `D_ij T_ij F` is `ℓ¹` (hence `ℓ²`) on the collision torus. -/
theorem lam_trace_l1 {F : L2 (Mom m)} (hF : Wien L F) (hij : i ≠ j) :
    Summable fun t : TIdx m i j => ‖(freq L t.1 : ℂ) * traceCoeff L i j hij (⇑F) t‖ := by
  have hL : 0 < L := Fact.out
  set G : Mom m → ℝ := fun c => (|freq L (c i)| + |freq L (c j)|) * ‖(F : Mom m → ℂ) c‖ with hG
  have hGs : Summable G := by
    have := (hF.l1_freq i).add (hF.l1_freq j)
    refine this.congr fun c => ?_
    simp only [hG, add_mul]
  obtain ⟨hfs, -⟩ := fibre_total hij G hGs
  refine Summable.of_nonneg_of_le (fun t => norm_nonneg _) (fun t => ?_) (hfs.mul_left (Real.sqrt L)⁻¹)
  have hdom : ∀ a : ℤ, ‖(freq L t.1 : ℂ) * (F : Mom m → ℂ) (fib i j hij t a)‖ ≤
      G (fib i j hij t a) := by
    intro a
    have : (freq L t.1 : ℝ) = freq L a + freq L (t.1 - a) := (freq_add_sub t.1 a).symm
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, this]
    simp only [hG, fib_i, fib_j]
    exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (norm_nonneg _)
  have hGt : Summable fun a : ℤ => G (fib i j hij t a) := hGs.comp_injective (fib_injective i j hij t)
  have hsn : Summable fun a : ℤ => ‖(freq L t.1 : ℂ) * (F : Mom m → ℂ) (fib i j hij t a)‖ :=
    Summable.of_nonneg_of_le (fun a => norm_nonneg _) hdom hGt
  unfold traceCoeff
  rw [show (freq L t.1 : ℂ) * ((((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∑' a, (⇑F) (fib i j hij t a)) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∑' a, (freq L t.1 : ℂ) * (⇑F) (fib i j hij t a) by
    rw [tsum_mul_left]; ring, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hdom hGt)

end InternalContact


section InternalJ

variable {L : ℝ} [Fact (0 < L)] {k n : ℕ}
variable (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
  (hg : ∀ r, IsTorusTest L (g r))

theorem cls_mem_range {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    cls hφ ∈ Set.range (PhysH1.val : PhysH1 L k → L2TN L k) := by
  rw [PhysH1.range_val]
  exact (wien_cls hφ).kin

/-- A smooth profile as an element of `H¹`. -/
def clsH {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) : PhysH1 L k :=
  Classical.choose (cls_mem_range hφ)

theorem val_clsH {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) : (clsH hφ).val = cls hφ :=
  Classical.choose_spec (cls_mem_range hφ)

/-- `A^{-1/2} z`, as an `L²` function. -/
def Ainv (z : L2TN L k) : L2TN L k := ((PhysH1.unitary (L := L) (k := k)).symm z).val

theorem momUnitary_Ainv_mul (z : L2TN L k) (w : Mom k) :
    (momUnitary L k z : Mom k → ℂ) w = (kinSqrt L k w : ℂ) * (momUnitary L k (Ainv z) : Mom k → ℂ) w := by
  have h := PhysH1.unitary_coeff ((PhysH1.unitary (L := L) (k := k)).symm z) w
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h

/-- `⟨A^{-1/2} z, A^{1/2} φ⟩ = ⟨z, φ⟩` for `φ ∈ H¹`. -/
theorem inner_Ainv (z : L2TN L k) (φ : PhysH1 L k) :
    ⟪Ainv z, PhysH1.unitary φ⟫_ℂ = ⟪z, φ.val⟫_ℂ := by
  rw [← (momUnitary L k).inner_map_map, ← (momUnitary L k).inner_map_map z, inner_eq_tsum',
    inner_eq_tsum']
  refine tsum_congr fun w => ?_
  rw [PhysH1.unitary_coeff, momUnitary_Ainv_mul z w, map_mul, Complex.conj_ofReal]
  ring

/-- `K = A^{1/2} J A^{-1/2}` for `J = Σ_r |f_r⟩⟨g_r|` acting on all `k` variables. -/
def KTi : L2TN L k →L[ℂ] L2TN L k :=
  ∑ r, InnerProductSpace.rankOne ℂ (PhysH1.unitary (clsH (hf r))) (Ainv (cls (hg r)))

/-- The `ℓ²` vector `(s,ℓ) ↦ λ_s (T_ij F)(s,ℓ)` for `F` of Wiener type. -/
def wvec {F : L2 (Mom k)} (hF : Wien L F) {i j : Fin k} (hij : i ≠ j) : L2 (TIdx k i j) :=
  ⟨fun t => (freq L t.1 : ℂ) * traceCoeff L i j hij (⇑F) t,
    memL2_iff.2 (sq_summable_of_summable (fun _ => norm_nonneg _) (lam_trace_l1 hF hij))⟩

/-- `V = D_ij T_ij J A^{-1/2}` for an internal contact. -/
def VTi {i j : Fin k} (hij : i ≠ j) : L2TN L k →L[ℂ] L2 (TIdx k i j) :=
  ∑ r, InnerProductSpace.rankOne ℂ (wvec (wien_cls (hf r)) hij) (Ainv (cls (hg r)))

theorem hV_KTi {i j : Fin k} (hij : i ≠ j) (y : L2TN L k) (t : TIdx k i j) :
    (freq L t.1 : ℂ) * (traceInv hij (KTi f g hf hg y) : TIdx k i j → ℂ) t =
      (VTi f g hf hg hij y : TIdx k i j → ℂ) t := by
  unfold KTi VTi
  simp only [sum_apply, map_sum, lp.coeFn_sum, Finset.sum_apply, Finset.mul_sum,
    InnerProductSpace.rankOne_apply, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 : (traceInv hij (PhysH1.unitary (clsH (hf r))) : TIdx k i j → ℂ) t =
      traceCoeff L i j hij (⇑(momUnitary L k (cls (hf r)))) t := by
    rw [traceInv_apply, LinearIsometryEquiv.symm_apply_apply]
    show traceCoeff L i j hij (coeffFun (clsH (hf r))) t = _
    unfold coeffFun
    rw [val_clsH]
  rw [h1]
  show _ = ⟪Ainv (cls (hg r)), y⟫_ℂ * ((freq L t.1 : ℂ) * traceCoeff L i j hij
    (⇑(momUnitary L k (cls (hf r)))) t)
  ring

/-- The energy-space operator `K_H = A^{-1/2} K A^{1/2}` of the internal case. -/
def KHi (φ : PhysH1 L k) : PhysH1 L k :=
  (PhysH1.unitary (L := L) (k := k)).symm (KTi f g hf hg (PhysH1.unitary φ))

/-- **Identification of `K_H` with the actual `J`:** `val (K_H φ) = J φ`. -/
theorem val_KHi (φ : PhysH1 L k) : (KHi f g hf hg φ).val = Jsum f g hf hg φ.val := by
  have hv : ∀ X : Fin n → PhysH1 L k, (∑ r, X r).val = ∑ r, (X r).val := fun X => by
    simpa only [PhysH1.valCLM_apply] using map_sum (PhysH1.valCLM (L := L) (k := k)) X Finset.univ
  have hs : ∀ (c : ℂ) (x : PhysH1 L k), (c • x).val = c • x.val := fun c x => by
    simpa only [PhysH1.valCLM_apply] using map_smul (PhysH1.valCLM (L := L) (k := k)) c x
  unfold KHi KTi Jsum
  simp only [sum_apply, map_sum, InnerProductSpace.rankOne_apply, map_smul, hv, hs,
    LinearIsometryEquiv.symm_apply_apply, val_clsH, inner_Ainv]

theorem KHi_adjoint (φ ψ : PhysH1 L k) :
    ⟪φ.val, (KHi f g hf hg ψ).val⟫_ℂ = ⟪(KHi g f hg hf φ).val, ψ.val⟫_ℂ := by
  rw [val_KHi, val_KHi, ← adjoint_Jsum f g hf hg, ContinuousLinearMap.adjoint_inner_left]

/-- **The internal commutator clause.** For `J = Σ_r |f_r⟩⟨g_r|` on `k` variables and an internal
contact `i ≠ j` among them: `C = A_k^{-1/2}[B_ij, J]A_k^{-1/2}` is compact on `L²(𝕋_L^k)`, with
commutator form `b_ij(φ, Jψ) − b_ij(J^*φ, ψ)` on `H¹` (`J`, `J^*` the actual operators). -/
theorem internal_commutator {i j : Fin k} (hij : i ≠ j) :
    ∃ C : L2TN L k →L[ℂ] L2TN L k, IsCompactOperator C ∧
      ∀ φ ψ : PhysH1 L k,
        ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ =
          bform hij φ (KHi f g hf hg ψ) - bform hij (KHi g f hg hf φ) ψ :=
  comm_form hij (KTi f g hf hg) (KTi g f hg hf) (VTi f g hf hg hij) (VTi g f hg hf hij)
    (hV_KTi f g hf hg hij) (hV_KTi g f hg hf hij)

end InternalJ


theorem kinWeight_comp_sqrt {L : ℝ} {m : ℕ} (σ : Equiv.Perm (Fin m)) (w : Mom m) :
    kinSqrt L m (w ∘ σ) = kinSqrt L m w := by
  unfold kinSqrt; rw [kinWeight_comp]

/-! ## Part 10: bosonic restriction -/

section Bosonic

variable {L : ℝ} [Fact (0 < L)] {m : ℕ}

variable (L m) in
/-- The bosonic subspace `L²_sym(𝕋_L^m)` of permutation-invariant wave functions. -/
def SymL2 : Submodule ℂ (L2TN L m) :=
  ⨅ σ : Equiv.Perm (Fin m), LinearMap.ker (((physPerm (L := L) σ).toLinearMap) - LinearMap.id)

theorem mem_symL2_iff (x : L2TN L m) :
    x ∈ SymL2 L m ↔ ∀ σ : Equiv.Perm (Fin m), physPerm σ x = x := by
  unfold SymL2
  rw [Submodule.mem_iInf]
  refine forall_congr' fun σ => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

theorem isClosed_symL2 : IsClosed ((SymL2 L m : Submodule ℂ (L2TN L m)) : Set (L2TN L m)) := by
  have : ((SymL2 L m : Submodule ℂ (L2TN L m)) : Set (L2TN L m)) =
      ⋂ σ : Equiv.Perm (Fin m), {x : L2TN L m | physPerm σ x = x} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter]
    exact mem_symL2_iff x
  rw [this]
  exact isClosed_iInter fun σ => isClosed_eq (physPerm σ).continuous continuous_id

instance : CompleteSpace (SymL2 L m) := (isClosed_symL2 (L := L) (m := m)).completeSpace_coe

/-- **`A^{-1/2}` maps `L²_sym` onto `H¹_sym`:** `φ ∈ H¹_sym ⟺ A^{1/2}φ ∈ L²_sym`. -/
theorem unitary_mem_symL2_iff (φ : PhysH1 L m) :
    PhysH1.unitary φ ∈ SymL2 L m ↔ φ ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L m)) := by
  rw [mem_symL2_iff, PhysH1.mem_sym_iff, isSymm_iff_coeff, isSymm_iff_coeff]
  refine forall_congr' fun σ => forall_congr' fun w => ?_
  rw [PhysH1.unitary_coeff, PhysH1.unitary_coeff, kinWeight_comp_sqrt σ w]
  have hne : (kinSqrt L m w : ℂ) ≠ 0 := by
    have := one_le_kinSqrt L m w
    exact_mod_cast (by linarith : kinSqrt L m w ≠ 0)
  exact (mul_right_inj' hne)

/-- Compression of a compact operator to the bosonic subspace is compact, and its form is the
restricted form. -/
theorem compress_symL2 (C : L2TN L m →L[ℂ] L2TN L m) (hC : IsCompactOperator C) :
    IsCompactOperator ((ContinuousLinearMap.adjoint (SymL2 L m).subtypeL).comp
      (C.comp (SymL2 L m).subtypeL)) ∧
    ∀ x y : SymL2 L m,
      ⟪x, ((ContinuousLinearMap.adjoint (SymL2 L m).subtypeL).comp
        (C.comp (SymL2 L m).subtypeL)) y⟫_ℂ = ⟪(x : L2TN L m), C (y : L2TN L m)⟫_ℂ := by
  refine ⟨?_, fun x y => ?_⟩
  · have h1 : IsCompactOperator (C.comp (SymL2 L m).subtypeL) := hC.comp_clm (SymL2 L m).subtypeL
    exact h1.clm_comp (ContinuousLinearMap.adjoint (SymL2 L m).subtypeL)
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rfl

end Bosonic


/-! ## Part 11: ENERGY-002 `lem:A1-trace`, assembled -/

section Final

variable {L : ℝ} [Fact (0 < L)]

/-- Compression `P C P` of an operator to the bosonic subspace `L²_sym`
(`P` the orthogonal projection onto `L²_sym`, `ι` its inclusion). -/
def compressSym {m : ℕ} (C : L2TN L m →L[ℂ] L2TN L m) : SymL2 L m →L[ℂ] SymL2 L m :=
  (ContinuousLinearMap.adjoint (SymL2 L m).subtypeL).comp (C.comp (SymL2 L m).subtypeL)

/-- Bosonic restriction of a commutator form `c` represented by `C` on `L²`: the compression of `C`
is compact, and on `x, y ∈ L²_sym` its form is `c(A^{-1/2}x, A^{-1/2}y)` with `A^{-1/2}x ∈ H¹_sym`. -/
def CompressClause {m : ℕ} (C : L2TN L m →L[ℂ] L2TN L m) (c : PhysH1 L m → PhysH1 L m → ℂ) : Prop :=
  IsCompactOperator (compressSym C) ∧
    ∀ x y : SymL2 L m,
      (PhysH1.unitary (L := L) (k := m)).symm (x : L2TN L m) ∈
          (PhysH1.sym : Submodule ℂ (PhysH1 L m)) ∧
        ⟪x, compressSym C y⟫_ℂ =
          c ((PhysH1.unitary (L := L) (k := m)).symm (x : L2TN L m))
            ((PhysH1.unitary (L := L) (k := m)).symm (y : L2TN L m))

theorem compressClause_of_form {m : ℕ} (C : L2TN L m →L[ℂ] L2TN L m) (hC : IsCompactOperator C)
    (c : PhysH1 L m → PhysH1 L m → ℂ)
    (hc : ∀ φ ψ : PhysH1 L m, ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ = c φ ψ) :
    CompressClause C c := by
  obtain ⟨h1, h2⟩ := compress_symL2 C hC
  refine ⟨h1, fun x y => ⟨?_, ?_⟩⟩
  · rw [← unitary_mem_symL2_iff, LinearIsometryEquiv.apply_symm_apply]
    exact x.2
  · have := hc ((PhysH1.unitary (L := L) (k := m)).symm (x : L2TN L m))
      ((PhysH1.unitary (L := L) (k := m)).symm (y : L2TN L m))
    rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply] at this
    rw [← this]
    exact h2 x y

/-- ENERGY-002, first paragraph, for one contact `(i, j)`, `i ≠ j`, on `m ≥ 2` variables:
(a) `T_ij : H¹ → H^{1/2}` bounded (and it is the actual restriction to `x_i = x_j`);
(b) `T_ij A_m^{-1/2}` compact;
(c) `B_ij = T_ij^* D_ij T_ij` bounded `H¹ → H^{-1}` (form `b_ij(f,g) = ⟨T_ij f, D_ij T_ij g⟩`), and
`A_m^{-1/2} T_ij^* T_ij A_m^{-1/2}` compact. -/
def TraceClause (L : ℝ) [Fact (0 < L)] (m : ℕ) (i j : Fin m) (hij : i ≠ j) : Prop :=
  ((∃ T : PhysH1 L m →L[ℂ] Hhalf i j L, ‖T‖ ≤ Real.sqrt (CL L / L) ∧
      ∀ x : PhysH1 L m, (T x).val = (collisionProductUnitary (L := L) i j).symm (productTrace i j hij x)) ∧
    ∀ (φ : (Fin m → ℝ) → ℂ) (hφ : IsTorusTest L φ),
      (productTrace (L := L) i j hij (smoothH1 hφ) :
          (AddCircle L × (Rest m i j → AddCircle L)) → ℂ) =ᵐ[dyij (L := L) i j]
        (fun p => liftK (L := L) φ (diagPoint i j p.1 p.2))) ∧
  (IsCompactOperator (traceInv (L := L) hij) ∧ IsCompactOperator (Sop (L := L) hij)) ∧
  ((∀ f g : PhysH1 L m, ‖bform hij f g‖ ≤ (CL L / L) * ‖f‖ * ‖g‖) ∧
    (∀ f g : PhysH1 L m, conj (bform hij f g) = bform hij g f) ∧
    (∀ f g : PhysH1 L m, bform hij f g = ⟪Bsand hij (PhysH1.unitary f), PhysH1.unitary g⟫_ℂ) ∧
    IsCompactOperator (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L Sop hij) ∧
    ∀ x y : L2TN L m, ⟪x, (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L Sop hij) y⟫_ℂ =
      ⟪traceCLM i j hij ((PhysH1.unitary (L := L) (k := m)).symm x),
        traceCLM i j hij ((PhysH1.unitary (L := L) (k := m)).symm y)⟫_ℂ)

/-- The same statements after bosonic restriction: `A^{-1/2}` identifies `L²_sym` with `H¹_sym`;
`T_ij` is bounded on `H¹_sym`; `T_ij A^{-1/2}` and the sandwich are compact on `L²_sym`. -/
def TraceClauseSym (L : ℝ) [Fact (0 < L)] (m : ℕ) (i j : Fin m) (hij : i ≠ j) : Prop :=
  (∀ φ : PhysH1 L m, PhysH1.unitary φ ∈ SymL2 L m ↔ φ ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L m))) ∧
  ‖(traceHalf (L := L) hij).comp (PhysH1.sym : Submodule ℂ (PhysH1 L m)).subtypeL‖ ≤
      Real.sqrt (CL L / L) ∧
  IsCompactOperator ((traceInv (L := L) hij).comp (SymL2 L m).subtypeL) ∧
  (∀ f g : PhysH1 L m, f ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L m)) →
      g ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L m)) → ‖bform hij f g‖ ≤ (CL L / L) * ‖f‖ * ‖g‖) ∧
  IsCompactOperator (compressSym (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L Sop hij))

theorem traceClause (m : ℕ) (i j : Fin m) (hij : i ≠ j) : TraceClause L m i j hij :=
  ⟨⟨⟨traceHalf hij, norm_traceHalf_le hij, productTrace_half hij⟩,
    fun φ hφ => productTrace_smooth i j hij hφ⟩,
   ⟨traceInv_isCompact hij, Sop_isCompact hij⟩,
   ⟨bform_bound hij, bform_conj hij, bform_eq hij, sandwich_isCompact hij, sandwich_inner hij⟩⟩

set_option maxRecDepth 8000 in
theorem traceClauseSym (m : ℕ) (i j : Fin m) (hij : i ≠ j) : TraceClauseSym L m i j hij := by
  refine ⟨unitary_mem_symL2_iff, ?_, ?_, fun f g _ _ => bform_bound hij f g, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    calc ‖(traceHalf hij).comp (PhysH1.sym : Submodule ℂ (PhysH1 L m)).subtypeL x‖
        ≤ ‖traceHalf (L := L) hij‖ * ‖(x : PhysH1 L m)‖ := (traceHalf hij).le_opNorm _
      _ ≤ Real.sqrt (CL L / L) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (norm_traceHalf_le hij) (norm_nonneg _)
  · exact IsCompactOperator.comp_clm (traceInv_isCompact (L := L) hij) (SymL2 L m).subtypeL
  · have h := (compress_symL2 (ContinuousLinearMap.adjoint (Sop (L := L) hij) ∘L Sop hij)
      (sandwich_isCompact hij)).1
    unfold compressSym
    exact h

/-- **ENERGY-002, external contact, commutator clause** (with bosonic restriction): for
`J = Σ_r |f_r⟩⟨g_r|` (finite rank, smooth kernel) on `k` variables and the external contact
`(i, k+1)`, `i ≤ k`.  `J ⊗ Id` is the operator `JI J` of Part 7 (matrix elements on elementary tensors
`⟨a⊗u, (J⊗Id)(a'⊗u')⟩ = ⟨a, Ja'⟩⟨u,u'⟩`; unique with them; adjoint `J^*⊗Id`); `K_H`, `K_H^*` are the
energy-space operators of `J⊗Id` and `(J⊗Id)^* = J^*⊗Id`; and
`A^{-1/2}[B_{i,k+1}, J⊗Id]A^{-1/2}` is the compact operator `C` with commutator form
`b(φ, (J⊗Id)ψ) − b((J⊗Id)^*φ, ψ)` on `H¹`, also after bosonic restriction. -/
def ExtCommClause (L : ℝ) [Fact (0 < L)] {k n : ℕ} (f g : Fin n → (Fin k → ℝ) → ℂ)
    (hf : ∀ r, IsTorusTest L (f r)) (hg : ∀ r, IsTorusTest L (g r)) (i : Fin k) : Prop :=
  ((∀ (a a' : Fin k → L2T L) (u u' : L2T L),
      ⟪elem a u, JI (Jsum f g hf hg) (elem a' u')⟫_ℂ =
        ⟪prodLp a, Jsum f g hf hg (prodLp a')⟫_ℂ * ⟪u, u'⟫_ℂ) ∧
    (∀ T : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1),
      (∀ (a a' : Fin k → L2T L) (u u' : L2T L),
        ⟪elem a u, T (elem a' u')⟫_ℂ = ⟪prodLp a, Jsum f g hf hg (prodLp a')⟫_ℂ * ⟪u, u'⟫_ℂ) →
      T = JI (Jsum f g hf hg)) ∧
    (∀ x y : L2TN L (k + 1), ⟪x, JI (Jsum f g hf hg) y⟫_ℂ =
      ⟪JI (ContinuousLinearMap.adjoint (Jsum f g hf hg)) x, y⟫_ℂ)) ∧
  (∀ φ : PhysH1 L (k + 1), (KH f g hf hg φ).val = JI (Jsum f g hf hg) φ.val) ∧
  (∀ φ : PhysH1 L (k + 1),
    (KH g f hg hf φ).val = JI (ContinuousLinearMap.adjoint (Jsum f g hf hg)) φ.val) ∧
  ∃ C : L2TN L (k + 1) →L[ℂ] L2TN L (k + 1), IsCompactOperator C ∧
    (∀ φ ψ : PhysH1 L (k + 1),
      ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ =
        bform (ext_ne i) φ (KH f g hf hg ψ) - bform (ext_ne i) (KH g f hg hf φ) ψ) ∧
    CompressClause C (fun φ ψ => bform (ext_ne i) φ (KH f g hf hg ψ) -
      bform (ext_ne i) (KH g f hg hf φ) ψ)

theorem extCommClause {k n : ℕ} (f g : Fin n → (Fin k → ℝ) → ℂ)
    (hf : ∀ r, IsTorusTest L (f r)) (hg : ∀ r, IsTorusTest L (g r)) (i : Fin k) :
    ExtCommClause L f g hf hg i := by
  refine ⟨⟨JI_matrix _, JI_unique _, JI_adjoint _⟩, val_KH f g hf hg, ?_, ?_⟩
  · intro φ
    rw [adjoint_Jsum f g hf hg]
    exact val_KH g f hg hf φ
  · obtain ⟨C, hC, hform⟩ := external_commutator f g hf hg i
    exact ⟨C, hC, hform, compressClause_of_form C hC _ hform⟩

/-- **ENERGY-002, internal contact, commutator clause** (with bosonic restriction), for
`J = Σ_r |f_r⟩⟨g_r|` on `k` variables and an internal contact `i ≠ j` among them. -/
def IntCommClause (L : ℝ) [Fact (0 < L)] {k n : ℕ} (f g : Fin n → (Fin k → ℝ) → ℂ)
    (hf : ∀ r, IsTorusTest L (f r)) (hg : ∀ r, IsTorusTest L (g r)) {i j : Fin k} (hij : i ≠ j) : Prop :=
  (∀ φ : PhysH1 L k, (KHi f g hf hg φ).val = Jsum f g hf hg φ.val) ∧
  (∀ φ : PhysH1 L k, (KHi g f hg hf φ).val = ContinuousLinearMap.adjoint (Jsum f g hf hg) φ.val) ∧
  ∃ C : L2TN L k →L[ℂ] L2TN L k, IsCompactOperator C ∧
    (∀ φ ψ : PhysH1 L k,
      ⟪PhysH1.unitary φ, C (PhysH1.unitary ψ)⟫_ℂ =
        bform hij φ (KHi f g hf hg ψ) - bform hij (KHi g f hg hf φ) ψ) ∧
    CompressClause C (fun φ ψ => bform hij φ (KHi f g hf hg ψ) - bform hij (KHi g f hg hf φ) ψ)

theorem intCommClause {k n : ℕ} (f g : Fin n → (Fin k → ℝ) → ℂ)
    (hf : ∀ r, IsTorusTest L (f r)) (hg : ∀ r, IsTorusTest L (g r)) {i j : Fin k} (hij : i ≠ j) :
    IntCommClause L f g hf hg hij := by
  refine ⟨val_KHi f g hf hg, ?_, ?_⟩
  · intro φ
    rw [adjoint_Jsum f g hf hg]
    exact val_KHi g f hg hf φ
  · obtain ⟨C, hC, hform⟩ := internal_commutator f g hf hg hij
    exact ⟨C, hC, hform, compressClause_of_form C hC _ hform⟩

/-- **ENERGY-002 (`lem:A1-trace`, `cubic_charge.tex:74`).**  For every `L > 0`:
* for each `m ≥ 2` and each pair `i ≠ j`: (a) `T_ij : H¹(𝕋_L^m) → H^{1/2}(𝕋_L^{m-1})` is bounded
  (the actual restriction), (b) `T_ij A_m^{-1/2}` is compact, (c) `B_ij` is bounded `H¹ → H^{-1}` and
  `A_m^{-1/2} T_ij^* T_ij A_m^{-1/2}` is compact — and the same after bosonic restriction;
* for every finite-rank smooth-kernel `J` on `k` variables: the commutator form
  `A_{k+1}^{-1/2}[B_{i,k+1}, J⊗Id]A_{k+1}^{-1/2}` (external contact `i ≤ k`) and the analogous internal
  one are compact, also after bosonic restriction. -/
theorem energy002 (L : ℝ) [Fact (0 < L)] :
    (∀ m : ℕ, 2 ≤ m → ∀ (i j : Fin m) (hij : i ≠ j),
        TraceClause L m i j hij ∧ TraceClauseSym L m i j hij) ∧
    (∀ (k n : ℕ) (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
        (hg : ∀ r, IsTorusTest L (g r)) (i : Fin k), ExtCommClause L f g hf hg i) ∧
    (∀ (k n : ℕ) (f g : Fin n → (Fin k → ℝ) → ℂ) (hf : ∀ r, IsTorusTest L (f r))
        (hg : ∀ r, IsTorusTest L (g r)) (i j : Fin k) (hij : i ≠ j), IntCommClause L f g hf hg hij) :=
  ⟨fun m _ i j hij => ⟨traceClause m i j hij, traceClauseSym m i j hij⟩,
   fun k n f g hf hg i => extCommClause f g hf hg i,
   fun k n f g hf hg i j hij => intCommClause f g hf hg hij⟩

end Final

/-! Kernel axiom audit. -/
#print axioms wien_cls
#print axioms JI_matrix
#print axioms JI_unique
#print axioms JI_adjoint
#print axioms val_KH
#print axioms KH_adjoint
#print axioms external_commutator
#print axioms val_KHi
#print axioms internal_commutator
#print axioms unitary_mem_symL2_iff
#print axioms compress_symL2
#print axioms traceClause
#print axioms traceClauseSym
#print axioms extCommClause
#print axioms intCommClause
#print axioms energy002

end QuantumNLS.EnergyContactCommutator
