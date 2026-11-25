import Mathlib
import QuantumNLS.BalancedWickDefinition
import QuantumNLS.MixedCommutator

/-!
# DEF-032 repair: the Wick quantization of a balanced homogeneous polynomial equals the placement of its auxiliary kernel

Source: `DEFINITIONS_LEDGER.md` DEF-032 (`def:report-32`, `definitions.tex:193`).  Ledger convention: "For an auxiliary
homogeneous kernel of bidegree `(p,p)`, this [the Wick operator `𝒲_N^q(f) = J_N^*∑ f_{αβ}N^{-|α|}(b^*)^β b^α J_N`] equals
the pullback of `(N)_p N^{-p}` times its normalized placement on the auxiliary label sector.  It is not the placement of that
kernel on the physical particle space."  Terra r128 held `BalancedWickDefinition` (BWD1, imported read-only, unchanged)
because `kernelQuantization` was defined for an arbitrary kernel but never related to the polynomial.  This module supplies that
relation and the equality.

## The polynomial-kernel relation (`kernelOf`, `Kmono`, `wordKernel`)
For a monomial `z^α \bar z^β` of bidegree `(p,p)` (`α, β` of total `p`) let `v_α, v_β : Fin p → ℤ` be words of occupations `α, β`
(`representative`), and `A_{αβ} = P_p |e_{v_β}⟩⟨e_{v_α}| P_p` on `Sym^p ℓ²(ℤ)` (`wordKernel`; it equals
`√(α!β!)/p! |β⟩⟨α|` in the occupation basis).  For `f = ∑ f_{αβ} z^α \bar z^β` put `A_f = ∑ f_{αβ} A_{αβ}` (`kernelOf p f`).
`kernelOf_symbol` proves the relation is the intended one: the product symbol `⟨u^{⊗p}, A_f u^{⊗p}⟩` is the literal evaluation
`f(u) = ∑ f_{αβ} u^α \bar u^β` (`BalancedWickDefinition.evaluate`).

## Proved (all standard axioms)
* `auxiliaryWick_zm_eq`: for `α, β ∈ 𝓜_p`, `p ≥ 1`, `N = p+q`:
  `W_N(z^α \bar z^β) = U4 ∘ ((N)_p N^{-p} 𝒰_{N,p}(A_{αβ})) ∘ U4⁻¹` on `ℓ²(𝓜_N)` (realized DEF-009 `U_N_r`, realized BWD1
  `auxiliaryWick`).  Proof: the matrix elements of the placement on the occupation basis are computed from the word
  coefficients `⟨e_w, |m⟩⟩ = √(m!/N!)[occ w = m]` (`inner_productVector_basisVector`) and the contraction identity
  `pinner_basisVector` (`(⟨e_v|⊗1)|m⟩_N = √(m_{(v)}·q!/N!)|m-α⟩_q`, via the partial inner product `pinner = (y ↦ φ⊗y)†`, the
  off-diagonal trace identity `inner_U_eq_inner_htmap'` and `inner_htmap_rankOne`), `inner_U_word`; the Fock side is the
  ladder formulas `AnnMono_ket`, `CreMono_ket` (`b^α|m⟩ = √(m!/(m-α)!)|m-α⟩`, `(b^*)^β|n⟩ = √((n+β)!/n!)|n+β⟩`,
  `mdesc` = falling-factorial product).  The two agree since `(N)_p · q!/N! = 1` (`fall_mul`).
* `auxiliaryWick_eq_kernel`: the same for a balanced homogeneous polynomial `f` of bidegree `(p,p)`:
  `W_N(f) = U4 ∘ ((N)_p N^{-p} 𝒰_{N,p}(A_f)) ∘ U4⁻¹` (linearity: `aux_core_sum`, `UlinL`).
* `wick_eq_kernelQuantization`: **the ledger equality**: `wick b g f = kernelQuantization b g hp (kernelOf p f.symbol)`
  (the pullback by the gauged `J_N` of `(N)_p N^{-p}` times the normalized placement on the auxiliary label sector), for every
  basis `b`, gauge `g`, and balanced finite polynomial `f` of bidegree `(p,p)`, `p ≥ 1`.

## Not asserted
* the first product correction (`C1`, Poisson bracket) and any `thm:full-wick` consequence;
* `p = 0` (the constant monomial gives the identity, already `BalancedWickDefinition.quantization_constant`) and
  `p > N` (zero, `BalancedWickDefinition.quantization_above_sector`);
* mixed bidegree polynomials (the convention is stated for a homogeneous kernel of bidegree `(p,p)`; a general balanced `f` is
  the sum of its homogeneous parts and each part is covered).
* No hypothesis on the basis beyond `b : BetheBasis L (p+q)`: no EXT-001 premise enters.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped InnerProductSpace ComplexConjugate
open QuantumNLS.TensorCarrier

noncomputable section

namespace QuantumNLS.WickKernelBridge

open QuantumNLS.OccupationUnitary
open QuantumNLS.Occupation (Occ Arr e total IsArray)

/-! ### Words, occupations and the coefficients of the occupation basis vectors -/

section Words

theorem occupation_append {p q : ℕ} (v : Word p) (r : Word q) :
    occupation (Fin.append v r) = occupation v + occupation r := by
  classical
  ext a
  simp only [Finsupp.add_apply, occupation_apply, Fintype.card_subtype, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem productVector_append {p q : ℕ} (v : Word p) (r : Word q) :
    splitIsometry (𝕜 := ℂ) p q (productVector (Fin.append v r)) =
      htmul (productVector v) (productVector r) := by
  have h : (fun i => oneBasis ((Fin.append v r) i)) =
      Fin.append (fun i => oneBasis (v i)) (fun j => oneBasis (r j)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  simp only [productVector, tensorMultilinear_apply]
  rw [h]
  exact splitIsometry_ptprod_append _ _

/-- `m!` (product of multiplicity factorials) as a real number. -/
def mfr (m : Occ) : ℝ := (multiplicityFactorial m : ℝ)

theorem mfr_pos (m : Occ) : 0 < mfr m := by
  unfold mfr; exact_mod_cast multiplicityFactorial_pos m

/-- **Word coefficients of an occupation basis vector**: `⟨e_w, |m⟩⟩ = √(m!/N!)·[occ w = m]`. -/
theorem inner_productVector_basisVector {N : ℕ} (w : Word N) (m : Arr N) :
    ⟪productVector w, (basisVector m : Tensor N)⟫_ℂ =
      if occupation w = m.1 then ((Real.sqrt (mfr m.1 / (N.factorial : ℝ)) : ℝ) : ℂ) else 0 := by
  have hb : (basisVector m : Tensor N) = occupationVector m := rfl
  rw [hb, occupationVector, inner_smul_right]
  by_cases h : occupation w = m.1
  · rw [if_pos h]
    have h1 : symProduct w = symProduct (representative m) :=
      symProduct_eq_of_occupation (by rw [occupation_representative]; exact h)
    have h2 := inner_productVector_symProduct_self w
    rw [← h1, h2, h]
    have hN : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    have hm : mfr m.1 ≠ 0 := (mfr_pos _).ne'
    unfold normalization
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_mul]
    congr 1
    unfold mfr
    have hy : (0 : ℝ) < (N.factorial : ℝ) / (multiplicityFactorial m.1 : ℝ) := by
      have := mfr_pos m.1; unfold mfr at this; positivity
    have e1 : (multiplicityFactorial m.1 : ℝ) / (N.factorial : ℝ) =
        ((N.factorial : ℝ) / (multiplicityFactorial m.1 : ℝ))⁻¹ := (inv_div _ _).symm
    rw [e1, Real.sqrt_inv]
    generalize (N.factorial : ℝ) / (multiplicityFactorial m.1 : ℝ) = y at hy ⊢
    have hs := Real.sqrt_pos.2 hy
    have hss := Real.mul_self_sqrt hy.le
    field_simp
    linarith
  · rw [if_neg h, inner_productVector_symProduct_of_ne (by rwa [occupation_representative]), mul_zero]

end Words

/-! ### The partial inner product `⟨φ|⊗1` and rank-one placements -/

section Pinner

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- `y ↦ φ ⊗ y`. -/
def tmulLeft (φ : X) : Y →L[ℂ] HilbertTensor ℂ X Y :=
  LinearMap.mkContinuous
    { toFun := fun y => htmul φ y
      map_add' := fun y y' => htmul_add_right φ y y'
      map_smul' := fun c y => htmul_smul_right c φ y }
    ‖φ‖ (fun y => (norm_htmul φ y).le)

theorem tmulLeft_apply (φ : X) (y : Y) : tmulLeft φ y = htmul φ y := rfl

/-- The partial inner product `⟨φ|⊗1 : X ⊗̂ Y → Y`, the adjoint of `y ↦ φ ⊗ y`. -/
def pinner (φ : X) : HilbertTensor ℂ X Y →L[ℂ] Y := ContinuousLinearMap.adjoint (tmulLeft φ)

theorem inner_pinner (φ : X) (y : Y) (Ψ : HilbertTensor ℂ X Y) :
    ⟪y, pinner φ Ψ⟫_ℂ = ⟪htmul φ y, Ψ⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right (tmulLeft φ) y Ψ

theorem pinner_htmul (φ x : X) (y : Y) : pinner φ (htmul x y) = ⟪φ, x⟫_ℂ • y := by
  apply ext_inner_left ℂ
  intro z
  rw [inner_pinner, inner_htmul, inner_smul_right, mul_comm]

theorem ext_htmul {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (T T' : HilbertTensor ℂ X Y →L[ℂ] Z) (h : ∀ x y, T (htmul x y) = T' (htmul x y)) : T = T' := by
  have hle : Submodule.span ℂ (Set.range fun p : X × Y => (htmul p.1 p.2 : HilbertTensor ℂ X Y)) ≤
      LinearMap.ker ((T - T' : HilbertTensor ℂ X Y →L[ℂ] Z) : HilbertTensor ℂ X Y →ₗ[ℂ] Z) := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨x, y⟩, rfl⟩
    simp [h x y]
  have hcl := Submodule.topologicalClosure_minimal _ hle
    (ContinuousLinearMap.isClosed_ker (T - T'))
  rw [span_htmul_dense] at hcl
  ext z
  have hz : z ∈ LinearMap.ker ((T - T' : HilbertTensor ℂ X Y →L[ℂ] Z) :
      HilbertTensor ℂ X Y →ₗ[ℂ] Z) := hcl (Submodule.mem_top)
  have := LinearMap.mem_ker.1 hz
  simpa [sub_eq_zero] using this

theorem htmap_rankOne (β α : X) :
    htmap (InnerProductSpace.rankOne ℂ β α) (ContinuousLinearMap.id ℂ Y) =
      (tmulLeft β).comp (pinner α) := by
  apply ext_htmul
  intro x y
  rw [htmap_htmul, ContinuousLinearMap.comp_apply, pinner_htmul, InnerProductSpace.rankOne_apply,
    tmulLeft_apply, htmul_smul_left, htmul_smul_right]
  simp

theorem inner_htmap_rankOne (β α : X) (Ψ' Ψ : HilbertTensor ℂ X Y) :
    ⟪Ψ', htmap (InnerProductSpace.rankOne ℂ β α) (ContinuousLinearMap.id ℂ Y) Ψ⟫_ℂ =
      ⟪pinner β Ψ', pinner α Ψ⟫_ℂ := by
  rw [htmap_rankOne, ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_left (tmulLeft β) (pinner α Ψ) Ψ').symm

end Pinner

/-! ### The off-diagonal trace identity for the placement `𝒰_{k+m,k}` -/

section OffDiagonal

open QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition QuantumNLS.MixedTraceNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem inner_htmap_symmetrize' (k m : ℕ) (S : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k)
    (ψ' ψ : SymSector ℂ E (k + m)) :
    ⟪splitIsometry k m (ψ' : HilbertTensorPower ℂ E (k + m)),
        htmap (extendSymKernel (symKernel S))
          (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)))⟫_ℂ =
      ⟪splitIsometry k m (ψ' : HilbertTensorPower ℂ E (k + m)),
        htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)))⟫_ℂ := by
  set Ψ := splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)) with hΨ
  set Ψ' := splitIsometry k m (ψ' : HilbertTensorPower ℂ E (k + m)) with hΨ'
  set I := ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m) with hI
  set Hπ := htmap (symProj ℂ E k) I with hHπ
  have hfix : Hπ Ψ = Ψ := htmap_symProj_split k m ψ
  have hfix' : Hπ Ψ' = Ψ' := htmap_symProj_split k m ψ'
  have hcomp : htmap (extendSymKernel (symKernel S)) I = Hπ ∘L (htmap S I ∘L Hπ) := by
    rw [extendSymKernel_symKernel]
    have h1 := htmap_comp (symProj ℂ E k) (S ∘L symProj ℂ E k) I I
    have h2 := htmap_comp S (symProj ℂ E k) I I
    simp only [hI, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] at h1 h2 ⊢
    rw [h1, h2]
  rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hadj : ∀ x, ⟪Ψ', Hπ x⟫_ℂ = ⟪Hπ Ψ', x⟫_ℂ := by
    intro x
    have h := ContinuousLinearMap.adjoint_inner_left Hπ x Ψ'
    rw [hHπ, htmap_symProj_adjoint] at h
    exact h.symm
  rw [hadj, hfix', hfix]

/-- Off-diagonal form of `MixedTraceNorm.inner_U_eq_inner_htmap`. -/
theorem inner_U_eq_inner_htmap' (k m : ℕ) (ψ' ψ : SymSector ℂ E (k + m))
    (S : HilbertTensorPower ℂ E k →L[ℂ] HilbertTensorPower ℂ E k) :
    ⟪ψ', U_N_r (r := k) (q := m) (symKernel S) ψ⟫_ℂ =
      ⟪splitIsometry k m (ψ' : HilbertTensorPower ℂ E (k + m)),
        htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ E m))
          (splitIsometry k m (ψ : HilbertTensorPower ℂ E (k + m)))⟫_ℂ := by
  rw [← inner_htmap_symmetrize' k m S ψ' ψ]
  set A := symKernel S with hA
  have hfix : symProj ℂ E (k + m) (ψ' : HilbertTensorPower ℂ E (k + m)) = ψ' :=
    groupAverage_apply_of_mem _ ψ'.property
  have hfixψ : symProj ℂ E (k + m) (ψ : HilbertTensorPower ℂ E (k + m)) = ψ :=
    groupAverage_apply_of_mem _ ψ.property
  have hadj : ∀ x : HilbertTensorPower ℂ E (k + m),
      ⟪(ψ' : HilbertTensorPower ℂ E (k + m)), symProj ℂ E (k + m) x⟫_ℂ =
        ⟪symProj ℂ E (k + m) (ψ' : HilbertTensorPower ℂ E (k + m)), x⟫_ℂ := by
    intro x
    have h := ContinuousLinearMap.adjoint_inner_left (symProj ℂ E (k + m)) x
      (ψ' : HilbertTensorPower ℂ E (k + m))
    rw [symProj_adjoint] at h
    exact h.symm
  have h0 : ⟪ψ', U_N_r (r := k) (q := m) A ψ⟫_ℂ =
      ⟪(ψ' : HilbertTensorPower ℂ E (k + m)),
        sandwichPlacement (r := k) (q := m) A (ψ : HilbertTensorPower ℂ E (k + m))⟫_ℂ := rfl
  rw [h0]
  unfold sandwichPlacement
  simp only [ContinuousLinearMap.comp_apply]
  rw [hfixψ, hadj, hfix]
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply]
  set e := splitIsometry k m (E := E) (𝕜 := ℂ) with he
  show ⟪(ψ' : HilbertTensorPower ℂ E (k + m)), e.symm (htmap (extendSymKernel A)
    (ContinuousLinearMap.id ℂ _) (e (ψ : HilbertTensorPower ℂ E (k + m))))⟫_ℂ = _
  rw [← e.inner_map_map, e.apply_symm_apply]

end OffDiagonal

/-! ### The contraction of an occupation vector with a word (`BR`) -/

section Contraction

open QuantumNLS.Occupation (mdesc)

theorem mult_split (m α : Occ) (h : α ≤ m) :
    multiplicityFactorial m = mdesc m α * multiplicityFactorial (m - α) := by
  classical
  unfold multiplicityFactorial mdesc
  have hα : α.support ⊆ m.support := Finsupp.support_mono h
  rw [Finsupp.prod_of_support_subset α hα (fun b k => (m b).descFactorial k)
      (fun _ _ => Nat.descFactorial_zero _),
    Finsupp.prod_of_support_subset (m - α) (Finsupp.support_tsub) (fun _ k => k.factorial)
      (fun _ _ => Nat.factorial_zero)]
  rw [Finsupp.prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  have hb : α b ≤ m b := h b
  rw [Finsupp.tsub_apply, mul_comm]
  exact (Nat.factorial_mul_descFactorial hb).symm

theorem mdesc_eq_zero_of_not_le {m α : Occ} (h : ¬ α ≤ m) : mdesc m α = 0 := by
  unfold mdesc
  obtain ⟨b, hb⟩ : ∃ b, ¬ α b ≤ m b := by
    by_contra hcon; push_neg at hcon; exact h hcon
  have hmem : b ∈ α.support := by
    rw [Finsupp.mem_support_iff]; intro h0; apply hb; rw [h0]; exact Nat.zero_le _
  exact Finset.prod_eq_zero hmem (Nat.descFactorial_eq_zero_iff_lt.2 (not_le.1 hb))

/-- The array `m - α` of total `q` when `α ≤ m` has total `p`, `m` total `p+q`. -/
def subArr {p q : ℕ} (m : Arr (p + q)) (α : Occ) (hα : total α = p) (h : α ≤ m.1) : Arr q :=
  ⟨m.1 - α, by
    have hm : total m.1 = p + q := m.2
    show total (m.1 - α) = q
    unfold total at hm hα ⊢
    have h2 := congrArg Finsupp.degree (tsub_add_cancel_of_le h)
    rw [map_add] at h2
    omega⟩

theorem ext_words {q : ℕ} (x y : Tensor q)
    (h : ∀ r : Word q, ⟪productVector r, x⟫_ℂ = ⟪productVector r, y⟫_ℂ) : x = y := by
  apply (productBasis q).repr.injective
  ext r
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, productBasis_apply]
  exact h r

theorem pinner_basisVector {p q : ℕ} (v : Word p) (m : Arr (p + q)) (h : occupation v ≤ m.1) :
    pinner (productVector v) (splitIsometry (𝕜 := ℂ) p q (basisVector m : Tensor (p + q))) =
      ((Real.sqrt ((mdesc m.1 (occupation v) : ℝ) * (q.factorial : ℝ) / ((p + q).factorial : ℝ)) : ℝ) : ℂ) •
        (basisVector (subArr m (occupation v) (occupation_total v) h) : Tensor q) := by
  apply ext_words
  intro r
  rw [inner_pinner, ← productVector_append, LinearIsometryEquiv.inner_map_map,
    inner_productVector_basisVector, inner_smul_right, inner_productVector_basisVector,
    occupation_append]
  have hsplit := mult_split m.1 (occupation v) h
  have hs : (subArr m (occupation v) (occupation_total v) h).1 = m.1 - occupation v := rfl
  rw [hs]
  have hiff : occupation v + occupation r = m.1 ↔ occupation r = m.1 - occupation v := by
    rw [eq_tsub_iff_add_eq_of_le h, add_comm]
  by_cases hr : occupation r = m.1 - occupation v
  · rw [if_pos (hiff.2 hr), if_pos hr]
    rw [← Complex.ofReal_mul]
    congr 1
    show Real.sqrt (mfr m.1 / ((p + q).factorial : ℝ)) =
      Real.sqrt ((mdesc m.1 (occupation v) : ℝ) * (q.factorial : ℝ) / ((p + q).factorial : ℝ)) *
        Real.sqrt (mfr (m.1 - occupation v) / (q.factorial : ℝ))
    have hq : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
    have hmf : mfr m.1 = (mdesc m.1 (occupation v) : ℝ) * mfr (m.1 - occupation v) := by
      unfold mfr; rw [hsplit]; push_cast; ring
    rw [← Real.sqrt_mul (by positivity), hmf]
    congr 1
    field_simp
  · rw [if_neg (fun hh => hr (hiff.1 hh)), if_neg hr]
    simp

theorem pinner_basisVector_of_not_le {p q : ℕ} (v : Word p) (m : Arr (p + q))
    (h : ¬ occupation v ≤ m.1) :
    pinner (productVector v) (splitIsometry (𝕜 := ℂ) p q (basisVector m : Tensor (p + q))) = 0 := by
  have h0 : ∀ r : Word q, ⟪productVector r, (0 : Tensor q)⟫_ℂ = 0 := fun r => inner_zero_right _
  apply ext_words
  intro r
  rw [inner_pinner, ← productVector_append, LinearIsometryEquiv.inner_map_map,
    inner_productVector_basisVector, occupation_append, h0, if_neg]
  intro hh
  exact h (by rw [← hh]; exact le_self_add)

end Contraction

/-! ### Matrix elements of the placement of a word kernel -/

section MatrixElement

open QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition QuantumNLS.MixedTraceNorm
open QuantumNLS.Occupation (mdesc)

/-- The word kernel `|e_{v_β}⟩⟨e_{v_α}|` on `E^{⊗̂p}`, symmetrized to a kernel on `Sym^p`. -/
def wordKernel {p : ℕ} (vβ vα : Word p) : BoundedSymmetricKernel OneParticle p :=
  symKernel (InnerProductSpace.rankOne ℂ (productVector vβ) (productVector vα))

theorem inner_basisVector_basisVector {n : ℕ} (a b : Arr n) :
    ⟪(basisVector a : Tensor n), (basisVector b : Tensor n)⟫_ℂ = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; rw [if_pos rfl]; exact inner_occupationVector_self a
  · rw [if_neg h]; exact inner_occupationVector_of_ne h

/-- **Matrix elements of `𝒰_{p+q,p}` of a word kernel on the occupation basis.** -/
theorem inner_U_word {p q : ℕ} (vα vβ : Word p) (m m' : Arr (p + q)) :
    ⟪(basisVector m' : Boson (p + q)),
        U_N_r (r := p) (q := q) (wordKernel vβ vα) (basisVector m)⟫_ℂ =
      if hα : occupation vα ≤ m.1 then
        if hβ : occupation vβ ≤ m'.1 then
          (if m.1 - occupation vα = m'.1 - occupation vβ then
            (((Real.sqrt ((mdesc m.1 (occupation vα) : ℝ) * (q.factorial : ℝ) /
                ((p + q).factorial : ℝ))) *
              Real.sqrt ((mdesc m'.1 (occupation vβ) : ℝ) * (q.factorial : ℝ) /
                ((p + q).factorial : ℝ)) : ℝ) : ℂ) else 0)
        else 0
      else 0 := by
  unfold wordKernel
  rw [inner_U_eq_inner_htmap', inner_htmap_rankOne]
  by_cases hα : occupation vα ≤ m.1
  · by_cases hβ : occupation vβ ≤ m'.1
    · rw [dif_pos hα, dif_pos hβ]
      change ⟪pinner (productVector vβ) (splitIsometry (𝕜 := ℂ) p q (basisVector m' : Tensor (p + q))),
        pinner (productVector vα) (splitIsometry (𝕜 := ℂ) p q (basisVector m : Tensor (p + q)))⟫_ℂ = _
      rw [pinner_basisVector vβ m' hβ, pinner_basisVector vα m hα, inner_smul_left, inner_smul_right,
        inner_basisVector_basisVector, Complex.conj_ofReal]
      have hiff : subArr m' (occupation vβ) (occupation_total vβ) hβ =
          subArr m (occupation vα) (occupation_total vα) hα ↔
          m.1 - occupation vα = m'.1 - occupation vβ := by
        constructor
        · intro h; exact (congrArg Subtype.val h).symm
        · intro h; exact Subtype.ext h.symm
      by_cases he : m.1 - occupation vα = m'.1 - occupation vβ
      · rw [if_pos (hiff.2 he), if_pos he]
        push_cast; ring
      · rw [if_neg (fun h => he (hiff.1 h)), if_neg he]; simp
    · rw [dif_pos hα, dif_neg hβ]
      change ⟪pinner (productVector vβ) (splitIsometry (𝕜 := ℂ) p q (basisVector m' : Tensor (p + q))),
        pinner (productVector vα) (splitIsometry (𝕜 := ℂ) p q (basisVector m : Tensor (p + q)))⟫_ℂ = 0
      rw [pinner_basisVector_of_not_le vβ m' hβ, inner_zero_left]
  · rw [dif_neg hα]
    change ⟪pinner (productVector vβ) (splitIsometry (𝕜 := ℂ) p q (basisVector m' : Tensor (p + q))),
      pinner (productVector vα) (splitIsometry (𝕜 := ℂ) p q (basisVector m : Tensor (p + q)))⟫_ℂ = 0
    rw [pinner_basisVector_of_not_le vα m hα, inner_zero_right]

end MatrixElement

/-! ### Creation/annihilation monomials on occupation kets -/

section Ladder

open QuantumNLS.Occupation (mdesc ket Ann Cre AnnMono CreMono FS)

theorem Ann_pow_ket (a : ℤ) (k : ℕ) (m : Occ) :
    (Ann a ^ k) (ket m) =
      (Real.sqrt ((m a).descFactorial k : ℝ) : ℂ) • ket (m - Finsupp.single a k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, QuantumNLS.Occupation.Ann_ket, smul_smul]
    have hk : (m - Finsupp.single a k) a = m a - k := by simp
    have hsub : m - Finsupp.single a k - QuantumNLS.Occupation.e a = m - Finsupp.single a (k + 1) := by
      rw [tsub_tsub, show QuantumNLS.Occupation.e a = Finsupp.single a 1 from rfl,
        ← Finsupp.single_add]
    rw [hsub, hk, Nat.descFactorial_succ]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    ring

theorem Cre_pow_ket (a : ℤ) (k : ℕ) (n : Occ) :
    (Cre a ^ k) (ket n) =
      (Real.sqrt ((n a + k).descFactorial k : ℝ) : ℂ) • ket (n + Finsupp.single a k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, QuantumNLS.Occupation.Cre_ket, smul_smul]
    have hk : (n + Finsupp.single a k) a = n a + k := by simp
    have hadd : n + Finsupp.single a k + QuantumNLS.Occupation.e a = n + Finsupp.single a (k + 1) := by
      rw [add_assoc, show QuantumNLS.Occupation.e a = Finsupp.single a 1 from rfl,
        ← Finsupp.single_add]
    rw [hadd, hk, show n a + (k + 1) = (n a + k) + 1 by ring, Nat.succ_descFactorial_succ]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    ring

theorem AnnMono_ket (α m : Occ) :
    AnnMono α (ket m) = (Real.sqrt (mdesc m α : ℝ) : ℂ) • ket (m - α) := by
  induction α using Finsupp.induction generalizing m with
  | zero =>
    simp [QuantumNLS.Occupation.AnnMono_zero, mdesc]
  | single_add a k α' ha hk ih =>
    have hdisj : Disjoint (Finsupp.single a k).support α'.support := by
      rw [Finsupp.support_single_ne_zero a hk, Finset.disjoint_singleton_left]; exact ha
    have hα'a : α' a = 0 := Finsupp.notMem_support_iff.1 ha
    rw [QuantumNLS.Occupation.AnnMono_add, Module.End.mul_apply, ih, map_smul,
      QuantumNLS.Occupation.AnnMono_single, Ann_pow_ket, smul_smul]
    have hm : (m - α') a = m a := by simp [hα'a]
    have hmd : mdesc m (Finsupp.single a k + α') =
        (m a).descFactorial k * mdesc m α' := by
      unfold mdesc
      rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (by simp)]
    rw [hm, hmd, tsub_tsub, add_comm α' (Finsupp.single a k)]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    ring

theorem CreMono_ket (β n : Occ) :
    CreMono β (ket n) = (Real.sqrt (mdesc (n + β) β : ℝ) : ℂ) • ket (n + β) := by
  induction β using Finsupp.induction generalizing n with
  | zero =>
    simp [QuantumNLS.Occupation.CreMono_zero, mdesc]
  | single_add a k β' ha hk ih =>
    have hdisj : Disjoint (Finsupp.single a k).support β'.support := by
      rw [Finsupp.support_single_ne_zero a hk, Finset.disjoint_singleton_left]; exact ha
    have hβ'a : β' a = 0 := Finsupp.notMem_support_iff.1 ha
    rw [QuantumNLS.Occupation.CreMono_add, Module.End.mul_apply, ih, map_smul,
      QuantumNLS.Occupation.CreMono_single, Cre_pow_ket, smul_smul]
    have hn : (n + β') a = n a := by simp [hβ'a]
    have hmd : mdesc (n + (Finsupp.single a k + β')) (Finsupp.single a k + β') =
        (n a + k).descFactorial k * mdesc (n + β') β' := by
      unfold mdesc
      rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (by simp)]
      congr 1
      · simp [hβ'a]
      · refine Finsupp.prod_congr fun b hb => ?_
        have hba : b ≠ a := fun h => ha (h ▸ hb)
        simp [Finsupp.single_apply, Ne.symm hba, add_assoc]
    rw [hn, hmd, show n + (Finsupp.single a k + β') = n + β' + Finsupp.single a k by
      rw [add_comm (Finsupp.single a k) β', add_assoc]]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    ring

end Ladder

/-! ### The monomial identity -/

section Monomial

open QuantumNLS.Occupation (mdesc WMono emb ket emb_ket)
open QuantumNLS.OccupationHilbert (core ext_core)
open QuantumNLS.WickSymbols (zm Mon Sym)
open QuantumNLS.BalancedWickDefinition (auxiliaryWick monomial_core)
open QuantumNLS.KernelDefinition

/-- Conjugation of an operator on `Sym^N ℓ²(ℤ)` into the occupation coefficient space by `U4`. -/
def conjU4 (N : ℕ) (T : Boson N →L[ℂ] Boson N) : OccupationHilbert.H N →L[ℂ] OccupationHilbert.H N :=
  (U4 N).toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
    (U4 N).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem conjU4_apply (N : ℕ) (T : Boson N →L[ℂ] Boson N) (x : OccupationHilbert.H N) :
    conjU4 N T x = U4 N (T ((U4 N).symm x)) := rfl

/-- **Fock side**: coordinates of the Wick monomial on an occupation ket. -/
theorem auxiliaryWick_zm_single {N : ℕ} (hN : 0 < N) (α β : Occ) (h : α.degree = β.degree)
    (m0 m' : Arr N) :
    auxiliaryWick N (zm α β) (lp.single 2 m0 (1 : ℂ)) m' =
      if m0.1 - α + β = m'.1 then
        (N : ℂ)⁻¹ ^ α.degree *
          (((Real.sqrt (mdesc m0.1 α : ℝ) : ℝ) : ℂ) *
            ((Real.sqrt (mdesc (m0.1 - α + β) β : ℝ) : ℝ) : ℂ))
      else 0 := by
  have h1 := monomial_core hN α β h (Finsupp.single m0 1) m'
  rw [OccupationHilbert.core_single, emb_ket] at h1
  rw [h1]
  unfold WMono
  rw [LinearMap.smul_apply, Module.End.mul_apply, AnnMono_ket, map_smul, CreMono_ket, smul_smul]
  simp only [Finsupp.smul_apply, ket, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem fall_mul (p q : ℕ) :
    (((p + q).descFactorial p : ℕ) : ℝ) * ((q.factorial : ℝ) / ((p + q).factorial : ℝ)) = 1 := by
  have h := Nat.factorial_mul_descFactorial (Nat.le_add_right p q)
  rw [Nat.add_sub_cancel_left] at h
  have hN : ((p + q).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h' : (q.factorial : ℝ) * (((p + q).descFactorial p : ℕ) : ℝ) = ((p + q).factorial : ℝ) := by
    exact_mod_cast h
  field_simp
  linarith

theorem sqrt_aux (p q : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (((p + q).descFactorial p : ℕ) : ℝ) *
        (Real.sqrt (a * (q.factorial : ℝ) / ((p + q).factorial : ℝ)) *
          Real.sqrt (b * (q.factorial : ℝ) / ((p + q).factorial : ℝ))) =
      Real.sqrt a * Real.sqrt b := by
  have hX : (0 : ℝ) ≤ (q.factorial : ℝ) / ((p + q).factorial : ℝ) := by positivity
  have e : ∀ c : ℝ, c * (q.factorial : ℝ) / ((p + q).factorial : ℝ) =
      c * ((q.factorial : ℝ) / ((p + q).factorial : ℝ)) := fun c => by ring
  rw [e a, e b, Real.sqrt_mul ha, Real.sqrt_mul hb]
  have hXX : Real.sqrt ((q.factorial : ℝ) / ((p + q).factorial : ℝ)) *
      Real.sqrt ((q.factorial : ℝ) / ((p + q).factorial : ℝ)) =
      (q.factorial : ℝ) / ((p + q).factorial : ℝ) := Real.mul_self_sqrt hX
  have hf := fall_mul p q
  calc (((p + q).descFactorial p : ℕ) : ℝ) * (Real.sqrt a * Real.sqrt (q.factorial / (p + q).factorial) *
        (Real.sqrt b * Real.sqrt (q.factorial / (p + q).factorial)))
      = Real.sqrt a * Real.sqrt b * ((((p + q).descFactorial p : ℕ) : ℝ) *
          (Real.sqrt (q.factorial / (p + q).factorial) * Real.sqrt (q.factorial / (p + q).factorial))) := by
        ring
    _ = Real.sqrt a * Real.sqrt b := by rw [hXX, hf, mul_one]

/-- **The monomial identity**: the Wick monomial `N^{-p}(b^*)^β b^α` on `ℓ²(𝓜_N)` equals `U4`-conjugate of
`(N)_p N^{-p} 𝒰_{N,p}` of the word kernel `|e_{v_β}⟩⟨e_{v_α}|` (`v_α`, `v_β` words of occupations `α`, `β`). -/
theorem auxiliaryWick_zm_eq (p q : ℕ) (hp : 1 ≤ p) (α β : Arr p) :
    auxiliaryWick (p + q) (zm α.1 β.1) =
      conjU4 (p + q) (((((p + q).descFactorial p : ℕ) : ℂ) * (((p + q : ℕ) : ℂ))⁻¹ ^ p) •
        U_N_r (r := p) (q := q) (wordKernel (representative β) (representative α))) := by
  have hN : 0 < p + q := by omega
  have hdeg : α.1.degree = β.1.degree := by
    have h1 := α.2; have h2 := β.2
    unfold IsArray total at h1 h2
    omega
  have hdα : α.1.degree = p := by have h1 := α.2; unfold IsArray total at h1; exact h1
  apply ext_core
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single m0 z =>
    have hz : (lp.single 2 m0 z : OccupationHilbert.H (p + q)) = z • lp.single 2 m0 1 := by
      rw [← lp.single_smul]; simp
    rw [OccupationHilbert.core_single, hz, map_smul, map_smul]
    congr 1
    apply lp.ext
    funext m'
    rw [auxiliaryWick_zm_single hN α.1 β.1 hdeg m0 m', conjU4_apply, U4_symm_single, U4_apply]
    rw [ContinuousLinearMap.smul_apply]
    change _ = ⟪(basisVector m' : Boson (p + q)),
      ((((p + q).descFactorial p : ℕ) : ℂ) * (((p + q : ℕ) : ℂ))⁻¹ ^ p) •
        U_N_r (r := p) (q := q) (wordKernel (representative β) (representative α)) (basisVector m0)⟫_ℂ
    rw [inner_smul_right, inner_U_word]
    simp only [occupation_representative]
    rw [hdα]
    by_cases hα : α.1 ≤ m0.1
    · rw [dif_pos hα]
      by_cases he : m0.1 - α.1 + β.1 = m'.1
      · rw [if_pos he]
        have hβ : β.1 ≤ m'.1 := he ▸ le_add_self
        have h2 : m0.1 - α.1 = m'.1 - β.1 := by rw [← he, add_tsub_cancel_right]
        rw [dif_pos hβ, if_pos h2, ← he]
        have hs := congrArg (fun r : ℝ => (r : ℂ))
          (sqrt_aux p q (mdesc m0.1 α.1 : ℝ) (mdesc (m0.1 - α.1 + β.1) β.1 : ℝ)
            (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        simp only [Complex.ofReal_mul] at hs
        push_cast at hs ⊢
        linear_combination (-(((p : ℂ) + q)⁻¹ ^ p)) * hs
      · rw [if_neg he]
        by_cases hβ : β.1 ≤ m'.1
        · rw [dif_pos hβ]
          have h2 : ¬ (m0.1 - α.1 = m'.1 - β.1) := fun h2 => he (by
            rw [h2, tsub_add_cancel_of_le hβ])
          rw [if_neg h2]; simp
        · rw [dif_neg hβ]; simp
    · rw [dif_neg hα]
      have h0 : mdesc m0.1 α.1 = 0 := mdesc_eq_zero_of_not_le hα
      simp [h0]

end Monomial

/-! ### The polynomial identity -/

section Polynomial

open QuantumNLS.Occupation (mdesc WMono emb ket emb_ket)
open QuantumNLS.OccupationHilbert (core ext_core)
open QuantumNLS.WickSymbols (zm Mon Sym WN symLin_expand Balanced)
open QuantumNLS.BalancedWickDefinition (auxiliaryWick monomial_core)
open QuantumNLS.KernelDefinition

/-- The word kernel of a monomial `z^α \bar z^β` of bidegree `(p,p)` (zero for other monomials):
`|e_{v_β}⟩⟨e_{v_α}|`, symmetrized. -/
def Kmono (p : ℕ) (pr : Mon) : BoundedSymmetricKernel OneParticle p :=
  if h : total pr.1 = p ∧ total pr.2 = p then
    wordKernel (representative (⟨pr.2, h.2⟩ : Arr p)) (representative (⟨pr.1, h.1⟩ : Arr p))
  else 0

/-- **The auxiliary kernel of a balanced homogeneous polynomial** `f = ∑ f_{αβ} z^α \bar z^β`
(all monomials of bidegree `(p,p)`): `A_f = ∑ f_{αβ} P_p |e_{v_β}⟩⟨e_{v_α}| P_p` on `Sym^p ℓ²(ℤ)`. -/
def kernelOf (p : ℕ) (f : Sym) : BoundedSymmetricKernel OneParticle p :=
  ∑ pr ∈ f.coeff.support, f.coeff pr • Kmono p pr

theorem aux_core_sum {N : ℕ} (hN : 0 < N) {f : Sym} (hb : Balanced f)
    (v : QuantumNLS.Occupation.Sector N) :
    auxiliaryWick N f (core N v) =
      ∑ pr ∈ f.coeff.support, f.coeff pr • auxiliaryWick N (zm pr.1 pr.2) (core N v) := by
  apply lp.ext
  funext m
  have hbm : ∀ pr ∈ f.coeff.support, Balanced (zm pr.1 pr.2) := fun pr hpr =>
    QuantumNLS.BalancedWickDefinition.balanced_monomial pr.1 pr.2 (hb pr hpr)
  rw [auxiliaryWick, ite_eq_right hN.ne', QuantumNLS.WickBounds.WHil_core hN hb,
    OccupationHilbert.core_apply, QuantumNLS.WickBounds.WS_apply]
  have hWN : WN N f = ∑ pr ∈ f.coeff.support, f.coeff pr • WMono N pr.1 pr.2 :=
    symLin_expand _ f
  rw [hWN]
  have hR : (∑ pr ∈ f.coeff.support, f.coeff pr • auxiliaryWick N (zm pr.1 pr.2) (core N v) :
      OccupationHilbert.H N) m =
      ∑ pr ∈ f.coeff.support, f.coeff pr * auxiliaryWick N (zm pr.1 pr.2) (core N v) m := by
    simp only [lp.coeFn_sum, lp.coeFn_smul]
    rw [Finset.sum_apply]
    simp
  rw [hR, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun pr hpr => ?_
  rw [monomial_core hN pr.1 pr.2 (hb pr hpr) v m]
  simp


/-- `genericU_N_r N r` as a linear map in the kernel. -/
def UlinL (N r : ℕ) (hr : r ≤ N) : BoundedSymmetricKernel OneParticle r →ₗ[ℂ]
    (SymSector ℂ OneParticle N →L[ℂ] SymSector ℂ OneParticle N) where
  toFun A := genericU_N_r N r hr A
  map_add' A B := QuantumNLS.RootOverlapLimit.genericU_add N r hr A B
  map_smul' c A := by simpa using QuantumNLS.RootOverlapLimit.genericU_smul N r hr c A

/-- **The polynomial identity.**  For `f = ∑ f_{αβ} z^α \bar z^β` homogeneous of bidegree `(p,p)`, `p ≥ 1`, on the
occupation coefficient space `ℓ²(𝓜_{p+q})`:
`W_N(f) = (N)_p N^{-p} · 𝒰_{N,p}(A_f)` (conjugated by `U4`), where `A_f = kernelOf p f` is the auxiliary kernel of `f`. -/
theorem auxiliaryWick_eq_kernel (p q : ℕ) (hp : 1 ≤ p) (f : Sym)
    (hf : ∀ pr ∈ f.coeff.support, total pr.1 = p ∧ total pr.2 = p) :
    auxiliaryWick (p + q) f =
      conjU4 (p + q) (((((p + q).descFactorial p : ℕ) : ℂ) * (((p + q : ℕ) : ℂ))⁻¹ ^ p) •
        genericU_N_r (p + q) p (Nat.le_add_right p q) (kernelOf p f)) := by
  have hN : 0 < p + q := by omega
  have hb : Balanced f := fun pr hpr => (hf pr hpr).1.trans (hf pr hpr).2.symm
  have hU : genericU_N_r (p + q) p (Nat.le_add_right p q) (kernelOf p f) =
      ∑ pr ∈ f.coeff.support, f.coeff pr • U_N_r (r := p) (q := q) (Kmono p pr) := by
    unfold kernelOf
    have h1 := map_sum (UlinL (p + q) p (Nat.le_add_right p q)) (fun pr => f.coeff pr • Kmono p pr)
      f.coeff.support
    change genericU_N_r (p + q) p (Nat.le_add_right p q) (∑ pr ∈ f.coeff.support, f.coeff pr • Kmono p pr) = _
    have h2 : UlinL (p + q) p (Nat.le_add_right p q) (∑ pr ∈ f.coeff.support, f.coeff pr • Kmono p pr) =
      genericU_N_r (p + q) p (Nat.le_add_right p q) (∑ pr ∈ f.coeff.support, f.coeff pr • Kmono p pr) := rfl
    rw [← h2, h1]
    refine Finset.sum_congr rfl fun pr _ => ?_
    rw [map_smul]
    change f.coeff pr • genericU_N_r (p + q) p (Nat.le_add_right p q) (Kmono p pr) = _
    rw [QuantumNLS.MixedCommutator.genericU_add_eq p q (Nat.le_add_right p q)]
  have hmono : ∀ pr ∈ f.coeff.support, auxiliaryWick (p + q) (zm pr.1 pr.2) =
      conjU4 (p + q) (((((p + q).descFactorial p : ℕ) : ℂ) * (((p + q : ℕ) : ℂ))⁻¹ ^ p) •
        U_N_r (r := p) (q := q) (Kmono p pr)) := by
    intro pr hpr
    have h := hf pr hpr
    have := auxiliaryWick_zm_eq p q hp ⟨pr.1, h.1⟩ ⟨pr.2, h.2⟩
    rw [Kmono, dif_pos h]
    exact this
  apply ext_core
  intro v
  rw [aux_core_sum hN hb, hU]
  rw [Finset.sum_congr rfl (fun pr hpr => by rw [hmono pr hpr])]
  simp only [conjU4_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, map_sum,
    map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun pr _ => ?_
  rw [smul_comm]

end Polynomial

/-! ### The pulled-back equality and the polynomial-kernel relation -/

section PullBack

open QuantumNLS.BalancedWickDefinition (Polynomial wick kernelQuantization evaluate quantization)
open QuantumNLS.WickSymbols (Sym)

variable {L : ℝ} [Fact (0 < L)]

/-- **DEF-032 convention, proved.**  For a balanced finite polynomial `f` homogeneous of bidegree `(p,p)`, `p ≥ 1`
(`N = p+q`), its gauged Wick operator is the pullback of `(N)_p N^{-p}` times the normalized placement
`𝒰_{N,p}` of the auxiliary kernel `A_f` on the auxiliary label sector:
`𝒲_N^q(f) = J_N^*((N)_p N^{-p} 𝒰_{N,p}(A_f))J_N`, i.e. `wick = kernelQuantization` for `A_f = kernelOf p f.symbol`. -/
theorem wick_eq_kernelQuantization (p q : ℕ) (hp : 1 ≤ p)
    (b : QuantumNLS.BetheCoefficientTransform.BetheBasis L (p + q))
    (g : QuantumNLS.BetheOccupationGauge.Gauge) (f : Polynomial)
    (hf : ∀ pr ∈ f.symbol.coeff.support, total pr.1 = p ∧ total pr.2 = p) :
    wick b g f = kernelQuantization b g (Nat.le_add_right p q) (kernelOf p f.symbol) := by
  ext ψ
  have h := auxiliaryWick_eq_kernel p q hp f.symbol hf
  unfold wick quantization kernelQuantization QuantumNLS.BalancedWickDefinition.coefficientUnitary
    QuantumNLS.BetheCoefficientTransform.fockTransform
  dsimp only
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [h, conjU4_apply]
  simp

end PullBack

/-! ### The polynomial-kernel relation: the product symbol of `A_f` is `f` -/

section Symbol

open QuantumNLS.KernelDefinition QuantumNLS.TensorPlacements QuantumNLS.MixedTraceNorm
open QuantumNLS.BalancedWickDefinition (Polynomial evaluate)

theorem kernelProductSymbol_wordKernel {p : ℕ} (vβ vα : Word p) (u : OneParticle) :
    kernelProductSymbol (wordKernel vβ vα) u =
      (occupation vα).prod (fun n k => u n ^ k) *
        (occupation vβ).prod (fun n k => (starRingEnd ℂ) (u n) ^ k) := by
  unfold kernelProductSymbol wordKernel
  set x : SymSector ℂ OneParticle p := ⟨htpow p u, htpow_mem_symSector p u⟩ with hx
  have h1 : ((symKernel (InnerProductSpace.rankOne ℂ (productVector vβ) (productVector vα)) x :
      SymSector ℂ OneParticle p) : Tensor p) =
      symProj ℂ OneParticle p (InnerProductSpace.rankOne ℂ (productVector vβ) (productVector vα)
        (x : Tensor p)) := rfl
  rw [h1, inner_symProj_of_mem x, InnerProductSpace.rankOne_apply, inner_smul_right]
  have h2 : ⟪productVector vα, (htpow p u : Tensor p)⟫_ℂ = (occupation vα).prod (fun n k => u n ^ k) := by
    rw [inner_productVector_htpow, prod_occupation]
  have h3 : ⟪(htpow p u : Tensor p), productVector vβ⟫_ℂ =
      (starRingEnd ℂ) ((occupation vβ).prod (fun n k => u n ^ k)) := by
    rw [← inner_conj_symm, inner_productVector_htpow, prod_occupation]
  have hxx : (x : Tensor p) = htpow p u := rfl
  rw [hxx, h2, h3]
  simp [Finsupp.prod, map_prod, map_pow, mul_comm]

/-- `A ↦ ⟨u^{⊗p}, A u^{⊗p}⟩` is linear in the kernel. -/
def kpsL {p : ℕ} (u : OneParticle) : BoundedSymmetricKernel OneParticle p →ₗ[ℂ] ℂ where
  toFun A := kernelProductSymbol A u
  map_add' A B := by
    simp [kernelProductSymbol, inner_add_right]
  map_smul' c A := by
    simp [kernelProductSymbol, inner_smul_right]

/-- **The polynomial-kernel relation.**  The product symbol `⟨u^{⊗p}, A_f u^{⊗p}⟩` of the auxiliary kernel
`A_f` of a balanced homogeneous polynomial `f` of bidegree `(p,p)` is exactly the literal evaluation `f(u)`
(`BalancedWickDefinition.evaluate`), `f(w) = ∑ f_{αβ} w^α \bar w^β`. -/
theorem kernelOf_symbol (p : ℕ) (f : Polynomial)
    (hf : ∀ pr ∈ f.symbol.coeff.support, total pr.1 = p ∧ total pr.2 = p) (u : OneParticle) :
    kernelProductSymbol (kernelOf p f.symbol) u = evaluate f (fun n => u n) := by
  have h := map_sum (kpsL (p := p) u) (fun pr => f.symbol.coeff pr • Kmono p pr)
    f.symbol.coeff.support
  change kernelProductSymbol (∑ pr ∈ f.symbol.coeff.support, f.symbol.coeff pr • Kmono p pr) u = _
  have h' : kernelProductSymbol (∑ pr ∈ f.symbol.coeff.support, f.symbol.coeff pr • Kmono p pr) u =
      ∑ pr ∈ f.symbol.coeff.support, f.symbol.coeff pr * kernelProductSymbol (Kmono p pr) u := by
    have := h
    simp only [kpsL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul, smul_eq_mul] at this
    exact this
  rw [h']
  unfold evaluate
  refine Finset.sum_congr rfl fun pr hpr => ?_
  have hh := hf pr hpr
  rw [Kmono, dif_pos hh, kernelProductSymbol_wordKernel, occupation_representative,
    occupation_representative]
  ring

end Symbol

end QuantumNLS.WickKernelBridge

#print axioms QuantumNLS.WickKernelBridge.inner_productVector_basisVector
#print axioms QuantumNLS.WickKernelBridge.inner_U_eq_inner_htmap'
#print axioms QuantumNLS.WickKernelBridge.inner_htmap_rankOne
#print axioms QuantumNLS.WickKernelBridge.pinner_basisVector
#print axioms QuantumNLS.WickKernelBridge.inner_U_word
#print axioms QuantumNLS.WickKernelBridge.AnnMono_ket
#print axioms QuantumNLS.WickKernelBridge.CreMono_ket
#print axioms QuantumNLS.WickKernelBridge.auxiliaryWick_zm_eq
#print axioms QuantumNLS.WickKernelBridge.auxiliaryWick_eq_kernel
#print axioms QuantumNLS.WickKernelBridge.wick_eq_kernelQuantization
#print axioms QuantumNLS.WickKernelBridge.kernelProductSymbol_wordKernel
#print axioms QuantumNLS.WickKernelBridge.kernelOf_symbol
