import Mathlib
import QuantumNLS.KernelFactorialBound
import QuantumNLS.TransferNormality
import QuantumNLS.NormalityBridge
import QuantumNLS.FunctionalLinearizationVarying

/-!
# PROP-026 remainder 3: the commuting quadratures `Re S_N(z_θ)`, `Im S_N(z_θ)` and their joint functional calculus

(`source/chapters/propagation/mixed_propagation.tex:355-383`, `eq:MP-C0`, `eq:MP-L`, `lem:MP-linearization`.)

Imports read-only: KernelFactorialBound `a3f33627` (`kernel_bound`, `prop026_traceNorm_transfer_sharp`),
MixedCommutator `1df830ea`, TransferNormality `2fa59f86` (`transfer_normality`), UnconditionalBetheBasis
`ae212789`, NormalityBridge (`differentiable_normalizedTransfer`), FunctionalLinearizationVarying (`hB_of_continuous`).

* **Joint functional calculus** (explicit, from Mathlib's CFC of the normal element `T`): for a normal `T` with
  `‖T‖ ≤ R`, `quadHom T R : C(K_R, ℂ) →⋆ₐ[ℂ] B(H)`, `K_R = closedBall 0 R ⊆ ℝ² = EuclideanSpace ℝ (Fin 2)`,
  `quadHom T (liftC g) = cfc (g ∘ ι) T` (`ι : ℂ ≃ ℝ²`, `ζ ↦ (Re ζ, Im ζ)`), `quadHom T (x₀) = (T+T^*)/2 = Re T`,
  `quadHom T (x₁) = (T-T^*)/(2i) = Im T`.
* **`hquad`** (`quad_hquad`): `Φ_θ(coordC j) = α S_N(z_θ) + β S_N(z_θ)^*`, `‖α‖+‖β‖ = 1`.
* **`hcomm`**: all `Re/Im S_N(z_θ)` commute (from `transfer_normality`).
* **`hB`**: norm continuity of `z ↦ S_N(z)` and compactness of the parameter space.
* the uniform spectral bound `‖S_N(z)‖ ≤ Rbd` on `|Im z| ≤ h` (`norm_normalizedTransfer_le`, from `kernel_bound`);
* `PhiFam_deviation`: the background identification `b_θ = ι(s(z_θ)) = (Re s, Im s)`: the source's
  `‖(S_N(z_θ) - s)φ‖ ≤ δ` gives `‖(B_{θ,j} - b_{θ,j})φ‖ ≤ δ` for both quadratures (S_N normal);
* `quadHom_quadF`, `quadHom_linOp`, `C0N_eq_reOp`, `LN_eq_reOp`, `LN_eq_chart` (generic Hilbert space, apply with
  `H = Sym^N`, `S_θ = S_N(z_θ)`; `PhiFam'_eq`): for `F_θ(x) = Re(u_θ g_θ(x₀ + i x₁))`,
  `F_θ(B_θ) = Re(u_θ g_θ(S_θ))`, `C_{0,N} = ∫F_θ(B_θ)dν = Re ∫ u_θ f_{z_θ}(S_θ) dν` (`eq:MP-C0`), and with `g_θ`
  equal near `s_θ` to the chart `chartLambda` of `eq:MP-chart`, `L_N = Re ∫ u_θ D(z_θ)^{-1} S_θ dν` (`eq:MP-L`;
  `∂_wλ(z,s(z)) = D(z)^{-1}` from `MixedTraceNorm.hasDerivAt_chartLambda`);
* `hdF_of_continuous`, `hFm_of_continuous`: PROP-014 `hFm`, `hdF` from continuity on a compact parameter space;
* **`prop026_traceNorm_physical`**: PROP-026 (trace-norm form) for the physical family with `hquad`, `hcomm`, `hB`, `hker`
  discharged.

Unrealized objects kept as explicit parameters (listed precisely in the checkpoint): the contour data
(`z_θ`, the complex weight `u_θ` encoding `-p_t(z)·dz/dθ·θ_n/(2πκ)` and the finite measure `ν`), the bounded smooth
extensions `f_z = g_θ`, the background `A, D, G, s` (only `s_θ` enters the deviation hypothesis, `D_θ` enters `LN_eq_chart`),
the state `φ ∈ ran P_N` with the spectral deviation `δ`, the weights `w, M0`, and `F_θ` itself in the general theorem.
The PROP-014 operator-norm Bochner convention is the owner-accepted formulation inherited from `MixedTraceNorm`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped InnerProductSpace ComplexConjugate BigOperators Nat ContDiff ENNReal
open QuantumNLS.FunctionalLinearization QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor
  QuantumNLS.KernelDefinition QuantumNLS.NormalizedTransfer

namespace QuantumNLS.MixedQuadratures

/-! ### Generic: the joint functional calculus of a normal operator -/

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `ℂ ≃ ℝ²` as a linear isometry, `ζ ↦ (Re ζ, Im ζ)`. -/
def isoR2 : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr

theorem isoR2_apply_zero (ζ : ℂ) : isoR2 ζ 0 = ζ.re := by
  simp [isoR2, Complex.orthonormalBasisOneI_repr_apply]

theorem isoR2_apply_one (ζ : ℂ) : isoR2 ζ 1 = ζ.im := by
  simp [isoR2, Complex.orthonormalBasisOneI_repr_apply]

/-- The closed disc of radius `R` in `ℝ²`. -/
def Kdisc (R : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 R

instance (R : ℝ) : CompactSpace (Kdisc R) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)

theorem isStarNormal_of_commute {T : H →L[ℂ] H} (h : Commute (ContinuousLinearMap.adjoint T) T) :
    IsStarNormal T :=
  ⟨by rw [ContinuousLinearMap.star_eq_adjoint]; exact h⟩

theorem mem_Kdisc_of_spec (T : H →L[ℂ] H) (R : ℝ) (hR : ‖T‖ ≤ R) (ζ : ℂ) (hζ : ζ ∈ spectrum ℂ T) :
    isoR2 ζ ∈ Kdisc R := by
  have h0 := spectrum.subset_closedBall_norm_mul T hζ
  rw [Metric.mem_closedBall, dist_zero_right] at h0
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h2 : ‖ζ‖ ≤ ‖T‖ := h0.trans (by
    have := mul_le_mul_of_nonneg_left h1 (norm_nonneg T)
    linarith)
  show isoR2 ζ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R
  rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
  exact h2.trans hR

/-- The continuous map from the spectrum into the disc, `ζ ↦ (Re ζ, Im ζ)`. -/
def specMap (T : H →L[ℂ] H) (R : ℝ) (hR : ‖T‖ ≤ R) : C(spectrum ℂ T, Kdisc R) :=
  ⟨fun ζ => ⟨isoR2 ζ.1, mem_Kdisc_of_spec T R hR ζ.1 ζ.2⟩,
    (isoR2.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- **The joint continuous functional calculus** of the two commuting quadratures of a normal `T` on the disc. -/
def quadHom (T : H →L[ℂ] H) (hT : IsStarNormal T) (R : ℝ) (hR : ‖T‖ ≤ R) :
    C(Kdisc R, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (cfcHom hT).comp (ContinuousMap.compStarAlgHom' ℂ ℂ (specMap T R hR))

theorem quadHom_liftC (T : H →L[ℂ] H) (hT : IsStarNormal T) (R : ℝ) (hR : ‖T‖ ≤ R)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (hg : Continuous g) :
    quadHom T hT R hR (liftC (K := Kdisc R) g hg) = cfc (fun ζ : ℂ => g (isoR2 ζ)) T := by
  have hc : ContinuousOn (fun ζ : ℂ => g (isoR2 ζ)) (spectrum ℂ T) :=
    (hg.comp isoR2.continuous).continuousOn
  rw [cfc_apply _ T hT hc]
  rfl

theorem quadHom_coord0 (T : H →L[ℂ] H) (hT : IsStarNormal T) (R : ℝ) (hR : ‖T‖ ≤ R) :
    quadHom T hT R hR (coordC (d := 2) (K := Kdisc R) 0) =
      (1 / 2 : ℂ) • (T + ContinuousLinearMap.adjoint T) := by
  unfold coordC
  rw [quadHom_liftC]
  show cfc (fun ζ : ℂ => ((isoR2 ζ 0 : ℝ) : ℂ)) T = _
  have e' : (fun ζ : ℂ => ((isoR2 ζ 0 : ℝ) : ℂ)) = fun ζ => (1 / 2 : ℂ) * (id ζ + star ζ) := by
    funext ζ
    rw [isoR2_apply_zero]
    simp only [id, Complex.star_def]
    apply Complex.ext <;> simp <;> ring
  have hid : ContinuousOn (id : ℂ → ℂ) (spectrum ℂ T) := continuousOn_id
  have hst : ContinuousOn (star : ℂ → ℂ) (spectrum ℂ T) := continuous_star.continuousOn
  have hadd : ContinuousOn (fun ζ : ℂ => id ζ + star ζ) (spectrum ℂ T) := hid.add hst
  have h1 : cfc (fun ζ : ℂ => (1 / 2 : ℂ) * (id ζ + star ζ)) T =
      (1 / 2 : ℂ) • cfc (fun ζ : ℂ => id ζ + star ζ) T := cfc_const_mul (1 / 2 : ℂ) _ T hadd
  have h2 : cfc (fun ζ : ℂ => id ζ + star ζ) T = cfc (id : ℂ → ℂ) T + cfc (star : ℂ → ℂ) T :=
    cfc_add (hf := hid) (hg := hst)
  have h3 : cfc (id : ℂ → ℂ) T = T := cfc_id ℂ T hT
  have h4 : cfc (star · : ℂ → ℂ) T = star T := cfc_star_id T hT
  rw [e', h1, h2, h3, h4, ContinuousLinearMap.star_eq_adjoint]

theorem quadHom_coord1 (T : H →L[ℂ] H) (hT : IsStarNormal T) (R : ℝ) (hR : ‖T‖ ≤ R) :
    quadHom T hT R hR (coordC (d := 2) (K := Kdisc R) 1) =
      (-Complex.I / 2 : ℂ) • (T - ContinuousLinearMap.adjoint T) := by
  unfold coordC
  rw [quadHom_liftC]
  show cfc (fun ζ : ℂ => ((isoR2 ζ 1 : ℝ) : ℂ)) T = _
  have e' : (fun ζ : ℂ => ((isoR2 ζ 1 : ℝ) : ℂ)) = fun ζ => (-Complex.I / 2 : ℂ) * (id ζ - star ζ) := by
    funext ζ
    rw [isoR2_apply_one]
    simp only [id, Complex.star_def]
    apply Complex.ext <;> simp <;> ring
  have hid : ContinuousOn (id : ℂ → ℂ) (spectrum ℂ T) := continuousOn_id
  have hst : ContinuousOn (star : ℂ → ℂ) (spectrum ℂ T) := continuous_star.continuousOn
  have hsub : ContinuousOn (fun ζ : ℂ => id ζ - star ζ) (spectrum ℂ T) := hid.sub hst
  have h1 : cfc (fun ζ : ℂ => (-Complex.I / 2 : ℂ) * (id ζ - star ζ)) T =
      (-Complex.I / 2 : ℂ) • cfc (fun ζ : ℂ => id ζ - star ζ) T := cfc_const_mul (-Complex.I / 2 : ℂ) _ T hsub
  have h2 : cfc (fun ζ : ℂ => id ζ - star ζ) T = cfc (id : ℂ → ℂ) T - cfc (star : ℂ → ℂ) T :=
    cfc_sub (hf := hid) (hg := hst)
  have h3 : cfc (id : ℂ → ℂ) T = T := cfc_id ℂ T hT
  have h4 : cfc (star · : ℂ → ℂ) T = star T := cfc_star_id T hT
  rw [e', h1, h2, h3, h4, ContinuousLinearMap.star_eq_adjoint]

/-- **`hquad`**: each coordinate quadrature is `α T + β T^*` with `‖α‖ + ‖β‖ ≤ 1`. -/
theorem quad_hquad (T : H →L[ℂ] H) (hT : IsStarNormal T) (R : ℝ) (hR : ‖T‖ ≤ R) (j : Fin 2) :
    ∃ α β : ℂ, ‖α‖ + ‖β‖ ≤ 1 ∧
      quadHom T hT R hR (coordC (d := 2) (K := Kdisc R) j) = α • T + β • ContinuousLinearMap.adjoint T := by
  fin_cases j
  · refine ⟨1 / 2, 1 / 2, ?_, ?_⟩
    · norm_num
    · show quadHom T hT R hR (coordC (d := 2) (K := Kdisc R) 0) = _
      rw [quadHom_coord0, smul_add]
  · refine ⟨-Complex.I / 2, Complex.I / 2, ?_, ?_⟩
    · simp
      norm_num
    · show quadHom T hT R hR (coordC (d := 2) (K := Kdisc R) 1) = _
      rw [quadHom_coord1, smul_sub, sub_eq_add_neg, ← neg_smul]
      congr 2
      ring

end Generic


/-! ### The physical family -/

section Physical

open QuantumNLS.KernelFactorialBound QuantumNLS.HighMomentsRank

variable (L : ℝ) [Fact (0 < L)]

/-- The uniform spectral bound on the strip `|Im z| ≤ h`. -/
def Rbd (κ h : ℝ) : ℝ :=
  1 + Real.exp (L * h) + 2 * Real.exp (L * h) * ((|κ| * L) * Real.exp (|κ| * L))

theorem norm_one_add_exp_le (z : ℂ) (h : ℝ) (hz : |z.im| ≤ h) :
    ‖1 + Complex.exp (Complex.I * z * L)‖ ≤ 1 + Real.exp (L * h) := by
  have hL : 0 < L := Fact.out
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, Complex.norm_exp]
  have : (Complex.I * z * (L : ℂ)).re = -(z.im * L) := by simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have h1 : -(z.im * L) ≤ L * h := by
    have := neg_abs_le z.im
    nlinarith [abs_nonneg z.im]
  linarith [Real.exp_le_exp.mpr h1]

theorem norm_normalizedTransfer_le (κ : ℝ) (N : ℕ) (z : ℂ) (h : ℝ) (hz : |z.im| ≤ h) :
    ‖normalizedTransfer L κ N z‖ ≤ Rbd L κ h := by
  have hL : 0 < L := Fact.out
  unfold Rbd
  have hsplit : normalizedTransfer L κ N z =
      (1 + Complex.exp (Complex.I * z * L)) • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) +
      ∑ j : Fin N, (((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ) •
        genericU_N_r N (j.val + 1) j.2 (orderedKernel L (j.val + 1) z) := rfl
  rw [hsplit]
  refine le_trans (norm_add_le (E := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) _ _) ?_
  have h1 : ‖(1 + Complex.exp (Complex.I * z * L)) • ContinuousLinearMap.id ℂ
      (SymSector ℂ (L2T L) N)‖ ≤ 1 + Real.exp (L * h) := by
    refine (QuantumNLS.MixedCommutator.norm_smul_clm_le _ _).trans ?_
    have hid : ‖ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    calc _ ≤ ‖1 + Complex.exp (Complex.I * z * L)‖ * 1 :=
          mul_le_mul_of_nonneg_left hid (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact norm_one_add_exp_le L z h hz
  have hex : Real.exp (L * |z.im|) ≤ Real.exp (L * h) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz hL.le)
  have hterm : ∀ j : Fin N, ‖(((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ) •
      genericU_N_r N (j.val + 1) j.2 (orderedKernel L (j.val + 1) z)‖ ≤
      2 * Real.exp (L * h) * (((j : ℝ) + 1) * ((|κ| * L) ^ (j.val + 1) /
        Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ))) := by
    intro j
    have hN0 : 0 < N := j.pos
    have hb := fallR_bounds N hN0 (j.val + 1) j.2
    refine (QuantumNLS.MixedCommutator.norm_smul_clm_le _ _).trans ?_
    have hU := norm_genericU_N_r_le N (j.val + 1) j.2 (orderedKernel L (j.val + 1) z)
    have hkb := kernel_bound (L := L) κ (j.val + 1) z
    have hcoef : ‖(((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ)‖ ≤ |κ| ^ (j.val + 1) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hb.1]
      calc |κ| ^ (j.val + 1) * fallR N (j.val + 1) ≤ |κ| ^ (j.val + 1) * 1 :=
            mul_le_mul_of_nonneg_left hb.2.2 (by positivity)
        _ = _ := mul_one _
    calc _ ≤ |κ| ^ (j.val + 1) * ‖orderedKernel L (j.val + 1) z‖ :=
          mul_le_mul hcoef hU (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
      _ ≤ 2 * Real.exp (L * |z.im|) * (|κ| * L) ^ (j.val + 1) /
            Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ) := hkb
      _ = 2 * Real.exp (L * |z.im|) * ((|κ| * L) ^ (j.val + 1) /
            Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ)) := by ring
      _ ≤ 2 * Real.exp (L * h) * ((|κ| * L) ^ (j.val + 1) /
            Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 2 * Real.exp (L * h) * (((j : ℝ) + 1) * ((|κ| * L) ^ (j.val + 1) /
            Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hq : 0 ≤ (|κ| * L) ^ (j.val + 1) / Real.sqrt (((2 * (j.val + 1))! : ℕ) : ℝ) := by positivity
          have : (1 : ℝ) ≤ (j : ℝ) + 1 := by
            have := (Nat.cast_nonneg j.val : (0 : ℝ) ≤ j.val)
            show (1 : ℝ) ≤ ((j.val : ℕ) : ℝ) + 1
            linarith
          nlinarith
  have h2 : ‖∑ j : Fin N, (((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ) •
      genericU_N_r N (j.val + 1) j.2 (orderedKernel L (j.val + 1) z)‖ ≤
      2 * Real.exp (L * h) * ((|κ| * L) * Real.exp (|κ| * L)) := by
    refine le_trans (norm_sum_le (E := SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) Finset.univ _) ?_
    refine (Finset.sum_le_sum (fun j _ => hterm j)).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (QuantumNLS.MixedCommutator.sum_weight_le (|κ| * L) (by positivity) N)
      (by positivity)
  linarith


end Physical

/-! ### The family `Φ_θ` of joint functional calculi of `S_N(z_θ)` -/

section Family

open MeasureTheory QuantumNLS.TransferNormality

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_lin (A B : H →L[ℂ] H) (h1 : Commute A B) (h2 : Commute A (ContinuousLinearMap.adjoint B))
    (h3 : Commute (ContinuousLinearMap.adjoint A) B)
    (h4 : Commute (ContinuousLinearMap.adjoint A) (ContinuousLinearMap.adjoint B))
    (α β α' β' : ℂ) :
    Commute (α • A + β • ContinuousLinearMap.adjoint A) (α' • B + β' • ContinuousLinearMap.adjoint B) :=
  Commute.add_left
    (Commute.add_right ((h1.smul_left α).smul_right α') ((h2.smul_left α).smul_right β'))
    (Commute.add_right ((h3.smul_left β).smul_right α') ((h4.smul_left β).smul_right β'))

theorem norm_adjoint_apply_eq (A : H →L[ℂ] H) (h : Commute (ContinuousLinearMap.adjoint A) A) (x : H) :
    ‖ContinuousLinearMap.adjoint A x‖ = ‖A x‖ := by
  have e1 := ContinuousLinearMap.adjoint_inner_left A (ContinuousLinearMap.adjoint A x) x
  have e2 := ContinuousLinearMap.adjoint_inner_right A x (A x)
  have e3 : A (ContinuousLinearMap.adjoint A x) = ContinuousLinearMap.adjoint A (A x) := by
    have := congrArg (fun T : H →L[ℂ] H => T x) h.eq
    simpa using this.symm
  rw [inner_self_eq_norm_sq_to_K] at e1
  rw [inner_self_eq_norm_sq_to_K] at e2
  rw [e3] at e1
  have h0 := e1.trans e2
  have h1 : ‖ContinuousLinearMap.adjoint A x‖ ^ 2 = ‖A x‖ ^ 2 := by exact_mod_cast h0
  have h2 := congrArg Real.sqrt h1
  simpa [Real.sqrt_sq (norm_nonneg _)] using h2

theorem norm_half_le (A : H →L[ℂ] H) (x : H) (hn : ‖ContinuousLinearMap.adjoint A x‖ = ‖A x‖) (c e : ℂ)
    (hc : ‖c‖ ≤ 1 / 2) (he : ‖e‖ = 1) :
    ‖(c • (A + e • ContinuousLinearMap.adjoint A)) x‖ ≤ ‖A x‖ := by
  rw [ContinuousLinearMap.smul_apply, norm_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  have h1 : ‖A x + e • ContinuousLinearMap.adjoint A x‖ ≤ 2 * ‖A x‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, he, one_mul, hn]; linarith
  calc ‖c‖ * ‖A x + e • ContinuousLinearMap.adjoint A x‖ ≤ (1 / 2) * (2 * ‖A x‖) :=
        mul_le_mul hc h1 (norm_nonneg _) (by norm_num)
    _ = ‖A x‖ := by ring

variable (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
include hκ hN

theorem SN_commutes (z w : ℂ) :
    Commute (normalizedTransfer L κ N z) (normalizedTransfer L κ N w) ∧
    Commute (normalizedTransfer L κ N z) (ContinuousLinearMap.adjoint (normalizedTransfer L κ N w)) ∧
    Commute (ContinuousLinearMap.adjoint (normalizedTransfer L κ N z)) (normalizedTransfer L κ N w) ∧
    Commute (ContinuousLinearMap.adjoint (normalizedTransfer L κ N z))
      (ContinuousLinearMap.adjoint (normalizedTransfer L κ N w)) := by
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hN)
  have := transfer_normality L N hN (κ / N) hc z w
  simp only [normalizedTransfer_eq_transfer]
  exact this

theorem SN_isStarNormal (z : ℂ) : IsStarNormal (normalizedTransfer L κ N z) :=
  isStarNormal_of_commute (SN_commutes L κ hκ N hN z z).2.2.1

/-- **The commuting quadratures' joint functional calculus** `Φ_θ` of `S_N(z_θ)` on the disc of radius `R`. -/
def PhiFam {Θ : Type*} (z : Θ → ℂ) (R : ℝ) (hR : ∀ θ, ‖normalizedTransfer L κ N (z θ)‖ ≤ R) (θ : Θ) :
    C(Kdisc R, ℂ) →⋆ₐ[ℂ] (SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) :=
  quadHom (normalizedTransfer L κ N (z θ)) (SN_isStarNormal L κ hκ N hN (z θ)) R (hR θ)

variable {L κ N}

theorem PhiFam_hquad {Θ : Type*} (z : Θ → ℂ) (R : ℝ) (hR : ∀ θ, ‖normalizedTransfer L κ N (z θ)‖ ≤ R)
    (θ : Θ) (j : Fin 2) :
    ∃ α β : ℂ, ‖α‖ + ‖β‖ ≤ 1 ∧
      PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) j) =
        α • normalizedTransfer L κ N (z θ) +
          β • (normalizedTransfer L κ N (z θ)).adjoint :=
  quad_hquad _ _ R (hR θ) j

theorem PhiFam_hcomm {Θ : Type*} (z : Θ → ℂ) (R : ℝ) (hR : ∀ θ, ‖normalizedTransfer L κ N (z θ)‖ ≤ R)
    (θ θ' : Θ) (j j' : Fin 2) :
    Commute (PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) j))
      (PhiFam L κ hκ N hN z R hR θ' (coordC (d := 2) (K := Kdisc R) j')) := by
  obtain ⟨α, β, -, h1⟩ := PhiFam_hquad hκ hN z R hR θ j
  obtain ⟨α', β', -, h2⟩ := PhiFam_hquad hκ hN z R hR θ' j'
  rw [h1, h2]
  obtain ⟨c1, c2, c3, c4⟩ := SN_commutes L κ hκ N hN (z θ) (z θ')
  exact commute_lin _ _ c1 c2 c3 c4 α β α' β'

/-- **`hB`**: norm continuity of `θ ↦ Re/Im S_N(z_θ)` for continuous `z`, hence strong measurability on a compact
parameter space (PROP-014 `hB`). -/
theorem PhiFam_hB {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    [CompactSpace Θ] (ν : Measure Θ) (z : Θ → ℂ) (hz : Continuous z) (R : ℝ)
    (hR : ∀ θ, ‖normalizedTransfer L κ N (z θ)‖ ≤ R) (j : Fin 2) :
    AEStronglyMeasurable (fun θ => PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) j)) ν := by
  have hS : Continuous fun θ => normalizedTransfer L κ N (z θ) :=
    ((QuantumNLS.NormalityBridge.differentiable_normalizedTransfer (L := L) (κ := κ) (N := N)).continuous).comp hz
  have hSa : Continuous fun θ => ContinuousLinearMap.adjoint (normalizedTransfer L κ N (z θ)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := SymSector ℂ (L2T L) N)
      (F := SymSector ℂ (L2T L) N)).continuous.comp hS
  refine aestronglyMeasurable_coord_of_continuous ν (PhiFam L κ hκ N hN z R hR) j ?_
  fin_cases j
  · have : (fun θ => PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 0)) =
        fun θ => (1 / 2 : ℂ) • (normalizedTransfer L κ N (z θ) +
          ContinuousLinearMap.adjoint (normalizedTransfer L κ N (z θ))) :=
      funext fun θ => quadHom_coord0 _ _ R (hR θ)
    show Continuous fun θ => PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 0)
    rw [this]
    exact Continuous.const_smul (hS.add hSa) (1 / 2 : ℂ)
  · have : (fun θ => PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 1)) =
        fun θ => (-Complex.I / 2 : ℂ) • (normalizedTransfer L κ N (z θ) -
          ContinuousLinearMap.adjoint (normalizedTransfer L κ N (z θ))) :=
      funext fun θ => quadHom_coord1 _ _ R (hR θ)
    show Continuous fun θ => PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 1)
    rw [this]
    exact Continuous.const_smul (hS.sub hSa) (-Complex.I / 2 : ℂ)

/-- **The background identification `b_θ = s(z_θ)`**: for a complex number `s` (the background symbol `s(z)`), with
`b = ι(s) = (Re s, Im s)`, `‖(B_{θ,j} - b_j) φ‖ ≤ ‖(S_N(z_θ) - s) φ‖` for both quadratures (`S_N` is normal). -/
theorem PhiFam_deviation {Θ : Type*} (z : Θ → ℂ) (R : ℝ) (hR : ∀ θ, ‖normalizedTransfer L κ N (z θ)‖ ≤ R)
    (θ : Θ) (s : ℂ) (phi : SymSector ℂ (L2T L) N) (j : Fin 2) :
    ‖(PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) j) -
        ((isoR2 s j : ℝ) : ℂ) • (1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)) phi‖ ≤
      ‖(normalizedTransfer L κ N (z θ) -
        s • (1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N)) phi‖ := by
  set S := normalizedTransfer L κ N (z θ) with hS
  set A : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N := S - s • 1 with hA
  have hAd : ContinuousLinearMap.adjoint A = ContinuousLinearMap.adjoint S - (starRingEnd ℂ s) • 1 := by
    rw [hA, map_sub, map_smulₛₗ, ContinuousLinearMap.adjoint_one]
  have hAn : Commute (ContinuousLinearMap.adjoint A) A := by
    obtain ⟨-, -, c3, -⟩ := SN_commutes L κ hκ N hN (z θ) (z θ)
    rw [hAd, hA]
    exact (c3.sub_left (Commute.smul_left (Commute.one_left _) _)).sub_right
      ((Commute.smul_right (Commute.one_right _) _).sub_left
        (Commute.smul_left (Commute.smul_right (Commute.one_left _) _) _))
  have hn := norm_adjoint_apply_eq A hAn phi
  fin_cases j
  · have e : PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 0) -
        ((isoR2 s 0 : ℝ) : ℂ) • (1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) =
        (1 / 2 : ℂ) • (A + (1 : ℂ) • ContinuousLinearMap.adjoint A) := by
      rw [PhiFam, quadHom_coord0, isoR2_apply_zero, hAd, hA]
      have hre : ((s.re : ℝ) : ℂ) = (1 / 2) * (s + (starRingEnd ℂ) s) := by
        apply Complex.ext <;> simp <;> ring
      rw [hre]
      module
    show ‖(PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 0) -
        ((isoR2 s 0 : ℝ) : ℂ) • 1) phi‖ ≤ ‖A phi‖
    rw [e]
    exact norm_half_le A phi hn _ _ (by norm_num) (by simp)
  · have e : PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 1) -
        ((isoR2 s 1 : ℝ) : ℂ) • (1 : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) =
        (-Complex.I / 2 : ℂ) • (A + (-1 : ℂ) • ContinuousLinearMap.adjoint A) := by
      rw [PhiFam, quadHom_coord1, isoR2_apply_one, hAd, hA]
      have him : ((s.im : ℝ) : ℂ) = (-Complex.I / 2) * (s - (starRingEnd ℂ) s) := by
        apply Complex.ext <;> simp <;> ring
      rw [him]
      module
    show ‖(PhiFam L κ hκ N hN z R hR θ (coordC (d := 2) (K := Kdisc R) 1) -
        ((isoR2 s 1 : ℝ) : ℂ) • 1) phi‖ ≤ ‖A phi‖
    rw [e]
    exact norm_half_le A phi hn _ _ (by simp) (by simp)

end Family


/-! ### Identification of `F_θ(B_θ)`, `C_{0,N}` and `L_N` with `f_z(S_N(z))`, `Re ∮ …`, `eq:MP-L` -/

section Identification

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real part `Re A = (A + A^*)/2` of a bounded operator (the "Re" of `eq:MP-C0`, `eq:MP-L`). -/
def reOp (A : H →L[ℂ] H) : H →L[ℂ] H := (1 / 2 : ℂ) • (A + ContinuousLinearMap.adjoint A)

/-- The adjoint as a bounded conjugate-linear map. -/
def adjSL : (H →L[ℂ] H) →SL[starRingEnd ℂ] (H →L[ℂ] H) :=
  (ContinuousLinearMap.adjoint : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H)).toContinuousLinearEquiv.toContinuousLinearMap

theorem adjSL_apply (A : H →L[ℂ] H) : adjSL A = ContinuousLinearMap.adjoint A := rfl

/-- `∫ Re φ = Re ∫ φ` (the Bochner integral commutes with the real-linear continuous map `Re`). -/
theorem integral_reOp {X : Type*} [MeasurableSpace X] (μ : Measure X) {ph : X → (H →L[ℂ] H)}
    (hph : Integrable ph μ) : ∫ x, reOp (ph x) ∂μ = reOp (∫ x, ph x ∂μ) := by
  have hadj : ∫ x, ContinuousLinearMap.adjoint (ph x) ∂μ = ContinuousLinearMap.adjoint (∫ x, ph x ∂μ) :=
    ContinuousLinearMap.integral_comp_commSL (σ := starRingEnd ℂ) (fun r x => by simp) adjSL hph
  have hint : Integrable (fun x => ContinuousLinearMap.adjoint (ph x)) μ := adjSL.integrable_comp hph
  unfold reOp
  rw [integral_smul, integral_add hph hint, hadj]

/-- `resKd` of a globally continuous function is the restriction of its complex cast. -/
theorem resKd_eq_liftC {K : Set (EuclideanSpace ℝ (Fin 2))} [CompactSpace K]
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (hf : Continuous f) :
    resKd K f = liftC (K := K) (fun y => ((f y : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hf) := by
  ext x
  rw [resKd_apply hf.continuousOn]
  rfl

/-- The real function `F(x) = Re(u · g(x₀ + i x₁))` of the two quadratures (`F_θ` of `eq:MP-C0`). -/
def quadF (u : ℂ) (g : ℂ → ℂ) : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => (u * g (isoR2.symm x)).re

theorem continuous_quadF (u : ℂ) {g : ℂ → ℂ} (hg : Continuous g) : Continuous (quadF u g) :=
  Complex.continuous_re.comp (continuous_const.mul (hg.comp isoR2.symm.continuous))

/-- **`F_θ(B_θ) = Re (u f(S))`**: the functional calculus of the real function `Re(u g(x₀+ix₁))` of the two
commuting quadratures is the real part of `u · g(S)`, `g(S)` the CFC of the normal `S`. -/
theorem quadHom_quadF (T : H →L[ℂ] H) (hT : IsStarNormal T) (R : ℝ) (hR : ‖T‖ ≤ R) (u : ℂ) {g : ℂ → ℂ}
    (hg : Continuous g) :
    quadHom T hT R hR (resKd (Kdisc R) (quadF u g)) = reOp (u • cfc g T) := by
  rw [resKd_eq_liftC _ (continuous_quadF u hg), quadHom_liftC]
  have e : (fun ζ : ℂ => (((quadF u g (isoR2 ζ) : ℝ)) : ℂ)) =
      fun ζ => (1 / 2 : ℂ) * ((u * g ζ) + star (u * g ζ)) := by
    funext ζ
    simp only [quadF, LinearIsometryEquiv.symm_apply_apply]
    rw [Complex.re_eq_add_conj]
    simp only [Complex.star_def]
    ring
  rw [e]
  have h1 : ContinuousOn (fun ζ : ℂ => u * g ζ) (spectrum ℂ T) := (continuous_const.mul hg).continuousOn
  have h2 : ContinuousOn (fun ζ : ℂ => star (u * g ζ)) (spectrum ℂ T) :=
    (continuous_star.comp (continuous_const.mul hg)).continuousOn
  have h3 : ContinuousOn (fun ζ : ℂ => (u * g ζ) + star (u * g ζ)) (spectrum ℂ T) := h1.add h2
  have hc1 : cfc (fun ζ : ℂ => (1 / 2 : ℂ) * ((u * g ζ) + star (u * g ζ))) T =
      (1 / 2 : ℂ) • cfc (fun ζ : ℂ => (u * g ζ) + star (u * g ζ)) T := cfc_const_mul (1 / 2 : ℂ) _ T h3
  have hc2 : cfc (fun ζ : ℂ => (u * g ζ) + star (u * g ζ)) T =
      cfc (fun ζ : ℂ => u * g ζ) T + cfc (fun ζ : ℂ => star (u * g ζ)) T :=
    cfc_add (hf := h1) (hg := h2)
  have hc3 : cfc (fun ζ : ℂ => u * g ζ) T = u • cfc g T :=
    cfc_const_mul u g T hg.continuousOn
  have hc4 : cfc (fun ζ : ℂ => star (u * g ζ)) T = star (cfc (fun ζ : ℂ => u * g ζ) T) :=
    cfc_star (fun ζ : ℂ => u * g ζ) T
  rw [hc1, hc2, hc4, hc3]
  unfold reOp
  rw [ContinuousLinearMap.star_eq_adjoint]

/-- The derivative of `F` at `b = ι(s)` in the coordinate directions: `∂_0F = Re(u g')`, `∂_1F = -Im(u g')`. -/
theorem fderiv_quadF (u : ℂ) {g : ℂ → ℂ} {g' s : ℂ} (hg : HasDerivAt g g' s) (j : Fin 2) :
    fderiv ℝ (quadF u g) (isoR2 s) (EuclideanSpace.single j 1) =
      (u * g' * isoR2.symm (EuclideanSpace.single j 1)).re := by
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => isoR2.symm x)
      (isoR2.symm.toContinuousLinearEquiv.toContinuousLinearMap) (isoR2 s) :=
    isoR2.symm.toContinuousLinearEquiv.hasFDerivAt
  have hs : isoR2.symm (isoR2 s) = s := LinearIsometryEquiv.symm_apply_apply _ _
  have h2 : HasFDerivAt g ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) g').restrictScalars ℝ)
      (isoR2.symm (isoR2 s)) := by
    rw [hs]; exact hg.hasFDerivAt.restrictScalars ℝ
  have h3 := h2.comp (isoR2 s) h1
  have h4 := h3.const_mul u
  have h5 := Complex.reCLM.hasFDerivAt.comp (isoR2 s) h4
  have h6 : HasFDerivAt (quadF u g) _ (isoR2 s) := h5
  rw [h6.fderiv]
  simp
  ring

theorem quadHom_linOp (T : H →L[ℂ] H) (hT : IsStarNormal T) (R : ℝ) (hR : ‖T‖ ≤ R) (u : ℂ) {g : ℂ → ℂ}
    {g' s : ℂ} (hg : HasDerivAt g g' s) :
    LinOp (quadHom T hT R hR) (quadF u g) (isoR2 s) = reOp ((u * g') • T) := by
  unfold LinOp
  rw [Fin.sum_univ_two, fderiv_quadF u hg 0, fderiv_quadF u hg 1]
  have e0 : isoR2.symm (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = 1 := by
    simp [isoR2, Complex.orthonormalBasisOneI_repr_symm_apply, EuclideanSpace.single_apply]
  have e1 : isoR2.symm (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = Complex.I := by
    simp [isoR2, Complex.orthonormalBasisOneI_repr_symm_apply, EuclideanSpace.single_apply]
  rw [e0, e1]
  have hc0 := quadHom_coord0 T hT R hR
  have hc1 := quadHom_coord1 T hT R hR
  rw [show ((0 : Fin 2)) = (0 : Fin 2) from rfl] at hc0
  rw [hc0, hc1]
  unfold reOp
  set c := u * g' with hc
  have hre : (((c * 1).re : ℝ) : ℂ) * (1 / 2) = (c + (starRingEnd ℂ) c) / 4 := by
    apply Complex.ext <;> simp <;> ring
  have hk : (((c * Complex.I).re : ℝ) : ℂ) * (-Complex.I / 2) = (c - (starRingEnd ℂ) c) / 4 := by
    apply Complex.ext <;> simp <;> ring
  rw [smul_smul, smul_smul, hre, hk, map_smulₛₗ]
  module

end Identification


/-! ### The identifications with `eq:MP-C0` and `eq:MP-L` (generic Hilbert space; apply with `H = Sym^N`) -/

section Identify2

open MeasureTheory QuantumNLS.FunctionalLinearization QuantumNLS.MixedTraceNorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Θ : Type*} [MeasurableSpace Θ]

/-- **`eq:MP-C0` identified.**  For a family of normal operators `S_θ` (e.g. `S_N(z_θ)`, `H = Sym^N`) with
`‖S_θ‖ ≤ R`, `Φ_θ = quadHom S_θ` and `F_θ(x) = Re(u_θ g_θ(x₀ + i x₁))` (`g_θ = f_{z_θ}` the bounded smooth extension of the
chart `λ(z_θ,·)`, `u_θ` the complex weight `-p_t(z)·(dz/dθ)·θ_n/(2πκ)` absorbing the contour data):
`C_{0,N} = ∫ F_θ(B_θ) dν = Re ∫ u_θ f_{z_θ}(S_θ) dν(θ)`. -/
theorem C0N_eq_reOp (ν : Measure Θ) (R : ℝ) (S : Θ → H →L[ℂ] H) (hS : ∀ θ, IsStarNormal (S θ))
    (hR : ∀ θ, ‖S θ‖ ≤ R) (u : Θ → ℂ) (g : Θ → ℂ → ℂ) (hg : ∀ θ, Continuous (g θ))
    (hint : Integrable (fun θ => u θ • cfc (g θ) (S θ)) ν) :
    C0N ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) (fun θ => quadF (u θ) (g θ)) =
      reOp (∫ θ, u θ • cfc (g θ) (S θ) ∂ν) := by
  unfold C0N
  have : ∀ θ, quadHom (S θ) (hS θ) R (hR θ) (resKd (Kdisc R) (quadF (u θ) (g θ))) =
      reOp (u θ • cfc (g θ) (S θ)) := fun θ => quadHom_quadF _ _ _ _ (u θ) (hg θ)
  simp_rw [this]
  exact integral_reOp ν hint

/-- **`eq:MP-L` identified.**  With `b_θ = ι(s_θ)` (`s_θ = s(z_θ)`, the background symbol) and `g_θ` complex
differentiable at `s_θ` with derivative `g_θ'`, `L_N = ∫ ∑_j ∂_jF_θ(b_θ) B_{θ,j} dν = Re ∫ u_θ g_θ'(s_θ) S_θ dν(θ)`. -/
theorem LN_eq_reOp (ν : Measure Θ) (R : ℝ) (S : Θ → H →L[ℂ] H) (hS : ∀ θ, IsStarNormal (S θ))
    (hR : ∀ θ, ‖S θ‖ ≤ R) (u : Θ → ℂ) (g : Θ → ℂ → ℂ) (g' s : Θ → ℂ)
    (hg : ∀ θ, HasDerivAt (g θ) (g' θ) (s θ))
    (hint : Integrable (fun θ => (u θ * g' θ) • S θ) ν) :
    LN ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) (fun θ => quadF (u θ) (g θ)) (fun θ => isoR2 (s θ)) =
      reOp (∫ θ, (u θ * g' θ) • S θ ∂ν) := by
  unfold LN
  have : ∀ θ, LinOp (quadHom (S θ) (hS θ) R (hR θ)) (quadF (u θ) (g θ)) (isoR2 (s θ)) =
      reOp ((u θ * g' θ) • S θ) := fun θ => quadHom_linOp _ _ _ _ (u θ) (hg θ)
  simp_rw [this]
  exact integral_reOp ν hint

/-- **The chart normalization in `L_N`**: if `g_θ` coincides near `s_θ` with the chart `λ(z,·) = chartLambda` of
`eq:MP-chart` (`g_θ` is a bounded smooth extension of it; `D, A, c0` the background data), then `g_θ'(s_θ) = D(z_θ)^{-1}`
(`MixedTraceNorm.hasDerivAt_chartLambda`) and `L_N = Re ∫ u_θ D(z_θ)^{-1} S_θ dν(θ)`, the printed `eq:MP-L`. -/
theorem LN_eq_chart (ν : Measure Θ) (R : ℝ) (S : Θ → H →L[ℂ] H) (hS : ∀ θ, IsStarNormal (S θ))
    (hR : ∀ θ, ‖S θ‖ ≤ R) (u : Θ → ℂ) (g : Θ → ℂ → ℂ) (s D A c0 : Θ → ℂ) (hD : ∀ θ, D θ ≠ 0)
    (hsD : ∀ θ, s θ + D θ ≠ 0) (hA : ∀ θ, A θ = (s θ + D θ) / 2)
    (hgc : ∀ θ, g θ =ᶠ[nhds (s θ)] chartLambda (c0 θ) (D θ) (s θ) (A θ))
    (hint : Integrable (fun θ => (u θ * (D θ)⁻¹) • S θ) ν) :
    LN ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) (fun θ => quadF (u θ) (g θ)) (fun θ => isoR2 (s θ)) =
      reOp (∫ θ, (u θ * (D θ)⁻¹) • S θ ∂ν) := by
  refine LN_eq_reOp ν R S hS hR u g (fun θ => (D θ)⁻¹) s (fun θ => ?_) hint
  exact (hasDerivAt_chartLambda (c0 θ) (hD θ) (hsD θ) (hA θ)).congr_of_eventuallyEq (hgc θ)

end Identify2

/-! ### The final PROP-026 statement for the physical family -/

section Final

open MeasureTheory QuantumNLS.FunctionalLinearization

variable (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
include hκ hN

/-- `Φ_θ` on the disc `K_{Rbd}` for the strip `|Im z| ≤ h` (the uniform spectral bound of the kernel estimate). -/
def PhiFam' {Θ : Type*} (z : Θ → ℂ) (h : ℝ) (hzh : ∀ θ, |(z θ).im| ≤ h) (θ : Θ) :
    C(Kdisc (Rbd L κ h), ℂ) →⋆ₐ[ℂ] (SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) :=
  PhiFam L κ hκ N hN z (Rbd L κ h) (fun θ => norm_normalizedTransfer_le L κ N (z θ) h (hzh θ)) θ

/-- `PhiFam'` is the joint functional calculus `quadHom` of `S_N(z_θ)`. -/
theorem PhiFam'_eq {Θ : Type*} (z : Θ → ℂ) (h : ℝ) (hzh : ∀ θ, |(z θ).im| ≤ h) (θ : Θ) :
    PhiFam' L κ hκ N hN z h hzh θ =
      quadHom (normalizedTransfer L κ N (z θ)) (SN_isStarNormal L κ hκ N hN (z θ)) (Rbd L κ h)
        (norm_normalizedTransfer_le L κ N (z θ) h (hzh θ)) := rfl

omit hκ hN

end Final

section Final2

open MeasureTheory QuantumNLS.FunctionalLinearization

set_option maxHeartbeats 4000000 in
/-- **PROP-026 `lem:MP-linearization` (trace-norm form) for the PHYSICAL family, with `hquad`, `hcomm` and `hB`
DISCHARGED.**  Here `Φ_θ = PhiFam'` is the joint functional calculus of the commuting quadratures `Re S_N(z_θ)`,
`Im S_N(z_θ)` of the realized DEF-048 transfer `S_N = normalizedTransfer` (`N = k+q`, `κ > 0`), `z : Θ → ℂ` continuous
on a compact parameter space with values in the strip `|Im z| ≤ h` (so `‖S_N(z_θ)‖ ≤ Rbd`), and `b_θ = ι(s_θ)`
with `s_θ` the background symbol value (`s(z_θ)`).  The deviation hypothesis is the source's
`‖(S_N(z_θ) - s_θ) φ‖ ≤ δ(θ)` (`eq:MP-fixed-deviation` / `eq:MP-growing-deviation` on `ran P_N`); it gives
`‖(B_{θ,j} - b_{θ,j})φ‖ ≤ δ(θ)` for both quadratures (`PhiFam_deviation`, `S_N` normal).  The weights `F_θ`
(absorbing `p_t(z)`, `dz`, `θ_n`, `-1/(2πκ)` and the extensions `f_z`), `w`, `δ` remain explicit parameters.
The PROP-014 operator-norm Bochner formulation is inherited as the owner-accepted convention of
`MixedTraceNorm`/`KernelFactorialBound` (NOT re-proved). -/
theorem prop026_traceNorm_physical :
    ∃ (m : ℕ) (C0 : ℝ), 1 ≤ m ∧ 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin 2))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ] [CompactSpace Θ]
        (ν : Measure Θ) [IsFiniteMeasure ν]
        (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (k q : ℕ) (hN : 1 ≤ k + q)
        (z : Θ → ℂ) (hz : Continuous z) (h : ℝ) (hzh : ∀ θ, |(z θ).im| ≤ h)
        (hKQ : Kdisc (Rbd L κ h) ⊆ Q)
        (s : Θ → ℂ) (hsQ : ∀ θ, isoR2 (s θ) ∈ Q)
        (F : Θ → EuclideanSpace ℝ (Fin 2) → ℝ) (hF : ∀ θ, ContDiffOn ℝ ∞ (F θ) U)
        (hFm : AEStronglyMeasurable (fun θ => resKd (Kdisc (Rbd L κ h)) (F θ)) ν)
        (hdF : ∀ j, AEStronglyMeasurable
          (fun θ => fderiv ℝ (F θ) (isoR2 (s θ)) (EuclideanSpace.single j 1)) ν)
        (phi : SymSector ℂ (L2T L) (k + q)) (hphi : ‖phi‖ = 1)
        (δ : Θ → ℝ) (hδ : ∀ θ, 0 ≤ δ θ)
        (hsδ : ∀ θ, ‖(normalizedTransfer L κ (k + q) (z θ) -
          s θ • (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤ δ θ)
        (w : Θ → ℝ) (hw0 : ∀ θ, 0 ≤ w θ) (hw : Integrable w ν)
        (hwδ : Integrable (fun θ => w θ * δ θ) ν)
        {M0 : ℝ} (hM0 : 0 ≤ M0)
        (hFb : ∀ θ, ∀ i ≤ m, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ w θ * M0),
        QuantumNLS.TraceClass.traceNorm
          (reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) • C0N ν (PhiFam' L κ hκ (k + q) hN z h hzh) F) 1 phi :
                SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
            reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) • LN ν (PhiFam' L κ hκ (k + q) hN z h hzh) F
                (fun θ => isoR2 (s θ))) 1 phi : SymSector ℂ (L2T L) (k + q)) :
                HilbertTensorPower ℂ (L2T L) (k + q))) ≤
          ENNReal.ofReal ((C0 * (C1 * M0)) * (∫ θ, w θ * δ θ ∂ν) *
            (Real.exp (L * h) * (2 * k * (2 * Real.exp (L * h) *
              ((|κ| * L) * Real.exp (|κ| * L)))))) := by
  obtain ⟨m, C0, hm, hC0, hmain⟩ := QuantumNLS.KernelFactorialBound.prop026_traceNorm_transfer_sharp 2
  refine ⟨m, C0, hm, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨C1, hC1, hC1b⟩ := hmain hU hQ hQU
  refine ⟨C1, hC1, fun {Θ} _ _ _ _ ν _ L _ κ hκ k q hN z hz h hzh hKQ s hsQ F hF hFm hdF phi hphi δ hδ hsδ
    w hw0 hw hwδ {M0} hM0 hFb => ?_⟩
  have hR : ∀ θ, ‖normalizedTransfer L κ (k + q) (z θ)‖ ≤ Rbd L κ h := fun θ =>
    norm_normalizedTransfer_le L κ (k + q) (z θ) h (hzh θ)
  refine hC1b ν L κ k q hN (PhiFam' L κ hκ (k + q) hN z h hzh) F hF (fun θ => isoR2 (s θ)) hKQ hsQ
    (fun θ θ' j j' => PhiFam_hcomm hκ hN z (Rbd L κ h) hR θ θ' j j')
    (fun j => PhiFam_hB hκ hN ν z hz (Rbd L κ h) hR j) hFm hdF phi hphi δ hδ
    (fun θ j => (PhiFam_deviation hκ hN z (Rbd L κ h) hR θ (s θ) phi j).trans (hsδ θ)) z h hzh
    (fun θ j => PhiFam_hquad hκ hN z (Rbd L κ h) hR θ j) w hw0 hw hwδ hM0 hFb


end Final2

/-! ### Measurability hypotheses `hFm`, `hdF` from continuity -/

section Meas

open MeasureTheory QuantumNLS.FunctionalLinearization

variable {d : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]

/-- `hdF` holds as soon as the directional derivatives `∂_jF_θ(b_θ)` are continuous in `θ`. -/
theorem hdF_of_continuous (ν : Measure Θ) (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ)
    (b : Θ → EuclideanSpace ℝ (Fin d))
    (hcont : ∀ j, Continuous fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) :
    ∀ j, AEStronglyMeasurable (fun θ => fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1)) ν :=
  fun j => (hcont j).aestronglyMeasurable

/-- `hFm` holds on a compact parameter space if `(θ, x) ↦ F_θ(x)` is jointly continuous. -/
theorem hFm_of_continuous [CompactSpace Θ] (ν : Measure Θ) (K : Set (EuclideanSpace ℝ (Fin d)))
    [CompactSpace K] (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : Continuous fun p : Θ × EuclideanSpace ℝ (Fin d) => F p.1 p.2) :
    AEStronglyMeasurable (fun θ => resKd K (F θ)) ν := by
  let G : C(Θ × K, ℂ) := ⟨fun p => ((F p.1 p.2.1 : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  have hcont : Continuous fun θ => resKd K (F θ) := by
    have h : (fun θ => resKd K (F θ)) = fun θ => G.curry θ := by
      funext θ
      have hθ : Continuous (F θ) := hF.comp (continuous_const.prodMk continuous_id)
      ext x
      rw [resKd_apply hθ.continuousOn]
      rfl
    rw [h]
    exact G.curry.continuous
  borelize C(K, ℂ)
  exact (stronglyMeasurable_iff_measurable_separable.2
    ⟨hcont.measurable, (isCompact_range hcont).isSeparable⟩).aestronglyMeasurable

end Meas

#print axioms quad_hquad
#print axioms norm_normalizedTransfer_le
#print axioms PhiFam_hquad
#print axioms PhiFam_hcomm
#print axioms PhiFam_hB
#print axioms PhiFam_deviation
#print axioms quadHom_quadF
#print axioms quadHom_linOp
#print axioms C0N_eq_reOp
#print axioms LN_eq_reOp
#print axioms LN_eq_chart
#print axioms prop026_traceNorm_physical
#print axioms hFm_of_continuous

end QuantumNLS.MixedQuadratures
