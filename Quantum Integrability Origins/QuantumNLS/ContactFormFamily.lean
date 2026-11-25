import QuantumNLS.ContactFormTheorem
import QuantumNLS.ContactOperator
import QuantumNLS.CollisionIdentification

/-!
# R-81E86877 `basis:lem:forms` (periodic_basis.tex:84-110), form family `H(c)`, `c ≥ 0`

Source (PR11 `3b1f701a`): `h_c[ψ] = Σ_j‖∂_jψ‖² + 2c Σ_{j<k} b_{jk}[ψ]`, `Dom(h_c) = H¹_sym(𝕋_L^N)`
(`basis:eq:form`), `b_{jk}[ψ]` = the integral of `|ψ|²` over `x_j = x_k` with respect to the
remaining `N-1` independent torus coordinates.

**Identification with DEF-005.** `b_{jk}` is the squared norm `∫ |T_{jk}ψ|² dy_{jk}` of the
frozen product trace on the coordinate measure `dyij` (common coordinate × the other `N-2` circles
= `N-1` independent coordinates, Lebesgue, no `√2`): `bform`, `bform_eq_integral`,
`q_self_eq_bform` (`q_{N,c}[ψ] = Σ_j‖∂_jψ‖² + 2cΣ_{j<k} b_{jk}[ψ]`, with the weak partials of
`CollisionIdentification`) and `bform_smooth` (`b_{jk}[φ] = ∫|φ(x_j=x_k=t, y)|²` for smooth `φ`).
So `basis:eq:form` is exactly the form of `ContactForm`/`ContactOperator` (same `2c`, same
coordinate measure); nothing is assumed.

Imports (read-only): `ContactFormTheorem`, `ContactOperator`, `CollisionIdentification`.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory QuantumNLS.Energy QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor
  QuantumNLS.CollisionTrace QuantumNLS.ProductWeakDerivatives QuantumNLS.Fourier
  QuantumNLS.ContactForm QuantumNLS.ContactOperator QuantumNLS.CollisionIdentification
  QuantumNLS.ContactDistributionFull QuantumNLS.ContactFormTheorem

namespace QuantumNLS.ContactFormFamily

section Identification
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `b_{jk}[ψ] = ∫ |T_{jk}ψ|² dy_{jk}`: the squared `L²(dy_{jk})` norm of the trace. -/
def bform (p : Pair N) (ψ : PhysH1 L N) : ℝ :=
  ∫ y, ‖(productTrace (L := L) p.1.1 p.1.2 (ne_of_lt p.2) ψ :
      (AddCircle L × (Rest N p.1.1 p.1.2 → AddCircle L)) → ℂ) y‖ ^ 2
    ∂(dyij (L := L) p.1.1 p.1.2)

theorem integral_norm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : Lp ℂ 2 μ) :
    ∫ y, ‖(g : α → ℂ) y‖ ^ 2 ∂μ = ‖g‖ ^ 2 := by
  have h1 : ⟪g, g⟫_ℂ = ((∫ y, ‖(g : α → ℂ) y‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [inner_self_eq_norm_sq_to_K]
  have h2 : ⟪g, g⟫_ℂ = ((‖g‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  exact_mod_cast h1.symm.trans h2

theorem bform_eq_norm_sq (p : Pair N) (ψ : PhysH1 L N) :
    bform p ψ = ‖productTrace (L := L) p.1.1 p.1.2 (ne_of_lt p.2) ψ‖ ^ 2 :=
  integral_norm_sq_eq _

theorem bform_eq_integral (p : Pair N) (ψ : PhysH1 L N) :
    bform p ψ = ∫ y, ‖(productTrace (L := L) p.1.1 p.1.2 (ne_of_lt p.2) ψ :
      (AddCircle L × (Rest N p.1.1 p.1.2 → AddCircle L)) → ℂ) y‖ ^ 2
      ∂((volume : Measure (AddCircle L)).prod
        (Measure.pi fun _ : Rest N p.1.1 p.1.2 => (volume : Measure (AddCircle L)))) := rfl

theorem bform_nonneg (p : Pair N) (ψ : PhysH1 L N) : 0 ≤ bform p ψ := by
  rw [bform_eq_norm_sq]; positivity

/-- For a smooth lattice-periodic `φ`, `b_{jk}[φ]` is the literal integral of `|φ|²` over `x_j=x_k`. -/
theorem bform_smooth (p : Pair N) {φ : (Fin N → ℝ) → ℂ} (hφ : IsTorusTest L φ) :
    bform p (smoothH1 hφ) = ∫ y, ‖liftK (L := L) φ
      (diagPoint p.1.1 p.1.2 y.1 y.2)‖ ^ 2 ∂(dyij (L := L) p.1.1 p.1.2) := by
  unfold bform
  refine integral_congr_ae ?_
  filter_upwards [productTrace_smooth (L := L) p.1.1 p.1.2 (ne_of_lt p.2) hφ] with y hy
  rw [hy]

/-- **`basis:eq:form` = DEF-005**: `q_{N,c}[ψ] = Σ_j‖∂_jψ‖² + 2c Σ_{j<k} b_{jk}[ψ]`, with the weak
partial derivatives `gradientCLM j ψ` and the exact coefficient `2c`. -/
theorem q_self_eq_bform (c : ℝ) (ψ : PhysH1 L N) :
    q c ψ ψ = ((∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 + 2 * c * ∑ p : Pair N, bform p ψ : ℝ) : ℂ) := by
  rw [q_eq_physical_pairings]
  have hp : ∀ p : Pair N, ⟪productTrace (L := L) p.1.1 p.1.2 (ne_of_lt p.2) ψ,
      productTrace (L := L) p.1.1 p.1.2 (ne_of_lt p.2) ψ⟫_ℂ = ((bform p ψ : ℝ) : ℂ) := fun p => by
    rw [bform_eq_norm_sq, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hk : ∀ j : Fin N, ⟪gradientCLM j ψ, gradientCLM j ψ⟫_ℂ = ((‖gradientCLM j ψ‖ ^ 2 : ℝ) : ℂ) :=
    fun j => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [hp, hk]
  push_cast
  rfl

/-- **The printed trace estimate integrated over the other coordinates:** for every `ε > 0` there
is `C` (depending on `ε, N, L`) with `Σ_{j<k} b_{jk}[ψ] ≤ ε Σ_j‖∂_jψ‖² + C‖ψ‖²`, via the accepted
real-space trace estimate `productTrace_estimate_realspace` (R-C21B75F5). -/
theorem sum_bform_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : PhysH1 L N,
      ∑ p : Pair N, bform p ψ ≤ ε * ∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 + C * ‖ψ.val‖ ^ 2 := by
  have hL : 0 < L := Fact.out
  set n : ℝ := ((Fintype.card (Pair N) : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set ε' : ℝ := ε / (n + 1) with hε'
  have hε'0 : 0 < ε' := div_pos hε (by linarith)
  refine ⟨n * (L⁻¹ + ε'⁻¹), by positivity, fun ψ => ?_⟩
  have hp : ∀ p : Pair N, bform p ψ ≤ ε' * ‖gradientCLM p.1.1 ψ‖ ^ 2 + (L⁻¹ + ε'⁻¹) * ‖ψ.val‖ ^ 2 :=
    fun p => by
      rw [bform_eq_norm_sq]
      exact productTrace_estimate_realspace p.1.1 p.1.2 (ne_of_lt p.2) hε'0 ψ _
        (gradientCLM_hasWeakPartial p.1.1 ψ)
  have hk : ∀ p : Pair N, ‖gradientCLM p.1.1 ψ‖ ^ 2 ≤ ∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 :=
    fun p => Finset.single_le_sum (f := fun j : Fin N => ‖gradientCLM j ψ‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ p.1.1)
  calc ∑ p : Pair N, bform p ψ
      ≤ ∑ p : Pair N, (ε' * ∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 + (L⁻¹ + ε'⁻¹) * ‖ψ.val‖ ^ 2) :=
        Finset.sum_le_sum fun p _ => (hp p).trans (by
          have := mul_le_mul_of_nonneg_left (hk p) hε'0.le
          linarith)
    _ = n * (ε' * ∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2) + n * ((L⁻¹ + ε'⁻¹) * ‖ψ.val‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]; ring
    _ ≤ ε * ∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 + n * (L⁻¹ + ε'⁻¹) * ‖ψ.val‖ ^ 2 := by
        have hs : 0 ≤ ∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 :=
          Finset.sum_nonneg fun j _ => sq_nonneg _
        have h1 : n * ε' ≤ ε := by
          rw [hε']
          rw [mul_div_assoc', div_le_iff₀ (by linarith)]
          nlinarith
        have := mul_le_mul_of_nonneg_right h1 hs
        nlinarith

end Identification


section Family
variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem re_Bform_self (c : ℝ) (ψ : VSym L N) : (Bform c ψ ψ).re = formNormSq c ψ.1 := by
  unfold Bform formNormSq
  rw [Complex.add_re]
  congr 1
  have := inner_self_eq_norm_sq (𝕜 := ℂ) ψ.1.val
  simpa using this

/-- **Form order**: `q_{N,c}[ψ] ≤ q_{N,c'}[ψ]` for `0 ≤ c ≤ c'` (same form domain `H¹_sym`). -/
theorem q_mono {c c' : ℝ} (h : c ≤ c') (ψ : PhysH1 L N) : (q c ψ ψ).re ≤ (q c' ψ ψ).re := by
  have h1 := formNormSq_eq c ψ
  have h2 := formNormSq_eq c' ψ
  have hs : 0 ≤ ∑ p : Pair N, ‖Tpair p ψ‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  unfold formNormSq at h1 h2
  nlinarith [mul_nonneg (sub_nonneg.2 h) hs]

theorem Bform_mono {c c' : ℝ} (h : c ≤ c') (ψ : VSym L N) :
    (Bform c ψ ψ).re ≤ (Bform c' ψ ψ).re := by
  rw [re_Bform_self, re_Bform_self]
  unfold formNormSq
  have := q_mono h ψ.1
  linarith

/-- **The resolvents decrease in `c`**: `(H(c')+1)⁻¹ ≤ (H(c)+1)⁻¹` in the form (Loewner) order. -/
theorem Rop_antitone {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (h : c ≤ c') (f : SymL2 L N) :
    (⟪Rop c' hc' f, f⟫_ℂ).re ≤ (⟪Rop c hc f, f⟫_ℂ).re := by
  set u : VSym L N := psi c hc f with hu
  set u' : VSym L N := psi c' hc' f with hu'
  have ha : ⟪Rop c hc f, f⟫_ℂ = Bform c u u := (resolvent_eq hc f u).symm
  have ha' : ⟪Rop c' hc' f, f⟫_ℂ = Bform c' u' u' := (resolvent_eq hc' f u').symm
  have hmix : Bform c u' u = ⟪Rop c' hc' f, f⟫_ℂ := resolvent_eq hc f u'
  have hexp : Bform c (u' - u) (u' - u) =
      Bform c u' u' - Bform c u' u - Bform c u u' + Bform c u u := by
    have h1 : Bform c (u' - u) (u' - u) = BformCLM c hc (u' - u) (u' - u) := rfl
    rw [h1]
    simp only [map_sub, sub_apply, BformCLM_apply]
    ring
  have hconj : Bform c u u' = conj (Bform c u' u) := (Bform_conj_symm c u' u).symm
  have hnn : 0 ≤ (Bform c (u' - u) (u' - u)).re := by
    rw [re_Bform_self]
    exact (sq_nonneg _).trans (H1_le_formNormSq hc _)
  rw [hexp, hconj, hmix] at hnn
  simp only [Complex.add_re, Complex.sub_re, Complex.conj_re] at hnn
  have hm := Bform_mono h u'
  rw [← ha'] at hm
  rw [ha]
  linarith


/-- The contact-sum bound from the accepted trace estimate (`norm_Tpair_le`). -/
theorem norm_contactSum_le (φ ψ : PhysH1 L N) :
    ‖contactSum φ ψ‖ ≤ Fintype.card (Pair N) * (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := by
  have hL : 0 < L := Fact.out
  unfold contactSum
  calc ‖∑ p : Pair N, ⟪Tpair p φ, Tpair p ψ⟫_ℂ‖
      ≤ ∑ p : Pair N, ‖⟪Tpair p φ, Tpair p ψ⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ _p : Pair N, (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := Finset.sum_le_sum fun p _ =>
        (norm_inner_le_norm _ _).trans (by
          have h1 := norm_Tpair_le p φ
          have h2 := norm_Tpair_le p ψ
          calc ‖Tpair p φ‖ * ‖Tpair p ψ‖ ≤ ((1 + L⁻¹) * ‖φ‖) * ((1 + L⁻¹) * ‖ψ‖) :=
                mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            _ = (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := by ring)
    _ = Fintype.card (Pair N) * (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem Bform_contact_shift (c b : ℝ) (w x : VSym L N) :
    Bform c w x = Bform b w x + ((2 * (c - b) : ℝ) : ℂ) * contactSum w.1 x.1 := by
  unfold Bform q
  push_cast
  ring

theorem le_of_sq_le_mul {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ a * b) : a ≤ b := by
  by_contra hlt
  have hlt := not_le.1 hlt
  nlinarith

theorem norm_valSym_le (x : VSym L N) : ‖(valSym x : SymL2 L N)‖ ≤ ‖x‖ :=
  PhysH1.norm_val_le x.1

/-- The `H¹` norm of the variational resolvent is bounded by `‖f‖₂` (source: "testing against `u_c`"). -/
theorem norm_psi_le {c : ℝ} (hc : 0 ≤ c) (f : SymL2 L N) : ‖psi c hc f‖ ≤ ‖f‖ := by
  set u : VSym L N := psi c hc f with hu
  have h1 : ‖u‖ ^ 2 ≤ (Bform c u u).re := by
    rw [re_Bform_self]; exact H1_le_formNormSq hc _
  have h2 : Bform c u u = ⟪(valSym u : SymL2 L N), f⟫_ℂ := resolvent_eq hc f u
  have h3 : (Bform c u u).re ≤ ‖u‖ * ‖f‖ := by
    rw [h2]
    exact (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_valSym_le u) (norm_nonneg _)))
  exact le_of_sq_le_mul (norm_nonneg _) (h1.trans h3)

/-- The Lipschitz constant `2·#{j<k}·(1+L⁻¹)²`, depending only on `N` and `L`. -/
def lipConst (L : ℝ) (N : ℕ) : ℝ := 2 * Fintype.card (Pair N) * (1 + L⁻¹) ^ 2

omit [Fact (0 < L)] in
theorem lipConst_nonneg : 0 ≤ lipConst L N := by
  unfold lipConst; positivity

/-- **Global Lipschitz estimate** `‖(H(c)+1)⁻¹f − (H(b)+1)⁻¹f‖ ≤ K_{N,L}|c−b|‖f‖`. -/
theorem Rop_lipschitz_apply {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) (f : SymL2 L N) :
    ‖Rop c hc f - Rop b hb f‖ ≤ lipConst L N * |c - b| * ‖f‖ := by
  set v : VSym L N := psi c hc f - psi b hb f with hv
  have hkey : Bform c v v = -(((2 * (c - b) : ℝ) : ℂ) * contactSum v.1 (psi b hb f).1) := by
    have e1 : Bform c v (psi c hc f) = ⟪(valSym v : SymL2 L N), f⟫_ℂ := resolvent_eq hc f v
    have e2 : Bform b v (psi b hb f) = ⟪(valSym v : SymL2 L N), f⟫_ℂ := resolvent_eq hb f v
    have e3 := Bform_contact_shift c b v (psi b hb f)
    have e4 : Bform c v v = Bform c v (psi c hc f) - Bform c v (psi b hb f) := by
      exact map_sub (BformCLM c hc v) (psi c hc f) (psi b hb f)
    rw [e4, e1, e3, e2]
    ring
  have hlow : ‖v‖ ^ 2 ≤ (Bform c v v).re := by
    rw [re_Bform_self]; exact H1_le_formNormSq hc _
  have hup : (Bform c v v).re ≤ lipConst L N * |c - b| * (‖v‖ * ‖f‖) := by
    calc (Bform c v v).re ≤ ‖Bform c v v‖ := Complex.re_le_norm _
      _ = |2 * (c - b)| * ‖contactSum v.1 (psi b hb f).1‖ := by
          rw [hkey, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |2 * (c - b)| * (Fintype.card (Pair N) * (1 + L⁻¹) ^ 2 * (‖v‖ * ‖psi b hb f‖)) :=
          mul_le_mul_of_nonneg_left (norm_contactSum_le _ _) (abs_nonneg _)
      _ ≤ |2 * (c - b)| * (Fintype.card (Pair N) * (1 + L⁻¹) ^ 2 * (‖v‖ * ‖f‖)) := by
          have hL : 0 < L := Fact.out
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_psi_le hb f) (norm_nonneg _)) (by positivity))
            (abs_nonneg _)
      _ = lipConst L N * |c - b| * (‖v‖ * ‖f‖) := by
          rw [abs_mul, abs_two]; unfold lipConst; ring
  have hv1 : ‖v‖ ≤ lipConst L N * |c - b| * ‖f‖ := by
    refine le_of_sq_le_mul (by have := lipConst_nonneg (L := L) (N := N); positivity) ?_
    nlinarith
  calc ‖Rop c hc f - Rop b hb f‖ = ‖(valSym v : SymL2 L N)‖ := by
        rw [hv, map_sub]; rfl
    _ ≤ ‖v‖ := norm_valSym_le v
    _ ≤ _ := hv1

/-- **Global Lipschitz estimate in operator norm.** -/
theorem Rop_lipschitz {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) :
    ‖(Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) - Rop b hb‖ ≤ lipConst L N * |c - b| := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg lipConst_nonneg (abs_nonneg _)) fun f => ?_
  have := Rop_lipschitz_apply hc hb f
  simpa [sub_apply] using this


theorem q_zero_eq (ψ : PhysH1 L N) :
    q 0 ψ ψ = ((∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [q_self_eq_bform]; simp

/-- **`basis:lem:forms` (R-81E86877), assembled** (`c ≥ 0`, constants depending only on `N, L`):
(a) the forms `h_c[ψ] = Σ_j‖∂_jψ‖² + 2cΣ_{j<k}b_{jk}[ψ]` (on the common domain `H¹_sym`, with the
printed trace-estimate bound) are closed and nonnegative, and define self-adjoint nonnegative
operators `H(c)` (the operators associated with the forms);
(b) the family increases in form order and the resolvents `(H(c)+1)⁻¹ = Rop c` decrease;
(c) the free resolvent `(H(0)+1)⁻¹` is compact, `h_0 = Σ_j‖∂_jψ‖²`;
(d) `c ↦ (H(c)+1)⁻¹` is globally Lipschitz in operator norm with constant `lipConst L N`. -/
theorem form_family :
    -- (a)
    (∀ (c : ℝ) (ψ : PhysH1 L N), q c ψ ψ =
        ((∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 + 2 * c * ∑ p : Pair N, bform p ψ : ℝ) : ℂ)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : PhysH1 L N,
        ∑ p : Pair N, bform p ψ ≤ ε * ∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 + C * ‖ψ.val‖ ^ 2) ∧
    (∀ (c : ℝ) (hc : 0 ≤ c),
      (∀ u : ℕ → PhysH1 L N, (∀ n, u n ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) →
        (∀ ε > 0, ∃ n₀ : ℕ, ∀ m n, n₀ ≤ m → n₀ ≤ n → formNormSq c (u m - u n) < ε) →
        ∃ x : PhysH1 L N, x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) ∧
          Filter.Tendsto (fun n => formNormSq c (u n - x)) Filter.atTop (nhds 0)) ∧
      (∀ ψ : PhysH1 L N, 0 ≤ (q c ψ ψ).re) ∧
      IsSelfAdjoint (Hop (L := L) (N := N) c hc) ∧ IsAssociated c (Hop (L := L) (N := N) c hc) ∧
      (∀ ψ : (Hop (L := L) (N := N) c hc).domain,
        0 ≤ (⟪(ψ : SymL2 L N), Hop c hc ψ⟫_ℂ).re) ∧
      (∀ g : SymL2 L N, ∃ h : Rop c hc g ∈ (Hop (L := L) (N := N) c hc).domain,
        Hop c hc ⟨Rop c hc g, h⟩ + Rop c hc g = g) ∧
      ∀ ψ : (Hop (L := L) (N := N) c hc).domain,
        Rop c hc (Hop c hc ψ + (ψ : SymL2 L N)) = ψ) ∧
    -- (b)
    (∀ (c c' : ℝ) (hc : 0 ≤ c) (hc' : 0 ≤ c'), c ≤ c' →
      (∀ ψ : PhysH1 L N, (q c ψ ψ).re ≤ (q c' ψ ψ).re) ∧
      ∀ f : SymL2 L N, (⟪Rop c' hc' f, f⟫_ℂ).re ≤ (⟪Rop c hc f, f⟫_ℂ).re) ∧
    -- (c)
    (IsCompactOperator (Rop 0 le_rfl : SymL2 L N →L[ℂ] SymL2 L N) ∧
      ∀ ψ : PhysH1 L N, q 0 ψ ψ = ((∑ j : Fin N, ‖gradientCLM j ψ‖ ^ 2 : ℝ) : ℂ)) ∧
    -- (d)
    (0 ≤ lipConst L N ∧ ∀ (c b : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ b),
      ‖(Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) - Rop b hb‖ ≤ lipConst L N * |c - b|) := by
  refine ⟨q_self_eq_bform, fun ε hε => sum_bform_le hε, ?_, ?_, ?_, ?_⟩
  · intro c hc
    exact ⟨fun u hs hu => form_complete_sym hc u hs hu, fun ψ => q_nonneg hc ψ,
      Hop_isSelfAdjoint hc, Hop_isAssociated hc, Hop_domain_nonneg hc, Hop_Rop hc, Rop_Hop_add hc⟩
  · intro c c' hc hc' h
    exact ⟨fun ψ => q_mono h ψ, fun f => Rop_antitone hc hc' h f⟩
  · exact ⟨Hop_compact_resolvent le_rfl, q_zero_eq⟩
  · exact ⟨lipConst_nonneg, fun c b hc hb => Rop_lipschitz hc hb⟩

end Family

end QuantumNLS.ContactFormFamily
