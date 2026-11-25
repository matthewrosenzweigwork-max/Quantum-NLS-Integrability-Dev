import QuantumNLS.BetheVandermonde
import QuantumNLS.BetheLabels
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# R-BE514996 `intr:finite:thm:finite-diagonal-phase` (finite.tex:18-115)

Lean convention: the printed particle number `N ≥ 1` is `N + 1` here (`Fin (N+1)`), as in the
accepted `BetheEigenGlobal`/`BetheVandermonde`; Lean indices are zero based, printed `j = j.val+1`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology InnerProductSpace ComplexConjugate ContDiff Pointwise
open Filter MeasureTheory Set Polynomial
open QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.BetheWavefunctions QuantumNLS.BetheExtension
  QuantumNLS.BetheWeakGradient QuantumNLS.BetheH1 QuantumNLS.BetheEigen

namespace QuantumNLS.FiniteDiagonalPhase

/-- Lagrange-interpolation identity: `∑_p ∏_{k≠p} (1 - u/(v_p - v_k)) = n`. -/
theorem lagrange_sum {n : ℕ} (v : Fin n → ℂ) (hv : Function.Injective v) (u : ℂ) :
    ∑ p : Fin n, ∏ k ∈ Finset.univ.erase p, (1 - u / (v p - v k)) = n := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases hu : u = 0
  · subst hu; simp
  -- P = nodal (v + u) - nodal v
  set f : Polynomial ℂ := Lagrange.nodal Finset.univ v with hf
  set g : Polynomial ℂ := Lagrange.nodal Finset.univ (fun i => v i + u) with hg
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hfm : f.Monic := Lagrange.nodal_monic
  have hgm : g.Monic := Lagrange.nodal_monic
  have hfd : f.natDegree = n := by rw [hf, Lagrange.natDegree_nodal]; exact hcard
  have hgd : g.natDegree = n := by rw [hg, Lagrange.natDegree_nodal]; exact hcard
  have hdeg : (g - f).degree < ↑n := by
    have h1 : g.degree = f.degree := by
      rw [Polynomial.degree_eq_natDegree hfm.ne_zero, Polynomial.degree_eq_natDegree hgm.ne_zero,
        hfd, hgd]
    have := Polynomial.degree_sub_lt_left h1 hgm.ne_zero (by rw [hfm.leadingCoeff, hgm.leadingCoeff])
    rw [h1, Polynomial.degree_eq_natDegree hfm.ne_zero, hfd] at this
    exact this
  have hcoeff : (g - f).coeff (n - 1) = -(n : ℂ) * u := by
    rw [Polynomial.coeff_sub]
    have e1 := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin n))
      (fun i => v i + u) (by simpa using hn)
    have e2 := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin n)) v
      (by simpa using hn)
    simp only [hcard] at e1 e2
    rw [hg, hf, Lagrange.nodal_eq, Lagrange.nodal_eq, e1, e2]
    simp [Finset.sum_add_distrib]
  have hL := Lagrange.coeff_eq_sum (s := Finset.univ) (v := v) (hv.injOn) (P := g - f)
    (by simpa using hdeg)
  simp only [hcard] at hL
  rw [hcoeff] at hL
  have hev (i : Fin n) : (g - f).eval (v i) = (-u) *
      ∏ j ∈ Finset.univ.erase i, (v i - u - v j) := by
    have h0 : ∏ j, (v i - v j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
    rw [Polynomial.eval_sub, hg, hf]
    simp only [Lagrange.eval_nodal]
    rw [h0, sub_zero, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · ring
    · apply Finset.prod_congr rfl
      intro j _; ring
  have hne (i : Fin n) (j : Fin n) (hj : j ∈ Finset.univ.erase i) : v i - v j ≠ 0 :=
    sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hv h).symm)
  have hterm (i : Fin n) : (g - f).eval (v i) / ∏ j ∈ Finset.univ.erase i, (v i - v j) =
      (-u) * ∏ k ∈ Finset.univ.erase i, (1 - u / (v i - v k)) := by
    rw [hev, mul_div_assoc, ← Finset.prod_div_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have := hne i j hj
    field_simp
    ring
  simp only [hterm, ← Finset.mul_sum] at hL
  have := mul_left_cancel₀ (neg_ne_zero.mpr hu) (by rw [← hL]; ring : (-u) * (n : ℂ) =
    (-u) * ∑ i, ∏ k ∈ Finset.univ.erase i, (1 - u / (v i - v k)))
  exact this.symm


/-- Product over ordered pairs of positions `j < k` of the scattering factors. -/
def cf {n : ℕ} (u : ℂ) (v : Fin n → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), (1 - u / (v i - v j))

theorem cf_succ {n : ℕ} (u : ℂ) (v : Fin (n+1) → ℂ) :
    cf u v = (∏ j : Fin n, (1 - u / (v 0 - v j.succ))) * cf u (fun i => v i.succ) := by
  classical
  unfold cf
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Finset.prod_filter]
    rw [Fin.prod_univ_succ]
    simp
  · apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
    simp

theorem prod_erase_eq {n : ℕ} (g : Fin (n+1) → ℂ) (p : Fin (n+1)) :
    ∏ k ∈ Finset.univ.erase p, g k = ∏ j : Fin n, g (Equiv.swap 0 p j.succ) := by
  classical
  symm
  apply Finset.prod_nbij (fun j => Equiv.swap 0 p j.succ)
  · intro j _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    have := congrArg (Equiv.swap 0 p) h
    simp at this
  · intro a _ b _ h
    exact Fin.succ_injective _ ((Equiv.swap 0 p).injective h)
  · intro k hk
    simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at hk
    have h0 : Equiv.swap 0 p k ≠ 0 := by
      intro h
      apply hk
      have := congrArg (Equiv.swap 0 p) h
      simpa using this
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr h0
    exact ⟨j, by simp, by simp only [hj]; simp⟩
  · intro j _
    rfl

/-- The sum of all scattering amplitudes at distinct frequencies is `n!`. -/
theorem sum_cf {n : ℕ} (u : ℂ) (v : Fin n → ℂ) (hv : Function.Injective v) :
    ∑ σ : Equiv.Perm (Fin n), cf u (v ∘ σ) = (n.factorial : ℂ) := by
  classical
  induction n with
  | zero => simp [cf]
  | succ n ih =>
    rw [← (Equiv.Perm.decomposeFin (n := n)).symm.sum_comp, Fintype.sum_prod_type]
    have hp (p : Fin (n+1)) : ∑ τ : Equiv.Perm (Fin n),
        cf u (v ∘ Equiv.Perm.decomposeFin.symm (p, τ)) =
        (n.factorial : ℂ) * ∏ k ∈ Finset.univ.erase p, (1 - u / (v p - v k)) := by
      set w : Fin n → ℂ := fun i => v (Equiv.swap 0 p i.succ) with hw
      have hwi : Function.Injective w := by
        intro a b h
        exact Fin.succ_injective _ ((Equiv.swap 0 p).injective (hv h))
      have h1 (τ : Equiv.Perm (Fin n)) : cf u (v ∘ Equiv.Perm.decomposeFin.symm (p, τ)) =
          (∏ k ∈ Finset.univ.erase p, (1 - u / (v p - v k))) * cf u (w ∘ τ) := by
        rw [cf_succ]
        congr 1
        · rw [prod_erase_eq]
          simp only [Function.comp_apply, Equiv.Perm.decomposeFin_symm_apply_zero,
            Equiv.Perm.decomposeFin_symm_apply_succ]
          exact Fintype.prod_equiv τ _ _ (fun j => rfl)
        · simp [cf, hw]
      simp_rw [h1]
      rw [← Finset.mul_sum, ih w hwi]
      ring
    simp_rw [hp]
    rw [← Finset.mul_sum, lagrange_sum v hv u, Nat.factorial_succ]
    push_cast
    ring


/-! ### The printed objects, literally -/

/-- Printed `I_j = n_j + j - (N+1)/2`, with `M` the printed particle number and the printed
index `j` equal to `j.val + 1`. -/
def printedLabel {M : ℕ} (n : Fin M → ℤ) (j : Fin M) : ℝ :=
  (n j : ℝ) + ((j.val : ℝ) + 1) - ((M : ℝ) + 1) / 2

/-- Printed equation `L q_j + 2 Σ_{k≠j} arctan((q_j - q_k)/c) = 2π I_j`. -/
def LogBethe {M : ℕ} (L c : ℝ) (I q : Fin M → ℝ) : Prop :=
  ∀ j : Fin M, L * q j + 2 * ∑ k ∈ Finset.univ.erase j, Real.arctan ((q j - q k) / c) =
    2 * Real.pi * I j

/-- Printed `A_σ(q,c) = ∏_{j<k} (1 - ic/(q_{σ(j)} - q_{σ(k)}))`. -/
def finiteA {M : ℕ} (c : ℝ) (q : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) : ℂ :=
  ∏ j : Fin M, ∏ k ∈ Finset.univ.filter (fun k => j < k),
    (1 - Complex.I * (c : ℂ) / ((q (σ j) - q (σ k) : ℝ) : ℂ))

/-- Printed `B_{q,c}(x) = Σ_σ A_σ(q,c) exp(i Σ_j q_{σ(j)} x_j)`. -/
def finiteB {M : ℕ} (c : ℝ) (q : Fin M → ℝ) (x : Fin M → ℝ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin M), finiteA c q σ *
    Complex.exp (Complex.I * ((∑ j : Fin M, q (σ j) * x j : ℝ) : ℂ))

/-- Printed `Z_{q,c} = N! ∫_{0<x_N<⋯<x_1<L} |B_{q,c}(x)|² dx`. -/
def finiteZ {M : ℕ} (L c : ℝ) (q : Fin M → ℝ) : ℝ :=
  (M.factorial : ℝ) * ∫ x in chamber M L, ‖finiteB c q x‖ ^ 2

theorem printedLabel_eq (M : ℕ) (n : Fin M → ℤ) :
    printedLabel n = BetheAdmission.quantumNumbers n := by
  funext j
  unfold printedLabel BetheAdmission.quantumNumbers
  ring

theorem labelsOf_correctedInt {M : ℕ} {n : Fin M → ℤ} (hn : Monotone n) :
    BetheLabels.correctedInt (BetheLabels.labelsOf ⟨n, hn⟩) = n :=
  congrArg Subtype.val (BetheLabels.labelsEquivCorrected.right_inv ⟨n, hn⟩)

/-- **Identification of the printed solution `q` with the accepted roots** (increasing
convention of `BetheAdmission`, via the `BetheLabels` bridge). -/
theorem logBethe_iff_roots {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin M → ℤ} (hn : Monotone n) (q : Fin M → ℝ) :
    LogBethe L c (printedLabel n) q ↔ q = BetheSmooth.roots L n c := by
  have h := BetheLabels.rapidityEq_iff_roots hL hc (BetheLabels.labelsOf ⟨n, hn⟩) q
  rw [labelsOf_correctedInt hn] at h
  rw [printedLabel_eq]
  exact h

theorem roots_strictMono {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin M → ℤ} (hn : Monotone n) : StrictMono (BetheSmooth.roots L n c) := by
  have h := BetheLabels.roots_strictMono_labels hL hc (BetheLabels.labelsOf ⟨n, hn⟩)
  rwa [labelsOf_correctedInt hn] at h

theorem coordinateAnsatz_comp_perm {M : ℕ} (c : ℝ) (q : Fin M → ℝ)
    (τ : Equiv.Perm (Fin M)) (x : Fin M → ℝ) :
    coordinateAnsatz c (q ∘ τ) x = coordinateAnsatz c q x := by
  unfold coordinateAnsatz
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ : Equiv.Perm (Fin M) =>
    coefficient c (q ∘ σ) * planeWave (q ∘ σ) x)

theorem finiteB_eq_coordinateAnsatz {M : ℕ} (c : ℝ) (q : Fin M → ℝ) :
    finiteB c q = coordinateAnsatz c q := rfl

/-- The accepted decreasing source roots are the printed increasing roots reversed. -/
theorem sourceRoots_eq_comp_rev {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin M → ℤ) :
    BetheSmooth.sourceRoots L (BetheLabels.srcOf n) c =
      BetheSmooth.roots L n c ∘ Fin.revPerm := by
  funext i
  exact BetheLabels.sourceRoots_eq_roots_rev hL hc n i

/-- **The printed `B_{q,c}` is the accepted source wavefunction** of the reversed
(nonincreasing) labels, on all real coordinates. -/
theorem finiteB_roots_eq_wavefunction {M : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (n : Fin M → ℤ) :
    finiteB c (BetheSmooth.roots L n c) =
      wavefunction L c (BetheLabels.srcOf n) := by
  funext x
  rw [finiteB_eq_coordinateAnsatz]
  unfold wavefunction
  rw [sourceRoots_eq_comp_rev hL hc, coordinateAnsatz_comp_perm]

/-- Amplitudes are the accepted Bethe coefficients. -/
theorem finiteA_eq_coefficient {M : ℕ} (c : ℝ) (q : Fin M → ℝ) (σ : Equiv.Perm (Fin M)) :
    finiteA c q σ = coefficient c (q ∘ σ) := rfl

/-- **The diagonal identity** `Σ_σ A_σ(q,c) = N!` (printed alternating-polynomial step), for
distinct frequencies; proved by the Lagrange identity and induction on `N`. -/
theorem sum_finiteA {M : ℕ} (c : ℝ) {q : Fin M → ℝ} (hq : Function.Injective q) :
    ∑ σ : Equiv.Perm (Fin M), finiteA c q σ = (M.factorial : ℂ) := by
  have hv : Function.Injective (fun i => (q i : ℂ)) := fun a b h =>
    hq (Complex.ofReal_injective h)
  have := sum_cf (Complex.I * (c : ℂ)) (fun i => (q i : ℂ)) hv
  rw [← this]
  apply Finset.sum_congr rfl
  intro σ _
  unfold finiteA cf
  simp [Function.comp_apply]

/-- **Printed diagonal formula** `B_{q,c}(a,…,a) = N! e^{i a Σ q_j}`. -/
theorem finiteB_diagonal {M : ℕ} (c : ℝ) {q : Fin M → ℝ} (hq : Function.Injective q) (a : ℝ) :
    finiteB c q (fun _ => a) =
      (M.factorial : ℂ) * Complex.exp (Complex.I * (a : ℂ) * ∑ j, (q j : ℂ)) := by
  have he (σ : Equiv.Perm (Fin M)) :
      Complex.exp (Complex.I * ((∑ j : Fin M, q (σ j) * a : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (a : ℂ) * ∑ j, (q j : ℂ)) := by
    congr 1
    have : ∑ j : Fin M, q (σ j) * a = a * ∑ j, q j := by
      rw [← Finset.sum_mul, Equiv.sum_comp σ q]; ring
    rw [this]
    push_cast
    ring
  unfold finiteB
  simp_rw [he]
  rw [← Finset.sum_mul, sum_finiteA c hq]


/-! ### The cube integral of a symmetrically extended function equals `N!` chamber integrals -/

/-- The permuted open chamber `{x : x ∘ σ ∈ chamber}`. -/
def permChamber (M : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin M)) : Set (Fin M → ℝ) :=
  {x | (fun i => x (σ i)) ∈ chamber M L}

theorem permChamber_eq_preimage (M : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin M)) :
    permChamber M L σ =
      (fun x : Fin M → ℝ => fun i => x (σ i)) ⁻¹' chamber M L := rfl

theorem measurePreserving_permute (M : ℕ) (σ : Equiv.Perm (Fin M)) :
    MeasurePreserving (fun x : Fin M → ℝ => fun i => x (σ i)) volume volume :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin M => ℝ) σ).symm

theorem measurableSet_chamber (M : ℕ) (L : ℝ) : MeasurableSet (chamber M L) :=
  (BetheEigenGlobal.isOpen_chamber M L).measurableSet

theorem measurableSet_permChamber (M : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin M)) :
    MeasurableSet (permChamber M L σ) :=
  (measurePreserving_permute M σ).measurable (measurableSet_chamber M L)

theorem permChamber_subset_cube (M : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin M)) :
    permChamber M L σ ⊆ Icc (fun _ => (0 : ℝ)) (fun _ => L) := by
  intro x hx
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (hx.2 (σ.symm i)).1.le
    simpa using this
  · have := (hx.2 (σ.symm i)).2.le
    simpa using this

theorem permChamber_disjoint (M : ℕ) (L : ℝ) :
    Pairwise (Function.onFun Disjoint (permChamber M L)) := by
  intro σ τ hστ
  rw [Function.onFun, Set.disjoint_left]
  intro x hσ hτ
  apply hστ
  have hs := hσ.1
  have ht := hτ.1
  have hxi : Function.Injective x := by
    intro a b hab
    have := hs.injective (show (fun i => x (σ i)) (σ.symm a) = (fun i => x (σ i)) (σ.symm b) by
      simpa using hab)
    simpa using this
  have h := Tuple.unique_antitone (σ := σ) (τ := τ) hs.antitone ht.antitone
  apply Equiv.ext
  intro i
  exact hxi (congrFun h i)

/-- **`∫_{[0,L]^N} h(decreasing x) = N! ∫_{chamber} h`**: the cube is the union of the `N!`
permuted chambers up to a null set (coordinate hyperplanes and collision walls). -/
theorem cube_integral_decreasing {M : ℕ} {L : ℝ} (h : (Fin M → ℝ) → ℝ)
    (hh : Continuous h) :
    ∫ x, h (decreasing x) ∂cubeMeasure M L = (M.factorial : ℝ) * ∫ x in chamber M L, h x := by
  classical
  set μ := cubeMeasure M L with hμ
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ σ, permChamber M L σ := by
    have hb : ∀ᵐ x ∂μ, ∀ i, x i ≠ 0 ∧ x i ≠ L := by
      rw [hμ, cubeMeasure_eq_pi]
      refine Filter.eventually_all.2 fun i => ?_
      filter_upwards [Measure.ae_eval_ne (fun _ : Fin M => volume.restrict (Icc (0 : ℝ) L)) i 0,
        Measure.ae_eval_ne (fun _ : Fin M => volume.restrict (Icc (0 : ℝ) L)) i L]
        with x h0 h1
      exact ⟨h0, h1⟩
    filter_upwards [BetheEigen.cube_ae_injective (N := M) L,
      ae_restrict_mem measurableSet_Icc, hb] with x hinj hcube hbd
    refine Set.mem_iUnion.2 ⟨Tuple.sort (α := ℝᵒᵈ) x, ?_⟩
    have hanti : Antitone (x ∘ Tuple.sort (α := ℝᵒᵈ) x) := decreasing_antitone x
    have hinj' : Function.Injective (x ∘ Tuple.sort (α := ℝᵒᵈ) x) :=
      hinj.comp (Tuple.sort (α := ℝᵒᵈ) x).injective
    refine ⟨hanti.strictAnti_of_injective hinj', fun i => ?_⟩
    have hc := hcube
    have h1 := hbd (Tuple.sort (α := ℝᵒᵈ) x i)
    exact ⟨lt_of_le_of_ne (hc.1 _) (Ne.symm h1.1), lt_of_le_of_ne (hc.2 _) h1.2⟩
  have hint : ∀ σ : Equiv.Perm (Fin M),
      IntegrableOn (fun x => h (decreasing x)) (permChamber M L σ) μ := by
    intro σ
    have h1 : Integrable (fun x => h (decreasing x)) μ :=
      ((hh.comp (continuous_decreasing M)).continuousOn.integrableOn_compact isCompact_Icc :
        IntegrableOn _ (Icc (fun _ => (0 : ℝ)) (fun _ => L)) volume)
    exact h1.integrableOn
  have hsub (σ : Equiv.Perm (Fin M)) :
      ∫ x in permChamber M L σ, h (decreasing x) ∂μ = ∫ x in chamber M L, h x := by
    have hr : μ.restrict (permChamber M L σ) = volume.restrict (permChamber M L σ) := by
      rw [hμ, cubeMeasure, Measure.restrict_restrict (measurableSet_permChamber M L σ),
        Set.inter_eq_left.mpr (permChamber_subset_cube M L σ)]
    rw [hr]
    have hcongr : ∫ x in permChamber M L σ, h (decreasing x) =
        ∫ x in permChamber M L σ, h (fun i => x (σ i)) := by
      apply setIntegral_congr_fun (measurableSet_permChamber M L σ)
      intro x hx
      have hs : Antitone (x ∘ σ) := hx.1.antitone
      simp only [decreasing_eq_permute x σ hs]
      rfl
    rw [hcongr, permChamber_eq_preimage]
    exact (measurePreserving_permute M σ).setIntegral_preimage_emb
      (MeasurableEquiv.piCongrLeft (fun _ : Fin M => ℝ) σ).symm.measurableEmbedding
      h (chamber M L)
  rw [← Measure.restrict_eq_self_of_ae_mem hae, integral_iUnion_fintype
    (fun σ => measurableSet_permChamber M L σ) (permChamber_disjoint M L) hint]
  simp only [hsub, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]


/-! ### The symmetric periodic extension, its norm and positivity of `Z` -/

section Extension
variable {N : ℕ} {L c : ℝ} [Fact (0 < L)]

/-- The printed symmetric periodic extension of `B_{q,c}` (`q` the root vector of the
increasing labels `n`): the accepted `torusExtension` of the reversed, nonincreasing labels. -/
def finiteExt (L c : ℝ) [Fact (0 < L)] {M : ℕ} (n : Fin M → ℤ) :
    (Fin M → AddCircle L) → ℂ :=
  torusExtension L c (BetheLabels.srcOf n)

theorem finiteExt_continuous (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    Continuous (finiteExt L c n) :=
  continuous_torusExtension hc (BetheLabels.srcOf_antitone hn)

theorem finiteExt_permute {M : ℕ} (n : Fin M → ℤ) (x : Fin M → AddCircle L)
    (σ : Equiv.Perm (Fin M)) : finiteExt L c n (x ∘ σ) = finiteExt L c n x :=
  torusExtension_permute L c _ x σ

theorem finiteExt_chamber (hc : 0 < c) {n : Fin (N+1) → ℤ}
    {x : Fin (N+1) → ℝ} (hx : x ∈ chamber (N+1) L) :
    finiteExt L c n (fun i => (x i : AddCircle L)) =
      finiteB c (BetheSmooth.roots L n c) x := by
  have hL : 0 < L := Fact.out
  rw [finiteB_roots_eq_wavefunction hL hc]
  exact periodicExtension_chamber L c _ hx

theorem finiteExt_eq {M : ℕ} {n : Fin M → ℤ} (hc : 0 < c) (x : Fin M → AddCircle L) :
    finiteExt L c n x = finiteB c (BetheSmooth.roots L n c)
      (decreasing (fun i => (AddCircle.equivIco L 0 (x i) : ℝ))) := by
  have hL : 0 < L := Fact.out
  rw [finiteB_roots_eq_wavefunction hL hc]
  rfl

theorem finiteZ_eq_norm_sq (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    ‖(waveH1 (L := L) hc (BetheLabels.srcOf_antitone hn)).val‖ ^ 2 =
      finiteZ L c (BetheSmooth.roots L n c) := by
  have hL : 0 < L := Fact.out
  have hn' := BetheLabels.srcOf_antitone hn
  set w := waveH1 (L := L) hc hn' with hw
  have hE : Continuous (torusExtension L c (BetheLabels.srcOf n)) := continuous_torusExtension hc hn'
  have h1 := BetheCollision.inner_eq_integral_of_ae w.val w.val (coe_waveH1_val (L := L) hc hn')
    (coe_waveH1_val (L := L) hc hn')
  have h0 : ⟪w.val, w.val⟫_ℂ = ((‖w.val‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h0] at h1
  have h2 : ∫ y, conj (torusExtension L c (BetheLabels.srcOf n) y) *
      torusExtension L c (BetheLabels.srcOf n) y ∂torusPiMeasure L (N+1) =
      ((∫ y, ‖torusExtension L c (BetheLabels.srcOf n) y‖ ^ 2 ∂torusPiMeasure L (N+1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with y
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [h2] at h1
  have h3 : ‖w.val‖ ^ 2 = ∫ y, ‖torusExtension L c (BetheLabels.srcOf n) y‖ ^ 2
      ∂torusPiMeasure L (N+1) := Complex.ofReal_injective h1
  rw [h3]
  have h4 := torus_integral_cube (N := N+1) L
    (fun y => ((‖torusExtension L c (BetheLabels.srcOf n) y‖ ^ 2 : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp ((hE.norm).pow 2)).aestronglyMeasurable)
  have h5 : ∫ y, ‖torusExtension L c (BetheLabels.srcOf n) y‖ ^ 2 ∂torusPiMeasure L (N+1) =
      ∫ x, ‖symmetricExtension L c (BetheLabels.srcOf n) x‖ ^ 2 ∂cubeMeasure (N+1) L := by
    have h6 : ((∫ y, ‖torusExtension L c (BetheLabels.srcOf n) y‖ ^ 2
        ∂torusPiMeasure L (N+1) : ℝ) : ℂ) =
        ((∫ x, ‖symmetricExtension L c (BetheLabels.srcOf n) x‖ ^ 2 ∂cubeMeasure (N+1) L : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal, ← integral_complex_ofReal]
      rw [show torusPiMeasure L (N+1) = (volume : Measure (Fin (N+1) → AddCircle L)) from volume_pi.symm]
      rw [h4]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with x hx
      rw [torusExtension_closed_cube hc hn' x (fun i => ⟨hx.1 i, hx.2 i⟩)]
    exact_mod_cast h6
  rw [h5]
  have h7 := cube_integral_decreasing (M := N+1) (L := L)
    (fun y => ‖wavefunction L c (BetheLabels.srcOf n) y‖ ^ 2)
    ((((coordinateAnsatz_contDiff c _).continuous).norm).pow 2)
  unfold finiteZ
  rw [finiteB_roots_eq_wavefunction hL hc]
  exact h7


end Extension

/-! ### Finiteness and positivity of `Z` (printed: diagonal value plus continuity) -/

theorem integrableOn_chamber {M : ℕ} (L c : ℝ) (q : Fin M → ℝ) :
    IntegrableOn (fun x => ‖finiteB c q x‖ ^ 2) (chamber M L) := by
  have hc : Continuous (finiteB c q) := (coordinateAnsatz_contDiff c q).continuous
  have h : IntegrableOn (fun x => ‖finiteB c q x‖ ^ 2) (Icc (fun _ => (0 : ℝ)) (fun _ => L))
      volume := ((hc.norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc
  exact h.mono_set (fun x hx => ⟨fun i => (hx.2 i).1.le, fun i => (hx.2 i).2.le⟩)

/-- `0 < Z_{q,c}`: the diagonal value `N! e^{…} ≠ 0` and continuity give a point of the open
chamber where `B ≠ 0`; then the integral of a continuous nonnegative function is positive. -/
theorem finiteZ_pos {M : ℕ} {L : ℝ} (hL : 0 < L) (c : ℝ) {q : Fin M → ℝ}
    (hq : Function.Injective q) : 0 < finiteZ L c q := by
  have hB : Continuous (finiteB c q) := (coordinateAnsatz_contDiff c q).continuous
  have hg : Continuous (fun x => ‖finiteB c q x‖ ^ 2) := hB.norm.pow 2
  have hne : finiteB c q (fun _ => L / 2) ≠ 0 := by
    rw [finiteB_diagonal c hq]
    exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos M).ne') (Complex.exp_ne_zero _)
  let γ : ℝ → (Fin M → ℝ) := fun ε i => L / 2 - ε * (i.val : ℝ)
  have hγ : Continuous γ := by unfold γ; fun_prop
  have h0 : γ 0 = fun _ => L / 2 := by funext i; simp [γ]
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), finiteB c q (γ ε) ≠ 0 := by
    have hc0 : ContinuousAt (fun ε => finiteB c q (γ ε)) 0 := (hB.comp hγ).continuousAt
    exact hc0.eventually_ne (by rw [h0]; exact hne)
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < L / (2 * ((M : ℝ) + 1)) :=
    Ioo_mem_nhdsGT (by positivity)
  obtain ⟨ε, hε1, hε2, hε3⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and hev2).exists
  have hch : γ ε ∈ chamber M L := by
    have hM : ((M : ℝ) + 1) > 0 := by positivity
    have hlt : ε * ((M : ℝ) + 1) < L / 2 := by
      calc ε * ((M : ℝ) + 1) < L / (2 * ((M : ℝ) + 1)) * ((M : ℝ) + 1) :=
            mul_lt_mul_of_pos_right hε3 hM
        _ = L / 2 := by field_simp
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have : (i.val : ℝ) < j.val := by exact_mod_cast hij
      show L / 2 - ε * (j.val : ℝ) < L / 2 - ε * (i.val : ℝ)
      nlinarith
    · have hi : (i.val : ℝ) ≤ M := by exact_mod_cast i.2.le
      have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      constructor
      · show 0 < L / 2 - ε * (i.val : ℝ)
        nlinarith
      · show L / 2 - ε * (i.val : ℝ) < L
        nlinarith
  have hpos : 0 < ∫ x in chamber M L, ‖finiteB c q x‖ ^ 2 := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => by positivity) (integrableOn_chamber L c q)]
    apply IsOpen.measure_pos
    · exact (hg.isOpen_support).inter (BetheEigenGlobal.isOpen_chamber M L)
    · refine ⟨γ ε, ?_, hch⟩
      simp only [Function.mem_support]
      positivity
  unfold finiteZ
  exact mul_pos (by exact_mod_cast Nat.factorial_pos M) hpos

/-! ### The normalized vector, eigen-equation, diagonal origin value and phase uniqueness -/

section Psi
variable {N : ℕ} {L c : ℝ} [Fact (0 < L)]

theorem sum_sq_roots_eq_energy (hc : 0 < c) {n : Fin (N+1) → ℤ} :
    energy L c (BetheLabels.srcOf n) = ∑ j, BetheSmooth.roots L n c j ^ 2 := by
  have hL : 0 < L := Fact.out
  unfold energy
  rw [sourceRoots_eq_comp_rev hL hc]
  exact Equiv.sum_comp Fin.revPerm (fun j => BetheSmooth.roots L n c j ^ 2)

/-- The printed normalized wave `Ψ^d = Z^{-1/2} B`, as a vector of the symmetric space `L²_sym`:
the positive scalar `Z^{-1/2}` times the accepted `H¹_sym` Bethe vector of the labels `n`. -/
def finitePsi (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    ContactOperator.SymL2 L (N+1) :=
  ((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) •
    ContactOperator.valSym (waveH1Sym (L := L) hc (BetheLabels.srcOf_antitone hn))

theorem norm_valSym_wave (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    ‖ContactOperator.valSym (waveH1Sym (L := L) hc (BetheLabels.srcOf_antitone hn))‖ =
      Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)) := by
  rw [← finiteZ_eq_norm_sq hc hn, Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem finitePsi_norm (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    ‖finitePsi (L := L) hc hn‖ = 1 := by
  have hL : 0 < L := Fact.out
  have hZ := finiteZ_pos hL c (roots_strictMono hL hc hn).injective
  unfold finitePsi
  rw [norm_smul, norm_valSym_wave hc hn]
  have hs : 0 < Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)) := Real.sqrt_pos.2 hZ
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hs.le]
  exact inv_mul_cancel₀ hs.ne'

theorem finitePsi_ae (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    ((finitePsi (L := L) hc hn : ContactOperator.SymL2 L (N+1)) : L2TN L (N+1)) =ᵐ[torusPiMeasure L (N+1)]
      fun x => ((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) *
        finiteExt L c n x := by
  have hn' := BetheLabels.srcOf_antitone hn
  have h1 := Lp.coeFn_smul (((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ))
    (((ContactOperator.valSym (waveH1Sym (L := L) hc hn')) : ContactOperator.SymL2 L (N+1)) :
      L2TN L (N+1))
  filter_upwards [h1, coe_waveH1_val (L := L) hc hn'] with x hx hv
  change (((((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) •
      ((ContactOperator.valSym (waveH1Sym (L := L) hc hn')) : ContactOperator.SymL2 L (N+1)) :
      ContactOperator.SymL2 L (N+1)) : L2TN L (N+1)) : (Fin (N+1) → AddCircle L) → ℂ) x = _
  rw [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul]
  congr 1

theorem finitePsi_eigen (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    ∃ h : finitePsi (L := L) hc hn ∈ (ContactOperator.Hop c hc.le).domain,
      ContactOperator.Hop c hc.le ⟨finitePsi hc hn, h⟩ =
        ((∑ j, BetheSmooth.roots L n c j ^ 2 : ℝ) : ℂ) • finitePsi hc hn := by
  have hn' := BetheLabels.srcOf_antitone hn
  obtain ⟨h, heq⟩ := BetheEigenGlobal.Hop_eigen (L := L) hc hn'
  refine ⟨(ContactOperator.Hop c hc.le).domain.smul_mem _ h, ?_⟩
  have hsm : (⟨finitePsi (L := L) hc hn, (ContactOperator.Hop c hc.le).domain.smul_mem _ h⟩ :
      (ContactOperator.Hop c hc.le).domain) =
      ((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) •
        (⟨ContactOperator.valSym (waveH1Sym (L := L) hc hn'), h⟩ :
          (ContactOperator.Hop c hc.le).domain) := rfl
  rw [hsm, (ContactOperator.Hop c hc.le).map_smul, heq, smul_comm, ← sum_sq_roots_eq_energy hc]
  rfl

theorem finiteExt_origin (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    finiteExt L c n 0 = ((N+1).factorial : ℂ) := by
  have hL : 0 < L := Fact.out
  have hn' := BetheLabels.srcOf_antitone hn
  have h0 : (0 : Fin (N+1) → AddCircle L) = fun i => (((fun _ => (0 : ℝ)) i : ℝ) : AddCircle L) := by
    funext i; simp
  rw [h0]
  unfold finiteExt
  rw [torusExtension_closed_cube hc hn' (fun _ => 0) (fun i => ⟨le_rfl, hL.le⟩)]
  unfold symmetricExtension
  rw [decreasing_eq (fun _ _ _ => le_rfl), ← finiteB_roots_eq_wavefunction hL hc,
    finiteB_diagonal c (roots_strictMono hL hc hn).injective]
  simp

end Psi

/-! ### Phase uniqueness and the assembled theorem -/

/-- `z` is a positive real number. -/
def IsPositiveReal (z : ℂ) : Prop := 0 < z.re ∧ z.im = 0

section Phase
variable {N : ℕ} {L c : ℝ} [Fact (0 < L)]

theorem origin_value (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    ((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) * finiteExt L c n 0 =
      (((N+1).factorial * (Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℝ) : ℂ) := by
  rw [finiteExt_origin hc hn]
  push_cast
  ring

theorem origin_pos (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    0 < ((N+1).factorial : ℝ) * (Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ := by
  have hL : 0 < L := Fact.out
  have hZ := finiteZ_pos hL c (roots_strictMono hL hc hn).injective
  have hs : 0 < Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)) := Real.sqrt_pos.2 hZ
  have := Nat.factorial_pos (N+1)
  positivity

/-- **Unique phase in the eigenline**: the unit vectors `θ Ψ` of the line `ℂ Ψ` whose value at the
full diagonal origin `(0,…,0)` is positive are exactly `Ψ`. -/
theorem phase_unique (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) (θ : ℂ)
    (h1 : ‖θ • finitePsi (L := L) hc hn‖ = 1)
    (h2 : IsPositiveReal (θ * (((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) *
      finiteExt L c n 0))) :
    θ • finitePsi (L := L) hc hn = finitePsi hc hn := by
  rw [norm_smul, finitePsi_norm hc hn, mul_one] at h1
  rw [origin_value hc hn] at h2
  set r : ℝ := ((N+1).factorial : ℝ) * (Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ with hr
  have hr0 : 0 < r := origin_pos hc hn
  obtain ⟨h2a, h2b⟩ := h2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h2a
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at h2b
  have hre : 0 < θ.re := by
    by_contra hneg
    push Not at hneg
    exact absurd h2a (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hneg hr0.le))
  have him : θ.im = 0 := by
    rcases mul_eq_zero.1 h2b with h | h
    · exact h
    · exact absurd h hr0.ne'
  have hsq : θ.re * θ.re = 1 := by
    have h := Complex.normSq_eq_norm_sq θ
    rw [h1, Complex.normSq_apply, him] at h
    nlinarith
  have hre1 : θ.re = 1 := by nlinarith
  have hθ : θ = 1 := Complex.ext (by simpa using hre1) (by simpa using him)
  rw [hθ, one_smul]


/-- **`intr:finite:thm:finite-diagonal-phase`** (printed `N` is `N+1` here; zero-based indices),
all clauses except real-analytic dependence (see `finite_phase_analytic`).

* (1) the printed equation has a unique real solution `q`; it is strictly increasing, and it is
  the accepted root vector `BetheSmooth.roots` of the labels `n` (increasing convention);
* (2) `A_σ(q,c)` are the accepted Bethe coefficients and `B_{q,c}` is the accepted source
  wavefunction of the reversed labels, on all real coordinates;
* (3) the symmetric periodic extension is a continuous symmetric function on the torus equal to
  `B` on the chamber (explicitly `B` of the decreasing rearrangement of the representatives);
* (4) `0 < Z_{q,c} < ∞` (finite integral, `Z > 0`);
* (5) `Ψ^d = Z^{-1/2} B` is a unit vector of `L²_sym(𝕋_L^N)`, in the domain of the actual
  contact Hamiltonian `Hop`, eigenvector with eigenvalue `Σ q_j²` (the printed chamber energy);
* (6) `B_{q,c}(a,…,a) = N! e^{ia Σ q_j}`, `Ψ^d(0,…,0) = N! Z^{-1/2} > 0`;
* (7) within the eigenline `ℂ Ψ^d` it is the unique unit vector positive at the origin;
* (8) `m_k = #{j : n_j = k}` is the accepted multiplicity array. -/
theorem finite_diagonal_phase (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Monotone n) :
    (∃! q : Fin (N+1) → ℝ, LogBethe L c (printedLabel n) q) ∧
    (∀ q : Fin (N+1) → ℝ, LogBethe L c (printedLabel n) q → StrictMono q) ∧
    (∀ q : Fin (N+1) → ℝ, LogBethe L c (printedLabel n) q →
      (q = BetheSmooth.roots L n c ∧
       BetheSmooth.sourceRoots L (BetheLabels.srcOf n) c = q ∘ Fin.revPerm ∧
       (∀ σ, finiteA c q σ = coefficient c (q ∘ σ)) ∧
       finiteB c q = wavefunction L c (BetheLabels.srcOf n)) ∧
      (Continuous (finiteExt L c n) ∧
       (∀ (σ : Equiv.Perm (Fin (N+1))) (x : Fin (N+1) → AddCircle L),
          finiteExt L c n (x ∘ σ) = finiteExt L c n x) ∧
       (∀ x ∈ chamber (N+1) L, finiteExt L c n (fun i => (x i : AddCircle L)) = finiteB c q x) ∧
       (∀ x : Fin (N+1) → AddCircle L, finiteExt L c n x =
          finiteB c q (decreasing (fun i => (AddCircle.equivIco L 0 (x i) : ℝ))))) ∧
      (IntegrableOn (fun x => ‖finiteB c q x‖ ^ 2) (chamber (N+1) L) ∧
       0 < finiteZ L c q) ∧
      (∃ Ψ : ContactOperator.SymL2 L (N+1),
        ((Ψ : ContactOperator.SymL2 L (N+1)) : L2TN L (N+1)) =ᵐ[torusPiMeasure L (N+1)]
          (fun x => ((Real.sqrt (finiteZ L c q))⁻¹ : ℂ) * finiteExt L c n x) ∧
        ‖Ψ‖ = 1 ∧
        (∃ h : Ψ ∈ (ContactOperator.Hop c hc.le).domain,
          ContactOperator.Hop c hc.le ⟨Ψ, h⟩ = ((∑ j, q j ^ 2 : ℝ) : ℂ) • Ψ) ∧
        IsPositiveReal (((Real.sqrt (finiteZ L c q))⁻¹ : ℂ) * finiteExt L c n 0) ∧
        (∀ θ : ℂ, ‖θ • Ψ‖ = 1 →
          IsPositiveReal (θ * (((Real.sqrt (finiteZ L c q))⁻¹ : ℂ) * finiteExt L c n 0)) →
          θ • Ψ = Ψ)) ∧
      ((∀ a : ℝ, finiteB c q (fun _ => a) =
          ((N+1).factorial : ℂ) * Complex.exp (Complex.I * (a : ℂ) * ∑ j, (q j : ℂ))) ∧
       finiteExt L c n 0 = ((N+1).factorial : ℂ) ∧
       ((Real.sqrt (finiteZ L c q))⁻¹ : ℂ) * finiteExt L c n 0 =
         ((((N+1).factorial : ℝ) * (Real.sqrt (finiteZ L c q))⁻¹ : ℝ) : ℂ) ∧
       0 < ((N+1).factorial : ℝ) * (Real.sqrt (finiteZ L c q))⁻¹)) ∧
    (∀ k : ℤ, (BetheLabels.correctedEquivArr ⟨n, hn⟩).1 k =
      (Finset.univ.filter fun j => n j = k).card) := by
  have hL : 0 < L := Fact.out
  have hmono := roots_strictMono hL hc hn
  have hiff := logBethe_iff_roots hL hc hn
  refine ⟨⟨BetheSmooth.roots L n c, (hiff _).2 rfl, fun q hq => (hiff q).1 hq⟩,
    fun q hq => by rw [(hiff q).1 hq]; exact hmono, ?_, fun k => ?_⟩
  · intro q hq
    have hq' := (hiff q).1 hq
    subst hq'
    refine ⟨⟨rfl, sourceRoots_eq_comp_rev hL hc n, fun σ => finiteA_eq_coefficient _ _ σ,
      finiteB_roots_eq_wavefunction hL hc n⟩, ⟨finiteExt_continuous hc hn,
      fun σ x => finiteExt_permute n x σ, fun x hx => finiteExt_chamber hc hx,
      fun x => finiteExt_eq hc x⟩, ⟨integrableOn_chamber L c _, finiteZ_pos hL c hmono.injective⟩,
      ⟨finitePsi hc hn, finitePsi_ae hc hn, finitePsi_norm hc hn, finitePsi_eigen hc hn,
        by rw [origin_value hc hn]; exact ⟨by simpa using origin_pos hc hn, by simp⟩,
        fun θ h1 h2 => phase_unique hc hn θ h1 h2⟩,
      ⟨fun a => finiteB_diagonal c hmono.injective a, finiteExt_origin hc hn,
        origin_value hc hn, origin_pos hc hn⟩⟩
  · exact BetheLabels.correctedEquivArr_apply ⟨n, hn⟩ k

end Phase


/-! ### Analyticity of the chamber exponential integral `t ↦ ∫_{1>y_1>⋯>y_N>0} e^{i⟨t,y⟩} dy`
via the Banach algebra of bounded continuous functions on the chamber. -/

namespace ChamberExp

/-- The unit chamber `1 > y_1 > ⋯ > y_N > 0`. -/
abbrev Ch (M : ℕ) : Set (Fin M → ℝ) := chamber M 1

theorem isOpen_Ch (M : ℕ) : IsOpen (Ch M) := BetheEigenGlobal.isOpen_chamber M 1

abbrev X (M : ℕ) := ↥(Ch M)

/-- the finite measure of the chamber, as a measure on the subtype -/
def μX (M : ℕ) : Measure (X M) := Measure.comap Subtype.val (volume : Measure (Fin M → ℝ))

instance (M : ℕ) : IsFiniteMeasure (μX M) := by
  refine ⟨?_⟩
  unfold μX
  rw [Measure.comap_apply _ Subtype.val_injective (fun s hs => MeasurableSet.subtype_image (isOpen_Ch M).measurableSet hs) _ MeasurableSet.univ]
  have : Subtype.val '' (Set.univ : Set (X M)) ⊆ Icc (fun _ => (0:ℝ)) (fun _ => 1) := by
    rintro _ ⟨y, _, rfl⟩
    exact ⟨fun i => (y.2.2 i).1.le, fun i => (y.2.2 i).2.le⟩
  exact lt_of_le_of_lt (measure_mono this) (by
    rw [Real.volume_Icc_pi]; simp)

abbrev A (M : ℕ) := BoundedContinuousFunction (X M) ℂ

def uj (M : ℕ) (j : Fin M) : A M :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y : X M => Complex.I * ((y.1 j : ℝ) : ℂ))
    (continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_subtype_val))) 1 (by
      intro y
      have h := (y.2.2 j)
      simp [abs_of_pos h.1, h.2.le])

def Tlin (M : ℕ) : (Fin M → ℝ) →L[ℝ] A M :=
  ∑ j, (ContinuousLinearMap.proj j : (Fin M → ℝ) →L[ℝ] ℝ).smulRight (uj M j)

theorem Tlin_apply (M : ℕ) (t : Fin M → ℝ) (y : X M) :
    (Tlin M t) y = Complex.I * ((∑ j, t j * y.1 j : ℝ) : ℂ) := by
  simp [Tlin, uj, BoundedContinuousFunction.sum_apply, Finset.mul_sum, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring


def Lam (M : ℕ) : A M →L[ℝ] ℂ :=
  (MeasureTheory.L1.integralCLM (μ := μX M) (E := ℂ)).comp
    (BoundedContinuousFunction.toLp (E := ℂ) 1 (μX M) ℝ)

theorem Lam_apply (M : ℕ) (h : A M) : Lam M h = ∫ y, h y ∂(μX M) := by
  unfold Lam
  simp only [ContinuousLinearMap.comp_apply]
  rw [← MeasureTheory.L1.integral_eq, MeasureTheory.L1.integral_eq_integral]
  exact integral_congr_ae (BoundedContinuousFunction.coeFn_toLp 1 (μX M) ℝ h)

theorem exp_apply (M : ℕ) (h : A M) (y : X M) :
    (NormedSpace.exp h) y = Complex.exp (h y) := by
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) h
  have h2 := h1.mapL (BoundedContinuousFunction.evalCLM ℝ y)
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (h y)
  rw [← Complex.exp_eq_exp_ℂ] at h3
  have h4 : ∀ b, (BoundedContinuousFunction.evalCLM ℝ y) ((↑(b.factorial) : ℝ)⁻¹ • h ^ b) = ((↑(b.factorial) : ℝ)⁻¹ • h y ^ b) := by
    intro b; simp
  simp only [h4] at h2
  exact h2.unique h3

/-- the chamber exponential integral -/
def Gint (M : ℕ) (t : Fin M → ℝ) : ℂ :=
  ∫ y in Ch M, Complex.exp (Complex.I * ((∑ j, t j * y j : ℝ) : ℂ))

theorem Gint_eq (M : ℕ) (t : Fin M → ℝ) : Gint M t = Lam M (NormedSpace.exp (Tlin M t)) := by
  rw [Lam_apply]
  simp only [exp_apply, Tlin_apply]
  unfold Gint μX
  rw [← integral_subtype_comap (isOpen_Ch M).measurableSet]

theorem analyticAt_Gint (M : ℕ) (t0 : Fin M → ℝ) : AnalyticAt ℝ (Gint M) t0 := by
  have : Gint M = fun t => Lam M (NormedSpace.exp (Tlin M t)) := funext (Gint_eq M)
  rw [this]
  exact (Lam M).analyticAt _ |>.comp ((NormedSpace.exp_analytic (𝕂 := ℝ) (Tlin M t0)).comp ((Tlin M).analyticAt t0))


end ChamberExp

/-! ### Analytic implicit function theorem for the roots in `(L,c)` -/

namespace RootAnalytic
open QuantumNLS.BetheAdmission QuantumNLS.BetheRoots QuantumNLS.BetheSmooth
open QuantumNLS.BetheAdmission QuantumNLS.BetheRoots QuantumNLS.BetheSmooth

theorem analyticAt_arctan (x : ℝ) : AnalyticAt ℝ Real.arctan x := by
  have hz : (1 - (x : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hslit : (1 + (x : ℂ) * Complex.I) / (1 - (x : ℂ) * Complex.I) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hx : x = 0
    · left; simp [hx]
    · right
      rw [Complex.div_im]
      simp [Complex.normSq_apply]
      intro h
      have hd : (1 + x * x) ≠ 0 := (by nlinarith [mul_self_nonneg x] : 0 < 1 + x * x).ne'
      field_simp at h
      exact hx (by linarith)
  have h : AnalyticAt ℂ Complex.arctan (x : ℂ) := by
    unfold Complex.arctan
    refine analyticAt_const.mul (AnalyticAt.clog ?_ hslit)
    exact (analyticAt_const.add (analyticAt_id.mul analyticAt_const)).div
      (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)) hz
  have h2 : AnalyticAt ℝ (fun t : ℝ => Complex.arctan (t : ℂ)) x :=
    (h.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt x)
  have h3 : AnalyticAt ℝ (fun t : ℝ => (Complex.arctan (t : ℂ)).re) x :=
    (Complex.reCLM.analyticAt _).comp h2
  convert h3 using 1
  funext t
  rw [← Complex.ofReal_arctan, Complex.ofReal_re]


theorem logMap_analyticAt {N : ℕ} {c0 : ℝ} (hc : c0 ≠ 0) (L0 : ℝ) (q0 : Fin N → ℝ) :
    AnalyticAt ℝ (fun r : (ℝ × ℝ) × (Fin N → ℝ) => logMap r.1.1 r.1.2 r.2) ((L0, c0), q0) := by
  rw [analyticAt_pi_iff]
  intro i
  unfold logMap
  have hL : AnalyticAt ℝ (fun r : (ℝ × ℝ) × (Fin N → ℝ) => r.1.1) ((L0, c0), q0) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt _ |>.comp ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Fin N → ℝ)).analyticAt _)
  have hc' : AnalyticAt ℝ (fun r : (ℝ × ℝ) × (Fin N → ℝ) => r.1.2) ((L0, c0), q0) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt _ |>.comp ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Fin N → ℝ)).analyticAt _)
  have hq (j : Fin N) : AnalyticAt ℝ (fun r : (ℝ × ℝ) × (Fin N → ℝ) => r.2 j) ((L0, c0), q0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) j).analyticAt _ |>.comp
      ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Fin N → ℝ)).analyticAt _)
  refine hL.mul (hq i) |>.add (analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun j _ => ?_))
  exact (analyticAt_arctan _).comp ((hq i |>.sub (hq j)).div hc' hc)


/-- Real analytic dependence of the globally unique roots on both `L` and `c`, from the analytic
implicit function theorem at the (invertible) Gaudin derivative. -/
theorem root_analyticAt {N : ℕ} {L0 c0 : ℝ} (hL : 0 < L0) (hc : 0 < c0) (b : Fin N → ℝ) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => root p.1 b p.2) (L0, c0) := by
  let q0 := root L0 b c0
  let f := fun r : (ℝ × ℝ) × (Fin N → ℝ) => logMap r.1.1 r.1.2 r.2
  have hs : ContDiffAt ℝ ω f ((L0, c0), q0) := (logMap_analyticAt hc.ne' L0 q0).contDiffAt
  have hi : (fderiv ℝ f ((L0, c0), q0) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) (Fin N → ℝ)).IsInvertible := by
    have hd := ((hs.differentiableAt (by simp)).hasFDerivAt)
    have he : HasFDerivAt (fun x : Fin N → ℝ => ((L0, c0), x))
        (ContinuousLinearMap.inr ℝ (ℝ × ℝ) (Fin N → ℝ)) q0 := by
      convert (hasFDerivAt_const (L0, c0) q0).prodMk (hasFDerivAt_id q0) using 1 <;> ext <;> simp
    have := (hd.comp q0 he).unique (logMap_hasFDerivAt L0 hc q0)
    rw [this]
    exact gaudin_isInvertible hL hc q0
  let ψ := hs.implicitFunction (by simp) hi
  have he : (fun p : ℝ × ℝ => root p.1 b p.2) =ᶠ[𝓝 (L0, c0)] ψ := by
    filter_upwards [hs.eventually_apply_implicitFunction (by simp) hi,
      (isOpen_Ioi.prod isOpen_Ioi).mem_nhds (show (L0, c0) ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ) from ⟨hL, hc⟩)]
      with p hp hpos
    exact (eq_root hpos.1 hpos.2 (hp.trans (root_solves hL hc b))).symm
  exact ((hs.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq he).analyticAt


end RootAnalytic


theorem analyticAt_finiteA {M : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → ℝ} {q : E → Fin M → ℝ} {e0 : E}
    (hc : AnalyticAt ℝ c e0) (hq : AnalyticAt ℝ q e0)
    (hinj : Function.Injective (q e0)) (σ : Equiv.Perm (Fin M)) :
    AnalyticAt ℝ (fun e => finiteA (c e) (q e) σ) e0 := by
  unfold finiteA
  have hqj (j : Fin M) : AnalyticAt ℝ (fun e => q e j) e0 := analyticAt_pi_iff.1 hq j
  have hcc : AnalyticAt ℝ (fun e => ((c e : ℝ) : ℂ)) e0 := (Complex.ofRealCLM.analyticAt _).comp hc
  refine Finset.analyticAt_fun_prod _ fun j _ => Finset.analyticAt_fun_prod _ fun k hk => ?_
  have hjk : j < k := (Finset.mem_filter.1 hk).2
  have hd : AnalyticAt ℝ (fun e => ((q e (σ j) - q e (σ k) : ℝ) : ℂ)) e0 :=
    (Complex.ofRealCLM.analyticAt _).comp ((hqj (σ j)).sub (hqj (σ k)))
  refine analyticAt_const.sub ((analyticAt_const.mul hcc).div hd ?_)
  intro h
  have h' : q e0 (σ j) - q e0 (σ k) = 0 := by exact_mod_cast h
  have := hinj (sub_eq_zero.1 h')
  exact (ne_of_lt hjk) (σ.injective this)

theorem analyticAt_finiteB {M : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → ℝ} {q x : E → Fin M → ℝ} {e0 : E}
    (hc : AnalyticAt ℝ c e0) (hq : AnalyticAt ℝ q e0) (hx : AnalyticAt ℝ x e0)
    (hinj : Function.Injective (q e0)) :
    AnalyticAt ℝ (fun e => finiteB (c e) (q e) (x e)) e0 := by
  unfold finiteB
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  refine (analyticAt_finiteA hc hq hinj σ).mul ?_
  have hqj (j : Fin M) : AnalyticAt ℝ (fun e => q e j) e0 := analyticAt_pi_iff.1 hq j
  have hxj (j : Fin M) : AnalyticAt ℝ (fun e => x e j) e0 := analyticAt_pi_iff.1 hx j
  have hs : AnalyticAt ℝ (fun e => ∑ j, q e (σ j) * x e j) e0 :=
    Finset.analyticAt_fun_sum _ fun j _ => (hqj (σ j)).mul (hxj j)
  have hc' : AnalyticAt ℝ (fun e => Complex.I * ((∑ j, q e (σ j) * x e j : ℝ) : ℂ)) e0 :=
    analyticAt_const.mul ((Complex.ofRealCLM.analyticAt _).comp hs)
  exact (analyticAt_cexp.restrictScalars).comp hc'


open ChamberExp in
theorem smul_Ch {M : ℕ} {L : ℝ} (hL : 0 < L) : L • Ch M = chamber M L := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hL.ne']
  have hLi : 0 < L⁻¹ := inv_pos.2 hL
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h1 hij
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact lt_of_mul_lt_mul_left this hLi.le
    · have := h2 i
      simp only [Pi.smul_apply, smul_eq_mul] at this
      refine ⟨(mul_pos_iff_of_pos_left hLi).1 this.1, ?_⟩
      have := this.2
      rwa [inv_mul_lt_iff₀ hL, mul_one] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_lt_mul_of_pos_left (h1 hij) hLi
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact ⟨mul_pos hLi (h2 i).1, by rw [inv_mul_lt_iff₀ hL, mul_one]; exact (h2 i).2⟩

open ChamberExp in
theorem integral_chamber_scale {M : ℕ} {L : ℝ} (hL : 0 < L) (F : (Fin M → ℝ) → ℂ) :
    ∫ x in chamber M L, F x = ((L ^ M : ℝ) : ℂ) * ∫ y in Ch M, F (L • y) := by
  have h := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (volume : Measure (Fin M → ℝ)) F
    (Ch M) hL
  rw [smul_Ch hL, Module.finrank_fin_fun] at h
  rw [h, Complex.real_smul]
  have hp : (L ^ M : ℝ) ≠ 0 := (pow_pos hL M).ne'
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hp), one_mul]


open ChamberExp in
/-- complex-valued expansion of `Z`: `N! L^N Σ_{σ,τ} A_σ conj(A_τ) G(L (q∘σ - q∘τ))`. -/
def Zc (M : ℕ) (L c : ℝ) (q : Fin M → ℝ) : ℂ :=
  (M.factorial : ℂ) * ((L ^ M : ℝ) : ℂ) *
    ∑ σ : Equiv.Perm (Fin M), ∑ τ : Equiv.Perm (Fin M),
      (finiteA c q σ * conj (finiteA c q τ)) * Gint M (fun j => L * (q (σ j) - q (τ j)))

theorem finiteB_scaled_mul_conj {M : ℕ} (L c : ℝ) (q y : Fin M → ℝ) :
    finiteB c q (L • y) * conj (finiteB c q (L • y)) =
      ∑ σ : Equiv.Perm (Fin M), ∑ τ : Equiv.Perm (Fin M),
        (finiteA c q σ * conj (finiteA c q τ)) *
          Complex.exp (Complex.I * ((∑ j, (L * (q (σ j) - q (τ j))) * y j : ℝ) : ℂ)) := by
  unfold finiteB
  rw [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  rw [map_mul, ← Complex.exp_conj]
  have hexp : Complex.exp (Complex.I * ((∑ j, (L * (q (σ j) - q (τ j))) * y j : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((∑ j, q (σ j) * (L • y) j : ℝ) : ℂ)) *
        Complex.exp ((starRingEnd ℂ) (Complex.I * ((∑ j, q (τ j) * (L • y) j : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    have hr : (∑ j, (L * (q (σ j) - q (τ j))) * y j) =
        (∑ j, q (σ j) * (L • y) j) - ∑ j, q (τ j) * (L • y) j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hr]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hexp]
  ring

theorem integrableOn_Ch_of_continuous {M : ℕ} {f : (Fin M → ℝ) → ℂ} (hf : Continuous f) :
    IntegrableOn f (ChamberExp.Ch M) := by
  have h : IntegrableOn f (Icc (fun _ => (0 : ℝ)) (fun _ => 1)) volume :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  exact h.mono_set (fun x hx => ⟨fun i => (hx.2 i).1.le, fun i => (hx.2 i).2.le⟩)

open ChamberExp in
theorem finiteZ_eq_Zc {M : ℕ} {L : ℝ} (hL : 0 < L) (c : ℝ) (q : Fin M → ℝ) :
    (finiteZ L c q : ℂ) = Zc M L c q := by
  unfold finiteZ Zc
  have h1 : (((∫ x in chamber M L, ‖finiteB c q x‖ ^ 2 : ℝ)) : ℂ) =
      ∫ x in chamber M L, finiteB c q x * conj (finiteB c q x) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with x
    rw [Complex.mul_conj']
    push_cast
    rfl
  push_cast
  rw [h1, integral_chamber_scale hL, mul_assoc]
  congr 2
  · push_cast; rfl
  simp only [finiteB_scaled_mul_conj]
  rw [integral_finsetSum _ (fun σ _ => ?_)]
  · apply Finset.sum_congr rfl
    intro σ _
    rw [integral_finsetSum _ (fun τ _ => ?_)]
    · apply Finset.sum_congr rfl
      intro τ _
      rw [integral_const_mul]
      rfl
    · apply integrableOn_Ch_of_continuous
      fun_prop
  · apply integrable_finsetSum
    intro τ _
    apply integrableOn_Ch_of_continuous
    fun_prop


theorem analyticAt_Zc {M : ℕ} {b : Fin M → ℝ} {L0 c0 : ℝ}
    (hinj : Function.Injective (BetheSmooth.root L0 b c0)) (hL : 0 < L0) (hc : 0 < c0) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => Zc M p.1 p.2 (BetheSmooth.root p.1 b p.2)) (L0, c0) := by
  have hq : AnalyticAt ℝ (fun p : ℝ × ℝ => BetheSmooth.root p.1 b p.2) (L0, c0) :=
    RootAnalytic.root_analyticAt hL hc b
  have hc' : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) (L0, c0) :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt _
  have hL' : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) (L0, c0) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt _
  have hqj (j : Fin M) : AnalyticAt ℝ (fun p : ℝ × ℝ => BetheSmooth.root p.1 b p.2 j) (L0, c0) :=
    analyticAt_pi_iff.1 hq j
  unfold Zc
  refine (analyticAt_const.mul ((Complex.ofRealCLM.analyticAt _).comp (hL'.pow M))).mul ?_
  refine Finset.analyticAt_fun_sum _ fun σ _ => Finset.analyticAt_fun_sum _ fun τ _ => ?_
  have hA (ρ : Equiv.Perm (Fin M)) : AnalyticAt ℝ
      (fun p : ℝ × ℝ => finiteA p.2 (BetheSmooth.root p.1 b p.2) ρ) (L0, c0) :=
    analyticAt_finiteA hc' hq hinj ρ
  have hAc : AnalyticAt ℝ
      (fun p : ℝ × ℝ => conj (finiteA p.2 (BetheSmooth.root p.1 b p.2) τ)) (L0, c0) :=
    (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (hA τ)
  have ht : AnalyticAt ℝ (fun p : ℝ × ℝ => fun j => p.1 * (BetheSmooth.root p.1 b p.2 (σ j) -
      BetheSmooth.root p.1 b p.2 (τ j))) (L0, c0) :=
    analyticAt_pi_iff.2 fun j => hL'.mul ((hqj (σ j)).sub (hqj (τ j)))
  exact ((hA σ).mul hAc).mul ((ChamberExp.analyticAt_Gint M _).comp ht)

theorem analyticAt_finiteZ_root {M : ℕ} {b : Fin M → ℝ} {L0 c0 : ℝ}
    (hinj : Function.Injective (BetheSmooth.root L0 b c0)) (hL : 0 < L0) (hc : 0 < c0) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => finiteZ p.1 p.2 (BetheSmooth.root p.1 b p.2)) (L0, c0) := by
  have h : AnalyticAt ℝ (fun p : ℝ × ℝ => (Zc M p.1 p.2 (BetheSmooth.root p.1 b p.2)).re) (L0, c0) :=
    (Complex.reCLM.analyticAt _).comp (analyticAt_Zc hinj hL hc)
  refine h.congr ?_
  filter_upwards [(isOpen_Ioi (a := (0:ℝ))).preimage continuous_fst |>.mem_nhds
    (show (L0, c0) ∈ (fun p : ℝ × ℝ => p.1) ⁻¹' Set.Ioi (0:ℝ) from hL)] with p hp
  have := finiteZ_eq_Zc (M := M) hp (p.2) (BetheSmooth.root p.1 b p.2)
  rw [← this, Complex.ofReal_re]

theorem analyticAt_sqrt {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ Real.sqrt x := by
  have h : AnalyticAt ℝ (fun y : ℝ => Real.exp (Real.log y * (1 / 2))) x :=
    ((analyticAt_log hx).mul analyticAt_const).rexp'
  refine h.congr ?_
  filter_upwards [lt_mem_nhds hx] with y hy
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]


/-! ### Real-analytic dependence on `(L,c)` -/

/-- The parameter domain `L > 0, c > 0`. -/
def paramDomain : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2}

theorem isOpen_paramDomain : IsOpen paramDomain :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)

/-- The printed normalized wave `Z^{-1/2} B` as a formula in `(L,c,x)` (chamber coordinates). -/
def psiFormula {M : ℕ} (n : Fin M → ℤ) (L c : ℝ) (x : Fin M → ℝ) : ℂ :=
  ((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) *
    finiteB c (BetheSmooth.roots L n c) x

/-- `Ψ^d(L y)` for the symmetric periodic extension, at the point of the unit torus with
representative `y`, for arbitrary real `(L,c)` (the extension acts on `x = L y` reduced to
`[0,L)` as `L · fract y`). -/
def psiUnit {M : ℕ} (n : Fin M → ℤ) (L c : ℝ) (y : Fin M → ℝ) : ℂ :=
  ((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) *
    finiteB c (BetheSmooth.roots L n c) (decreasing (fun i => L * Int.fract (y i)))

theorem analyticAt_psiFormula {M : ℕ} {n : Fin M → ℤ} (hn : Monotone n)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {e0 : E} {Lf cf : E → ℝ}
    {xf : E → Fin M → ℝ} (hL : 0 < Lf e0) (hc : 0 < cf e0)
    (hLa : AnalyticAt ℝ Lf e0) (hca : AnalyticAt ℝ cf e0) (hxa : AnalyticAt ℝ xf e0) :
    AnalyticAt ℝ (fun e => psiFormula n (Lf e) (cf e) (xf e)) e0 := by
  have hP : AnalyticAt ℝ (fun e => (Lf e, cf e)) e0 := hLa.prod hca
  have hinj : Function.Injective (BetheSmooth.roots (Lf e0) n (cf e0)) :=
    (roots_strictMono hL hc hn).injective
  have hr : AnalyticAt ℝ (fun e => BetheSmooth.roots (Lf e) n (cf e)) e0 :=
    (RootAnalytic.root_analyticAt (b := fun i => 2 * Real.pi * BetheAdmission.quantumNumbers n i)
      hL hc).fun_comp_of_eq hP rfl
  have hZ : AnalyticAt ℝ (fun e => finiteZ (Lf e) (cf e) (BetheSmooth.roots (Lf e) n (cf e))) e0 :=
    (analyticAt_finiteZ_root (b := fun i => 2 * Real.pi * BetheAdmission.quantumNumbers n i)
      hinj hL hc).fun_comp_of_eq hP rfl
  have hZpos := finiteZ_pos hL (cf e0) hinj
  have hs : AnalyticAt ℝ (fun e => Real.sqrt
      (finiteZ (Lf e) (cf e) (BetheSmooth.roots (Lf e) n (cf e)))) e0 :=
    (analyticAt_sqrt hZpos).fun_comp_of_eq hZ rfl
  have hs' : AnalyticAt ℝ (fun e => ((Real.sqrt
      (finiteZ (Lf e) (cf e) (BetheSmooth.roots (Lf e) n (cf e))))⁻¹ : ℂ)) e0 := by
    have h1 : AnalyticAt ℝ (fun e => ((Real.sqrt
        (finiteZ (Lf e) (cf e) (BetheSmooth.roots (Lf e) n (cf e))) : ℝ) : ℂ)) e0 :=
      (Complex.ofRealCLM.analyticAt _).comp hs
    exact h1.inv (by exact_mod_cast (Real.sqrt_pos.2 hZpos).ne')
  exact hs'.mul (analyticAt_finiteB hca hr hxa hinj)

theorem decreasing_smul {M : ℕ} {L : ℝ} (hL : 0 < L) (x : Fin M → ℝ) :
    decreasing (L • x) = L • decreasing x := by
  have hanti : Antitone ((L • x) ∘ Tuple.sort (α := ℝᵒᵈ) x) := by
    intro i j hij
    have := decreasing_antitone x hij
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left this hL.le
  rw [decreasing_eq_permute (L • x) (Tuple.sort (α := ℝᵒᵈ) x) hanti]
  rfl

theorem equivIco_mul_coe {L : ℝ} [Fact (0 < L)] (y : ℝ) :
    (AddCircle.equivIco L 0 ((L * y : ℝ) : AddCircle L) : ℝ) = L * Int.fract y := by
  have hL : 0 < L := Fact.out
  have hmem : L * Int.fract y ∈ Set.Ico (0 : ℝ) (0 + L) := by
    refine ⟨mul_nonneg hL.le (Int.fract_nonneg y), ?_⟩
    rw [zero_add]
    exact mul_lt_of_lt_one_right hL (Int.fract_lt_one y)
  have hc : ((L * y : ℝ) : AddCircle L) = ((L * Int.fract y : ℝ) : AddCircle L) := by
    have h1 : L * y = L * Int.fract y + ((⌊y⌋ : ℤ) : ℝ) * L := by
      rw [← Int.self_sub_floor]; ring
    rw [h1, AddCircle.coe_add]
    have h2 : ((((⌊y⌋ : ℤ) : ℝ) * L : ℝ) : AddCircle L) = 0 :=
      (AddCircle.coe_eq_zero_iff L).2 ⟨⌊y⌋, by simp [zsmul_eq_mul]⟩
    rw [h2, add_zero]
  rw [hc]
  exact AddCircle.equivIco_coe_of_mem (p := L) (a := 0) hmem


/-- **Real-analytic dependence of the finite convention on `(L, c)`** (all `L > 0`, `c > 0`),
with periods identified with the unit torus via `x = L y`: the roots, `Z`, the normalized wave
`Ψ^d(L y) = Z^{-1/2} B(L y)` (jointly in `(L,c,y)` as a chamber formula; and, for every fixed
point `y` of the unit torus, the symmetric periodic extension, in `(L,c)`). -/
theorem finite_phase_analytic {M : ℕ} {n : Fin M → ℤ} (hn : Monotone n) :
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => BetheSmooth.roots p.1 n p.2) paramDomain ∧
    AnalyticOnNhd ℝ (fun p : ℝ × ℝ => finiteZ p.1 p.2 (BetheSmooth.roots p.1 n p.2))
      paramDomain ∧
    (∀ p ∈ paramDomain, 0 < finiteZ p.1 p.2 (BetheSmooth.roots p.1 n p.2)) ∧
    AnalyticOnNhd ℝ (fun r : (ℝ × ℝ) × (Fin M → ℝ) => psiFormula n r.1.1 r.1.2 (r.1.1 • r.2))
      (paramDomain ×ˢ Set.univ) ∧
    (∀ y : Fin M → ℝ,
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => psiUnit n p.1 p.2 y) paramDomain) := by
  have hb (p : ℝ × ℝ) (hp : p ∈ paramDomain) : Function.Injective (BetheSmooth.root p.1
      (fun i => 2 * Real.pi * BetheAdmission.quantumNumbers n i) p.2) :=
    (roots_strictMono hp.1 hp.2 hn).injective
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun r hr => ?_, fun y p hp => ?_⟩
  · exact RootAnalytic.root_analyticAt (b := fun i => 2 * Real.pi * BetheAdmission.quantumNumbers n i)
      hp.1 hp.2
  · exact analyticAt_finiteZ_root (b := fun i => 2 * Real.pi * BetheAdmission.quantumNumbers n i)
      (hb p hp) hp.1 hp.2
  · exact finiteZ_pos hp.1 p.2 (hb p hp)
  · have hL : AnalyticAt ℝ (fun r : (ℝ × ℝ) × (Fin M → ℝ) => r.1.1) r :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt _ |>.comp
        ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Fin M → ℝ)).analyticAt _)
    have hc : AnalyticAt ℝ (fun r : (ℝ × ℝ) × (Fin M → ℝ) => r.1.2) r :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt _ |>.comp
        ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Fin M → ℝ)).analyticAt _)
    have hy : AnalyticAt ℝ (fun r : (ℝ × ℝ) × (Fin M → ℝ) => r.2) r :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Fin M → ℝ)).analyticAt _
    exact analyticAt_psiFormula hn hr.1.1 hr.1.2 hL hc (hL.smul hy)
  · have hL : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1) p := (ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt _
    have hc : AnalyticAt ℝ (fun p : ℝ × ℝ => p.2) p := (ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt _
    set w : Fin M → ℝ := decreasing (fun i => Int.fract (y i)) with hw
    have h := analyticAt_psiFormula (M := M) hn (e0 := p) (Lf := fun p : ℝ × ℝ => p.1)
      (cf := fun p : ℝ × ℝ => p.2) (xf := fun p : ℝ × ℝ => p.1 • w) hp.1 hp.2 hL hc
      (hL.smul analyticAt_const)
    refine h.congr ?_
    filter_upwards [(isOpen_paramDomain.mem_nhds hp)] with q hq
    have hdec : decreasing (fun i => q.1 * Int.fract (y i)) = q.1 • w := by
      rw [← decreasing_smul hq.1]
      rfl
    simp only [psiFormula, psiUnit, hdec]


/-- **Identification with the actual torus extension**: for `L > 0`, `psiUnit n L c y` is
`Z^{-1/2}` times the symmetric periodic extension `finiteExt` at the point of the circle
product `(ℝ/Lℤ)^N` corresponding to the point `y` of the unit torus `(ℝ/ℤ)^N` (`x = L y`). -/
theorem psiUnit_eq_finiteExt {M : ℕ} {n : Fin M → ℤ} {L c : ℝ} [Fact (0 < L)] (hc : 0 < c)
    (y : Fin M → ℝ) :
    psiUnit n L c y = ((Real.sqrt (finiteZ L c (BetheSmooth.roots L n c)))⁻¹ : ℂ) *
      finiteExt L c n (fun i => ((L * y i : ℝ) : AddCircle L)) := by
  unfold psiUnit
  congr 1
  rw [finiteExt_eq hc]
  congr 2
  funext i
  exact (equivIco_mul_coe (L := L) (y i)).symm

end QuantumNLS.FiniteDiagonalPhase

#print axioms QuantumNLS.FiniteDiagonalPhase.lagrange_sum
#print axioms QuantumNLS.FiniteDiagonalPhase.cf
#print axioms QuantumNLS.FiniteDiagonalPhase.cf_succ
#print axioms QuantumNLS.FiniteDiagonalPhase.prod_erase_eq
#print axioms QuantumNLS.FiniteDiagonalPhase.sum_cf
#print axioms QuantumNLS.FiniteDiagonalPhase.printedLabel
#print axioms QuantumNLS.FiniteDiagonalPhase.LogBethe
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteA
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteB
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteZ
#print axioms QuantumNLS.FiniteDiagonalPhase.printedLabel_eq
#print axioms QuantumNLS.FiniteDiagonalPhase.labelsOf_correctedInt
#print axioms QuantumNLS.FiniteDiagonalPhase.logBethe_iff_roots
#print axioms QuantumNLS.FiniteDiagonalPhase.roots_strictMono
#print axioms QuantumNLS.FiniteDiagonalPhase.coordinateAnsatz_comp_perm
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteB_eq_coordinateAnsatz
#print axioms QuantumNLS.FiniteDiagonalPhase.sourceRoots_eq_comp_rev
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteB_roots_eq_wavefunction
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteA_eq_coefficient
#print axioms QuantumNLS.FiniteDiagonalPhase.sum_finiteA
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteB_diagonal
#print axioms QuantumNLS.FiniteDiagonalPhase.permChamber
#print axioms QuantumNLS.FiniteDiagonalPhase.permChamber_eq_preimage
#print axioms QuantumNLS.FiniteDiagonalPhase.measurePreserving_permute
#print axioms QuantumNLS.FiniteDiagonalPhase.measurableSet_chamber
#print axioms QuantumNLS.FiniteDiagonalPhase.measurableSet_permChamber
#print axioms QuantumNLS.FiniteDiagonalPhase.permChamber_subset_cube
#print axioms QuantumNLS.FiniteDiagonalPhase.permChamber_disjoint
#print axioms QuantumNLS.FiniteDiagonalPhase.cube_integral_decreasing
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteExt
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteExt_continuous
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteExt_permute
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteExt_chamber
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteExt_eq
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteZ_eq_norm_sq
#print axioms QuantumNLS.FiniteDiagonalPhase.integrableOn_chamber
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteZ_pos
#print axioms QuantumNLS.FiniteDiagonalPhase.sum_sq_roots_eq_energy
#print axioms QuantumNLS.FiniteDiagonalPhase.finitePsi
#print axioms QuantumNLS.FiniteDiagonalPhase.norm_valSym_wave
#print axioms QuantumNLS.FiniteDiagonalPhase.finitePsi_norm
#print axioms QuantumNLS.FiniteDiagonalPhase.finitePsi_ae
#print axioms QuantumNLS.FiniteDiagonalPhase.finitePsi_eigen
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteExt_origin
#print axioms QuantumNLS.FiniteDiagonalPhase.IsPositiveReal
#print axioms QuantumNLS.FiniteDiagonalPhase.origin_value
#print axioms QuantumNLS.FiniteDiagonalPhase.origin_pos
#print axioms QuantumNLS.FiniteDiagonalPhase.phase_unique
#print axioms QuantumNLS.FiniteDiagonalPhase.finite_diagonal_phase
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.Ch
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.isOpen_Ch
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.X
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.μX
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.A
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.uj
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.Tlin
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.Tlin_apply
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.Lam
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.Lam_apply
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.exp_apply
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.Gint
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.Gint_eq
#print axioms QuantumNLS.FiniteDiagonalPhase.ChamberExp.analyticAt_Gint
#print axioms QuantumNLS.FiniteDiagonalPhase.RootAnalytic.analyticAt_arctan
#print axioms QuantumNLS.FiniteDiagonalPhase.RootAnalytic.logMap_analyticAt
#print axioms QuantumNLS.FiniteDiagonalPhase.RootAnalytic.root_analyticAt
#print axioms QuantumNLS.FiniteDiagonalPhase.analyticAt_finiteA
#print axioms QuantumNLS.FiniteDiagonalPhase.analyticAt_finiteB
#print axioms QuantumNLS.FiniteDiagonalPhase.smul_Ch
#print axioms QuantumNLS.FiniteDiagonalPhase.integral_chamber_scale
#print axioms QuantumNLS.FiniteDiagonalPhase.Zc
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteB_scaled_mul_conj
#print axioms QuantumNLS.FiniteDiagonalPhase.integrableOn_Ch_of_continuous
#print axioms QuantumNLS.FiniteDiagonalPhase.finiteZ_eq_Zc
#print axioms QuantumNLS.FiniteDiagonalPhase.analyticAt_Zc
#print axioms QuantumNLS.FiniteDiagonalPhase.analyticAt_finiteZ_root
#print axioms QuantumNLS.FiniteDiagonalPhase.analyticAt_sqrt
#print axioms QuantumNLS.FiniteDiagonalPhase.paramDomain
#print axioms QuantumNLS.FiniteDiagonalPhase.isOpen_paramDomain
#print axioms QuantumNLS.FiniteDiagonalPhase.psiFormula
#print axioms QuantumNLS.FiniteDiagonalPhase.psiUnit
#print axioms QuantumNLS.FiniteDiagonalPhase.analyticAt_psiFormula
#print axioms QuantumNLS.FiniteDiagonalPhase.decreasing_smul
#print axioms QuantumNLS.FiniteDiagonalPhase.equivIco_mul_coe
#print axioms QuantumNLS.FiniteDiagonalPhase.finite_phase_analytic
#print axioms QuantumNLS.FiniteDiagonalPhase.psiUnit_eq_finiteExt
