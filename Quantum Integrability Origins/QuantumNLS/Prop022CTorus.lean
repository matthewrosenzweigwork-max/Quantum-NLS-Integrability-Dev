import Mathlib
import QuantumNLS.Prop022CCanon
import QuantumNLS.Prop022AWeyl
import QuantumNLS.Ext006StoneGeneratorR44a
import QuantumNLS.Ext006FieldMaximalityR44a
import QuantumNLS.Ext006WeylScalingR44a
import QuantumNLS.Ext006SourceWeylR44a

/-! PROP-022 route A, round 4, stage C3: the torus identification of the H-level canonical operators.

On the physical carrier `K = L²(𝕋_L)` (`FockSpace K = Fock L`, definitionally) this module proves:

* `annS_power`: the intrinsic annihilation acts on power vectors as `√(n+1) ⟨f,u⟩ u^{⊗n}` (generic);
* `annMap_eq`: the frozen coordinate annihilation `A (ĝ)` on a sector equals the intrinsic `annS g`
  (through the occupation coordinates `secEmb`);
* `C_emb`: the frozen coordinate creation `C (ĝ)` equals the intrinsic `creS g`;
* `phi_Zgen`: on the finite-particle core, `Phi ((a*(g) - a(g)) x) = (C ĝ - A ĝ)(Phi x)`, with
  `printedWeyl_generator` this gives `Phi ((a*(g) - a(g)) x) = i · field(-i g)(Phi x)`;
* `core_iff`: finite-particle vectors in sector coordinates are exactly the bounded-particle core
  vectors of the frozen Stone theory;
* the one-parameter group `WK g r = printedWeyl (r g)`, its group law, strong continuity, and the
  generator identification (sequential closure of the graph of `a*(g) - a(g)` on the core). -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology
open Filter

namespace QuantumNLS.Prop022CTorus
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022GClassical
open QuantumNLS.Prop022CTensorIso QuantumNLS.Prop022CCanon
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Occupation Ext006KernelHilbertSchmidt Prop022TensorCompressionR115
open Ext006PhysFockCoord Prop022ACoherent Prop022AWeyl Prop022OVacuum

/-! ### Generic computations on power vectors -/

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma split_htpow (n : ℕ) (u : E) :
    splitIsometry (𝕜 := ℂ) (E := E) n 1 (htpow (n + 1) u : HilbertTensorPower ℂ E (n + 1)) =
      htmul (htpow n u : HilbertTensorPower ℂ E n) (htpow 1 u : HilbertTensorPower ℂ E 1) := by
  have h : (fun _ : Fin (n + 1) => u) =
      Fin.append (fun _ : Fin n => u) (fun _ : Fin 1 => u) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  unfold htpow
  rw [h, splitIsometry_ptprod_append]

lemma inner_htpow_one (f u : E) :
    ⟪(htpow 1 f : HilbertTensorPower ℂ E 1), (htpow 1 u : HilbertTensorPower ℂ E 1)⟫_ℂ =
      ⟪f, u⟫_ℂ := by
  have h := IntrinsicContact.inner_htpow (E := E) 1 f u
  rwa [pow_one] at h

lemma creT_adj_power (f u : E) (n : ℕ) :
    ContinuousLinearMap.adjoint (creT f n) (htpow (n + 1) u : HilbertTensorPower ℂ E (n + 1)) =
      (((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * ⟪f, u⟫_ℂ) • (htpow n u : HilbertTensorPower ℂ E n) := by
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, creT, smul_apply, inner_smul_left,
    Complex.conj_ofReal, insLast_apply, Prop022CTensorIso.inner_symm_left, split_htpow, inner_htmul,
    inner_smul_right]
  erw [inner_htpow_one]
  ring

/-- The intrinsic annihilation on power vectors. -/
theorem annS_power (f u : E) (n : ℕ) :
    annS f n (powerH (n + 1) u) =
      (((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * ⟪f, u⟫_ℂ) • powerH n u := by
  rw [annS, creS, secOf_adjoint_apply]
  have h1 : ((powerH (n + 1) u : SymSector ℂ E (n + 1)) : HilbertTensorPower ℂ E (n + 1)) =
      htpow (n + 1) u := rfl
  rw [h1, creT_adj_power, map_smul, symProjToSector_eq]
  congr 1
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (powerH n u)

end Generic

/-! ### Torus: coordinate annihilation and creation -/

variable {L : ℝ} [Fact (0 < L)]

/-- `secEmb n` as a continuous linear map. -/
def embCLM (n : ℕ) : HN L n →L[ℂ] OF :=
  LinearMap.mkContinuous
    { toFun := secEmb n
      map_add' := emb_add n
      map_smul' := fun c x => emb_smul n c x } 1 (fun x => by change ‖secEmb n x‖ ≤ 1 * ‖x‖; rw [one_mul, norm_emb])

lemma embCLM_apply (n : ℕ) (x : HN L n) : embCLM n x = secEmb n x := rfl

lemma inner_ghat (g u : L2T L) : ⟪ghat g, ghat u⟫_ℂ = ⟪g, u⟫_ℂ :=
  LinearIsometryEquiv.inner_map_map _ g u

/-- **The frozen coordinate annihilation is the intrinsic one.** -/
theorem annMap_eq (g : L2T L) (n : ℕ) (y : HN L (n + 1)) :
    annMap (ghat g) n y = secEmb n (annS g n y) := by
  have hext : annMap (ghat g) n = (embCLM n).comp (annS g n) := by
    apply ContinuousLinearMap.ext_on (dense_powers (n + 1))
    rintro _ ⟨u, rfl⟩
    change annMap (ghat g) n (power (n + 1) u) = secEmb n (annS g n (powerH (n + 1) u))
    rw [annMap_apply, ann_emb_power, annS_power, emb_smul, inner_ghat]
    rfl
  exact congrArg (fun F => F y) hext

lemma inner_emb_self (a : ℕ) (y x : HN L a) : ⟪secEmb a y, secEmb a x⟫_ℂ = ⟪y, x⟫_ℂ := by
  unfold secEmb
  rw [LinearIsometryEquiv.inner_map_map, lp.inner_single_left (𝕜 := ℂ), lp.single_apply_self]

lemma inner_emb_ne {a b : ℕ} (h : a ≠ b) (y : HN L a) (x : HN L b) :
    ⟪secEmb a y, secEmb b x⟫_ℂ = 0 := by
  unfold secEmb
  rw [LinearIsometryEquiv.inner_map_map, lp.inner_single_left (𝕜 := ℂ), lp.single_apply_ne _ _ _ h,
    inner_zero_right]

/-- **The frozen coordinate creation is the intrinsic one.** -/
theorem C_emb (g : L2T L) (n : ℕ) (x : HN L n) :
    (Ext006SmoothOperatorsR34a.C (ghat g) (embD n x)).1 = secEmb (n + 1) (creS g n x) := by
  apply Ext006ClosedFieldGraphsR36a.ket_total
  intro k
  rw [ket_eq_emb (L := L) k]
  have key : ∀ (m : ℕ) (y : HN L m),
      ⟪secEmb m y, (Ext006SmoothOperatorsR34a.C (ghat g) (embD n x)).1⟫_ℂ =
        ⟪secEmb m y, secEmb (n + 1) (creS g n x)⟫_ℂ := by
    intro m y
    have h1 := Ext006FieldBoundsR42a.C_adjoint (ghat g) (embD m y) (embD n x)
    change ⟪(embD m y).1, _⟫_ℂ = _
    rw [h1]
    cases m with
    | zero =>
      rw [show (Ext006SmoothOperatorsR34a.A (ghat g) (embD 0 y)).1 = 0 from ann_emb_zero _ _,
        inner_zero_left, inner_emb_ne (by omega : 0 ≠ n + 1)]
    | succ j =>
      have hA : (Ext006SmoothOperatorsR34a.A (ghat g) (embD (j + 1) y)).1 =
          secEmb j (annS g j y) := (annMap_apply (ghat g) j y).symm.trans (annMap_eq g j y)
      rw [hA]
      change ⟪secEmb j (annS g j y), secEmb n x⟫_ℂ = _
      by_cases hj : j = n
      · subst hj
        rw [inner_emb_self, inner_emb_self]
        exact ContinuousLinearMap.adjoint_inner_left (creS g j) x y
      · rw [inner_emb_ne hj, inner_emb_ne (by omega : j + 1 ≠ n + 1)]
  exact key _ _

/-! ### Finite-particle vectors in occupation coordinates -/

lemma phi_eq_sum (y : Fock L) (N : ℕ) (hy : ∀ n, N < n → y n = 0) :
    Phi y = ∑ n ∈ Finset.range (N + 1), secEmb n (y n) := by
  have hs := lp.hasSum_single (p := 2) (by norm_num) y
  have h2 : HasSum (fun n : ℕ => (lp.single 2 n (y n) : Fock L))
      (∑ n ∈ Finset.range (N + 1), (lp.single 2 n (y n) : Fock L)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    have hn' : N < n := by simpa using hn
    simp [hy n hn']
  have h3 := hs.unique h2
  calc Phi y = Phi (∑ n ∈ Finset.range (N + 1), (lp.single 2 n (y n) : Fock L)) :=
        congrArg Phi h3
    _ = _ := by rw [map_sum]; rfl

/-- The occupation-coordinate vector of a finite-particle vector (smooth). -/
def embDfin (x : Dfin (L2T L)) : Ext006SmoothOperatorsR34a.D :=
  ⟨Phi (x : Fock L), by
    obtain ⟨N, hN⟩ := x.2
    rw [phi_eq_sum _ N hN]
    exact Submodule.sum_mem _ (fun n _ => emb_smooth n _)⟩

lemma embDfin_coe (x : Dfin (L2T L)) : (embDfin x).1 = Phi (x : Fock L) := rfl

lemma embDfin_eq_sum (x : Dfin (L2T L)) (N : ℕ) (hN : ∀ n, N < n → (x : Fock L) n = 0) :
    embDfin x = ∑ n ∈ Finset.range (N + 1), embD n ((x : Fock L) n) := by
  apply Subtype.ext
  rw [embDfin_coe, phi_eq_sum _ N hN, Submodule.coe_sum]
  rfl

lemma secEmb_zero (n : ℕ) : secEmb (L := L) n 0 = 0 := by
  unfold secEmb
  simp

/-- `Phi (a*(g) x)` is the frozen creation applied to `Phi x`. -/
theorem phi_creF (g : L2T L) (x : Dfin (L2T L)) :
    Phi (creF g x : Fock L) = (Ext006SmoothOperatorsR34a.C (ghat g) (embDfin x)).1 := by
  obtain ⟨N, hN⟩ := x.2
  have hb : ∀ n, N + 1 < n → (creF g x : Fock L) n = 0 := by
    intro n hn
    cases n with
    | zero => omega
    | succ k =>
      rw [creF_succ]
      have h := hN k (by omega)
      change creS g k ((x : Fock L) k) = 0
      rw [h, map_zero]
  rw [phi_eq_sum _ (N + 1) hb, Finset.sum_range_succ', creF_zero, secEmb_zero, add_zero,
    embDfin_eq_sum x N hN, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [creF_succ, C_emb]

/-- `Phi (a(g) x)` is the frozen annihilation applied to `Phi x`. -/
theorem phi_annF (g : L2T L) (x : Dfin (L2T L)) :
    Phi (annF g x : Fock L) = (Ext006SmoothOperatorsR34a.A (ghat g) (embDfin x)).1 := by
  obtain ⟨N, hN⟩ := x.2
  have hb : ∀ n, N < n → (annF g x : Fock L) n = 0 := by
    intro n hn
    rw [annF_apply, hN (n + 1) (by omega), map_zero]
  rw [phi_eq_sum _ N hb, embDfin_eq_sum x N hN, map_sum, Submodule.coe_sum,
    Finset.sum_range_succ, Finset.sum_range_succ' (fun k => (Ext006SmoothOperatorsR34a.A (ghat g)
      (embD k ((x : Fock L) k))).1)]
  have hlast : secEmb N ((annF g x : Fock L) N) = 0 := by
    rw [annF_apply, hN (N + 1) (by omega), map_zero, secEmb_zero]
  rw [hlast, add_zero,
    show (Ext006SmoothOperatorsR34a.A (ghat g) (embD 0 ((x : Fock L) 0))).1 = 0 from
      ann_emb_zero _ _, add_zero]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [annF_apply]
  exact ((annMap_apply (ghat g) k _).symm.trans (annMap_eq g k _)).symm

/-- **The core identity.** `a*(g) - a(g)` on the finite-particle core is `C ĝ - A ĝ` in
occupation coordinates. -/
theorem phi_Zgen (g : L2T L) (x : Dfin (L2T L)) :
    Phi (Zgen g x : Fock L) =
      (Ext006SmoothOperatorsR34a.C (ghat g) (embDfin x)).1 -
        (Ext006SmoothOperatorsR34a.A (ghat g) (embDfin x)).1 := by
  rw [Zgen_apply, map_sub, phi_creF, phi_annF]

/-- `Phi ((a*(g) - a(g)) x) = i · field(-i g) (Phi x)`, the frozen printed generator. -/
theorem phi_Zgen_field (g : L2T L) (x : Dfin (L2T L)) :
    Phi (Zgen g x : Fock L) =
      Complex.I • (Ext006StrongFieldR41a.field ((physicalBasis L).repr ((-Complex.I) • g))
        (embDfin x)).1 := by
  rw [printedWeyl_generator, phi_Zgen]
  rfl

/-! ### Core vectors are finite-particle vectors -/

lemma embDfin_core (x : Dfin (L2T L)) :
    embDfin x ∈ Ext006BoundedExponentialR43a.particleDomain := by
  obtain ⟨N, hN⟩ := x.2
  refine ⟨N, fun m hm => ?_⟩
  change Phi (x : Fock L) m = 0
  change (occupationCoefficient (freeBasis L (total m)) ((x : Fock L) (total m))) ⟨m, rfl⟩ = 0
  rw [hN (total m) hm, map_zero]
  rfl

lemma sector_zero_of_coeff (y : Fock L) (n : ℕ) (h : ∀ m : Occ, total m = n → Phi y m = 0) :
    y n = 0 := by
  apply (occupationCoefficient (freeBasis L n)).injective
  rw [map_zero]
  apply lp.ext
  funext a
  obtain ⟨m, hm⟩ := a
  change total m = n at hm
  subst hm
  exact h m rfl

lemma core_to_dfin (w : OF) (N : ℕ) (hw : ∀ m : Occ, N < total m → w m = 0) :
    (Phi (L := L)).symm w ∈ Dfin (L2T L) := by
  refine ⟨N, fun n hn => ?_⟩
  apply sector_zero_of_coeff
  intro m hm
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact hw m (by omega)

/-! ### The group `WK g r = printedWeyl (r g)` -/

/-- `r ↦ exp(r (a*(g) - a(g)))` on the physical carrier. -/
def WK (g : L2T L) (r : ℝ) : Fock L ≃ₗᵢ[ℂ] Fock L :=
  Ext006GlobalCovarianceR43a.physicalExponential ((-Complex.I) • g) r

lemma WK_apply (g : L2T L) (r : ℝ) (x : Fock L) :
    WK g r x = (Phi (L := L)).symm
      (Ext006BoundedExponentialR43a.unitary ((physicalBasis L).repr ((-Complex.I) • g)) r (Phi x)) :=
  rfl

theorem printedWeyl_eq_WK (g : L2T L) (r : ℝ) (x : Fock L) :
    printedWeyl ((r : ℂ) • g) x = WK g r x := by
  unfold printedWeyl
  rw [Ext006SourceWeylR44a.sourceWeyl_eq, Ext006GlobalCovarianceR43a.physicalExponential_apply,
    WK_apply]
  have hr : (physicalBasis L).repr ((-Complex.I) • (r : ℂ) • g) =
      (r : ℂ) • (physicalBasis L).repr ((-Complex.I) • g) := by
    rw [map_smul, map_smul, map_smul]
    exact smul_comm _ _ _
  rw [hr, Ext006WeylScalingR44a.unitary_real_smul]

theorem WK_zero (g : L2T L) (x : Fock L) : WK g 0 x = x := by
  rw [WK_apply, Ext006SeriesIdentificationR43a.unitary_zero, LinearIsometryEquiv.symm_apply_apply]

theorem WK_add (g : L2T L) (s t : ℝ) (x : Fock L) :
    WK g s (WK g t x) = WK g (s + t) x := by
  rw [WK_apply, WK_apply, WK_apply, LinearIsometryEquiv.apply_symm_apply,
    Ext006SeriesIdentificationR43a.unitary_add]

theorem WK_cont (g : L2T L) (x : Fock L) : Continuous (fun r : ℝ => WK g r x) :=
  Ext006GlobalCovarianceR43a.physicalExponential_strong_continuous ((-Complex.I) • g) x

lemma I_smul_neg_I_smul (w : OF) : Complex.I • ((-Complex.I) • w) = w := by
  rw [smul_smul]
  simp

/-! ### Generator identification (sequential form) -/

theorem WK_deriv_of_core (g : L2T L) (x y : Fock L) (z : ℕ → Dfin (L2T L))
    (hz : Tendsto (fun n => (z n : Fock L)) atTop (𝓝 x))
    (hZ : Tendsto (fun n => (Zgen g (z n) : Fock L)) atTop (𝓝 y)) :
    HasDerivAt (fun r : ℝ => WK g r x) y 0 := by
  set h := (physicalBasis L).repr ((-Complex.I) • g) with hh
  have hfld : ∀ n, (Ext006StrongFieldR41a.field h (embDfin (z n))).1 =
      (-Complex.I) • Phi (Zgen g (z n) : Fock L) := by
    intro n
    rw [phi_Zgen_field, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have hmem : (Phi x, (-Complex.I) • Phi y) ∈ Ext006FieldClosureR42a.closedFieldGraph h := by
    change _ ∈ closure {w : OF × OF | ∃ v : Ext006SmoothOperatorsR34a.D,
      w = (v.1, (Ext006StrongFieldR41a.field h v).1)}
    apply mem_closure_of_tendsto (b := atTop)
      (f := fun n => ((embDfin (z n)).1, (Ext006StrongFieldR41a.field h (embDfin (z n))).1))
    · refine Tendsto.prodMk_nhds ?_ ?_
      · exact ((Phi (L := L)).continuous.tendsto x).comp hz
      · simp only [hfld]
        exact ((Continuous.const_smul (Phi (L := L)).continuous (-Complex.I)).tendsto y).comp hZ
    · exact Eventually.of_forall (fun n => ⟨embDfin (z n), rfl⟩)
  have hd := Ext006StoneGeneratorR44a.graph_hasDerivAt h _ _ hmem 0
  rw [Ext006SeriesIdentificationR43a.unitary_zero, I_smul_neg_I_smul] at hd
  have hd2 := ((Phi (L := L)).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  have e2 : ((Phi (L := L)).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
      (Phi y) = y := by
    show (Phi (L := L)).symm (Phi y) = y
    exact (Phi (L := L)).symm_apply_apply y
  rw [e2] at hd2
  exact hd2

theorem WK_core_of_deriv (g : L2T L) (x y : Fock L)
    (hd : HasDerivAt (fun r : ℝ => WK g r x) y 0) :
    ∃ z : ℕ → Dfin (L2T L), Tendsto (fun n => (z n : Fock L)) atTop (𝓝 x) ∧
      Tendsto (fun n => (Zgen g (z n) : Fock L)) atTop (𝓝 y) := by
  set h := (physicalBasis L).repr ((-Complex.I) • g) with hh
  have hd1 : HasDerivAt (fun t : ℝ => Ext006BoundedExponentialR43a.unitary h t (Phi x))
      (Complex.I • ((-Complex.I) • Phi y)) 0 := by
    have hf : (fun t : ℝ => Ext006BoundedExponentialR43a.unitary h t (Phi x)) =
        (fun r : ℝ => (Phi (L := L)) (WK g r x)) := by
      funext t
      rw [WK_apply, LinearIsometryEquiv.apply_symm_apply]
    have hd0 := ((Phi (L := L)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    rw [hf, I_smul_neg_I_smul]
    exact hd0
  have hmem := Ext006StoneGeneratorR44a.derivative_mem_graph h (Phi x) ((-Complex.I) • Phi y) hd1
  have hc := (Ext006FieldMaximalityR44a.analytic_core_graph h (Phi x) ((-Complex.I) • Phi y)).mpr hmem
  change WithLp.toLp 2 (Phi x, (-Complex.I) • Phi y) ∈
    closure ((Ext006FieldMaximalityR44a.graphMap h).range : Set Ext006FieldMaximalityR44a.Pair) at hc
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp hc
  choose v hv using hp
  have hx : Tendsto (fun n => Ext006BoundedExponentialR43a.inclusion (v n)) atTop (𝓝 (Phi x)) := by
    have he := (WithLp.continuous_fst 2 OF OF).continuousAt.tendsto.comp ht
    simpa only [Function.comp_def, ← hv, Ext006FieldMaximalityR44a.graphMap_apply,
      WithLp.toLp_fst] using he
  have hy : Tendsto (fun n => (Ext006StrongFieldR41a.field h (v n).1).1) atTop
      (𝓝 ((-Complex.I) • Phi y)) := by
    have he := (WithLp.continuous_snd 2 OF OF).continuousAt.tendsto.comp ht
    simpa only [Function.comp_def, ← hv, Ext006FieldMaximalityR44a.graphMap_apply,
      WithLp.toLp_snd] using he
  let z : ℕ → Dfin (L2T L) := fun n =>
    ⟨(Phi (L := L)).symm (Ext006BoundedExponentialR43a.inclusion (v n)),
      core_to_dfin _ (Classical.choose (v n).2) (fun m hm => Classical.choose_spec (v n).2 m hm)⟩
  have hzD : ∀ n, embDfin (z n) = (v n).1 := by
    intro n
    apply Subtype.ext
    exact (Phi (L := L)).apply_symm_apply _
  refine ⟨z, ?_, ?_⟩
  · have h1 := ((Phi (L := L)).symm.continuous.tendsto (Phi x)).comp hx
    rw [LinearIsometryEquiv.symm_apply_apply] at h1
    exact h1
  · have hZ : ∀ n, (Zgen g (z n) : Fock L) = (Phi (L := L)).symm
        (Complex.I • (Ext006StrongFieldR41a.field h (v n).1).1) := by
      intro n
      rw [← hzD n, ← phi_Zgen_field, LinearIsometryEquiv.symm_apply_apply]
    simp only [hZ]
    have h1 : Tendsto (fun n => Complex.I • (Ext006StrongFieldR41a.field h (v n).1).1) atTop
        (𝓝 (Complex.I • (-Complex.I) • Phi y)) := hy.const_smul Complex.I
    have h2 := ((Phi (L := L)).symm.continuous.tendsto _).comp h1
    rw [I_smul_neg_I_smul, LinearIsometryEquiv.symm_apply_apply] at h2
    exact h2

end QuantumNLS.Prop022CTorus

#print axioms QuantumNLS.Prop022CTorus.annS_power
#print axioms QuantumNLS.Prop022CTorus.annMap_eq
#print axioms QuantumNLS.Prop022CTorus.C_emb
#print axioms QuantumNLS.Prop022CTorus.phi_Zgen_field
#print axioms QuantumNLS.Prop022CTorus.printedWeyl_eq_WK
#print axioms QuantumNLS.Prop022CTorus.WK_deriv_of_core
#print axioms QuantumNLS.Prop022CTorus.WK_core_of_deriv
