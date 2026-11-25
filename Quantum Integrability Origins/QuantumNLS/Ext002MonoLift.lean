import Mathlib
import QuantumNLS.BetheBlockTensor

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage M2a: L² lifts for field monomials

Measure-theoretic carriers for the weak normal-ordered field monomials of
`source/chapters/foundations/A04.tex:67-91` (matrix elements
`∫_w ∫_x ∫_y conj F(x,w) a(x;y) G(y,w)`), generalized to `r` creation and `s` annihilation
variables with `q` spectators.

* `pull`: precomposition of an `L²` class with a measurable map whose push-forward is a finite
  multiple `c • ν` of the target measure; its norm is exactly `√c · ‖F‖`.
* `mulOp`: multiplication by a bounded measurable function.
* `Trip L r s q = ((𝕋^r × 𝕋^q) × 𝕋^s)`, points `((x,w),y)`, with the product of the original
  mass-`L` torus measures, and the two placement maps `outPt ((x,w),y) = (x,w)` and
  `inPt ((x,w),y) = (y,w)` (block concatenation `Fin.append`, creation/annihilation block first,
  as in A04.tex:74-82). Their push-forwards are `L^s • μ_{r+q}` and `L^r • μ_{s+q}`
  (`map_outPt`, `map_inPt`).
No operator identification is postulated here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace ENNReal

namespace QuantumNLS.Ext002MonoLift
open PhysicalTensor

section Generic
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

theorem qmp_of_map {g : X → Y} (hg : Measurable g) {c : ℝ≥0∞} (hmap : μ.map g = c • ν) :
    Measure.QuasiMeasurePreserving g μ ν :=
  ⟨hg, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩

theorem memLp_pull {g : X → Y} (hg : Measurable g) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hmap : μ.map g = c • ν) (F : Lp ℂ 2 ν) : MemLp (fun x => F (g x)) 2 μ := by
  have h1 : MemLp F 2 (μ.map g) := by rw [hmap]; exact (Lp.memLp F).smul_measure hc
  exact h1.comp_of_map hg.aemeasurable

theorem eLpNorm_pull {g : X → Y} (hg : Measurable g) {c : ℝ≥0∞}
    (hmap : μ.map g = c • ν) (F : Lp ℂ 2 ν) :
    eLpNorm (fun x => F (g x)) 2 μ = c ^ ((1 : ℝ≥0∞) / 2).toReal • eLpNorm F 2 ν := by
  have h := eLpNorm_map_measure (p := 2) (f := g) (μ := μ) (g := (F : Y → ℂ))
    (by rw [hmap]; exact (Lp.aestronglyMeasurable F).smul_measure c) hg.aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ (Lp.aestronglyMeasurable F)] at h
  exact h.symm

theorem norm_toLp_pull {g : X → Y} (hg : Measurable g) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hmap : μ.map g = c • ν) (F : Lp ℂ 2 ν) :
    ‖(memLp_pull hg hc hmap F).toLp _‖ = c.toReal ^ ((1 : ℝ≥0∞) / 2).toReal * ‖F‖ := by
  rw [Lp.norm_toLp, eLpNorm_pull hg hmap F, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_rpow, Lp.norm_def]

/-- Precomposition with `g`, where `g_* μ = c • ν`. -/
def pull {g : X → Y} (hg : Measurable g) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hmap : μ.map g = c • ν) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun F => (memLp_pull hg hc hmap F).toLp _
      map_add' := fun F G => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_pull hg hc hmap (F + G)),
          Lp.coeFn_add ((memLp_pull hg hc hmap F).toLp _) ((memLp_pull hg hc hmap G).toLp _),
          MemLp.coeFn_toLp (memLp_pull hg hc hmap F), MemLp.coeFn_toLp (memLp_pull hg hc hmap G),
          (qmp_of_map hg hmap).ae_eq_comp (Lp.coeFn_add F G)] with x h hs hf hg' hc'
        rw [h, hs, Pi.add_apply, hf, hg']
        simpa only [Function.comp_apply, Pi.add_apply] using hc'
      map_smul' := fun a F => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_pull hg hc hmap (a • F)),
          Lp.coeFn_smul a ((memLp_pull hg hc hmap F).toLp _),
          MemLp.coeFn_toLp (memLp_pull hg hc hmap F),
          (qmp_of_map hg hmap).ae_eq_comp (Lp.coeFn_smul a F)] with x h hs hf hc'
        rw [h, RingHom.id_apply, hs, Pi.smul_apply, hf]
        simpa only [Function.comp_apply, Pi.smul_apply] using hc' }
    (c.toReal ^ ((1 : ℝ≥0∞) / 2).toReal)
    (fun F => (norm_toLp_pull hg hc hmap F).le)

theorem coeFn_pull {g : X → Y} (hg : Measurable g) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hmap : μ.map g = c • ν) (F : Lp ℂ 2 ν) :
    (pull hg hc hmap F : X → ℂ) =ᵐ[μ] fun x => F (g x) :=
  MemLp.coeFn_toLp (memLp_pull hg hc hmap F)

theorem norm_pull {g : X → Y} (hg : Measurable g) {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hmap : μ.map g = c • ν) (F : Lp ℂ 2 ν) :
    ‖pull hg hc hmap F‖ = c.toReal ^ ((1 : ℝ≥0∞) / 2).toReal * ‖F‖ :=
  norm_toLp_pull hg hc hmap F

theorem memLp_mul (φ : X → ℂ) (hφ : Measurable φ) (C : ℝ) (hb : ∀ x, ‖φ x‖ ≤ C)
    (f : Lp ℂ 2 μ) : MemLp (fun x => φ x * f x) 2 μ :=
  (Lp.memLp f).of_le_mul (hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

/-- Multiplication by a bounded measurable function on `L²(μ)`. -/
def mulOp (φ : X → ℂ) (hφ : Measurable φ) (C : ℝ) (hb : ∀ x, ‖φ x‖ ≤ C) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul φ hφ C hb f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_mul φ hφ C hb (f + g)),
          Lp.coeFn_add ((memLp_mul φ hφ C hb f).toLp _) ((memLp_mul φ hφ C hb g).toLp _),
          MemLp.coeFn_toLp (memLp_mul φ hφ C hb f), MemLp.coeFn_toLp (memLp_mul φ hφ C hb g),
          Lp.coeFn_add f g] with x h hs hf hg hfg
        rw [h, hs, Pi.add_apply, hf, hg, hfg, Pi.add_apply, mul_add]
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_mul φ hφ C hb (a • f)),
          Lp.coeFn_smul a ((memLp_mul φ hφ C hb f).toLp _),
          MemLp.coeFn_toLp (memLp_mul φ hφ C hb f), Lp.coeFn_smul a f] with x h hs hf haf
        rw [h, RingHom.id_apply, hs, Pi.smul_apply, hf, haf, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    C
    (fun f => by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MemLp.coeFn_toLp (memLp_mul φ hφ C hb f)] with x hx
      change ‖((memLp_mul φ hφ C hb f).toLp _ : X → ℂ) x‖ ≤ _
      rw [hx, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

theorem coeFn_mulOp (φ : X → ℂ) (hφ : Measurable φ) (C : ℝ) (hb : ∀ x, ‖φ x‖ ≤ C)
    (f : Lp ℂ 2 μ) : (mulOp φ hφ C hb f : X → ℂ) =ᵐ[μ] fun x => φ x * f x :=
  MemLp.coeFn_toLp (memLp_mul φ hφ C hb f)

/-- `mulOp` depends only on the multiplier. -/
theorem mulOp_congr (φ ψ : X → ℂ) (hφ : Measurable φ) (hψ : Measurable ψ) (C D : ℝ)
    (hb : ∀ x, ‖φ x‖ ≤ C) (hd : ∀ x, ‖ψ x‖ ≤ D) (h : φ = ψ) :
    (mulOp (μ := μ) φ hφ C hb) = mulOp ψ hψ D hd := by
  subst h
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coeFn_mulOp φ hφ C hb f, coeFn_mulOp φ hψ D hd f] with x h1 h2
  rw [h1, h2]

theorem mulOp_add (φ ψ : X → ℂ) (hφ : Measurable φ) (hψ : Measurable ψ) (C D : ℝ)
    (hb : ∀ x, ‖φ x‖ ≤ C) (hd : ∀ x, ‖ψ x‖ ≤ D) (hs : Measurable (φ + ψ))
    (hsb : ∀ x, ‖(φ + ψ) x‖ ≤ C + D) :
    (mulOp (μ := μ) (φ + ψ) hs (C + D) hsb) = mulOp φ hφ C hb + mulOp ψ hψ D hd := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coeFn_mulOp (φ + ψ) hs (C + D) hsb f, coeFn_mulOp φ hφ C hb f,
    coeFn_mulOp ψ hψ D hd f,
    Lp.coeFn_add (mulOp (μ := μ) φ hφ C hb f) (mulOp ψ hψ D hd f)] with x h1 h2 h3 h4
  rw [ContinuousLinearMap.add_apply, h4, h1]
  simp only [Pi.add_apply]
  rw [h2, h3, add_mul]

theorem mulOp_smul (a : ℂ) (φ : X → ℂ) (hφ : Measurable φ) (C D : ℝ)
    (hb : ∀ x, ‖φ x‖ ≤ C) (hs : Measurable (a • φ)) (hsb : ∀ x, ‖(a • φ) x‖ ≤ D) :
    (mulOp (μ := μ) (a • φ) hs D hsb) = a • mulOp φ hφ C hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [coeFn_mulOp (a • φ) hs D hsb f, coeFn_mulOp φ hφ C hb f,
    Lp.coeFn_smul a (mulOp (μ := μ) φ hφ C hb f)] with x h1 h2 h3
  rw [ContinuousLinearMap.smul_apply, h3, h1]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2, mul_assoc]

end Generic

section Torus
variable (L : ℝ) [Fact (0 < L)]

/-- Concatenation `(x,w) ↦ (x₁,…,x_m,w₁,…,w_q)` is the inverse of the frozen block split. -/
theorem splitCoordinates_symm_apply (m q : ℕ) (x : Fin m → AddCircle L)
    (w : Fin q → AddCircle L) :
    (BetheBlockTensor.splitCoordinates L m q).symm (x, w) = Fin.append x w := by
  rw [MeasurableEquiv.symm_apply_eq, BetheBlockTensor.splitCoordinates_apply]
  refine Prod.ext ?_ ?_ <;> funext i <;> simp

theorem appendU_eq (m q : ℕ) :
    (fun p : (Fin m → AddCircle L) × (Fin q → AddCircle L) => Fin.append p.1 p.2) =
      (BetheBlockTensor.splitCoordinates L m q).symm := by
  funext p
  exact (splitCoordinates_symm_apply L m q p.1 p.2).symm

theorem measurable_appendU (m q : ℕ) :
    Measurable (fun p : (Fin m → AddCircle L) × (Fin q → AddCircle L) => Fin.append p.1 p.2) := by
  rw [appendU_eq]
  exact (BetheBlockTensor.splitCoordinates L m q).symm.measurable

theorem measurePreserving_appendU (m q : ℕ) :
    MeasurePreserving (fun p : (Fin m → AddCircle L) × (Fin q → AddCircle L) => Fin.append p.1 p.2)
      ((torusPiMeasure L m).prod (torusPiMeasure L q)) (torusPiMeasure L (m+q)) := by
  rw [appendU_eq]
  exact (BetheBlockTensor.measurePreserving_splitCoordinates L m q).symm
    (BetheBlockTensor.splitCoordinates L m q)

/-- Points `((x,w),y)`: `x` creation block, `w` spectators, `y` annihilation block. -/
abbrev Trip (r s q : ℕ) : Type :=
  ((Fin r → AddCircle L) × (Fin q → AddCircle L)) × (Fin s → AddCircle L)

abbrev tripMeasure (r s q : ℕ) : Measure (Trip L r s q) :=
  ((torusPiMeasure L r).prod (torusPiMeasure L q)).prod (torusPiMeasure L s)

/-- Output configuration `(x,w)`. -/
def outPt {r s q : ℕ} (p : Trip L r s q) : Fin (r+q) → AddCircle L := Fin.append p.1.1 p.1.2

/-- Input configuration `(y,w)`. -/
def inPt {r s q : ℕ} (p : Trip L r s q) : Fin (s+q) → AddCircle L := Fin.append p.2 p.1.2

theorem measurable_outPt (r s q : ℕ) : Measurable (outPt L (r := r) (s := s) (q := q)) :=
  (measurable_appendU L r q).comp measurable_fst

theorem measurable_inPt (r s q : ℕ) : Measurable (inPt L (r := r) (s := s) (q := q)) :=
  (measurable_appendU L s q).comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))

theorem map_outPt (r s q : ℕ) :
    (tripMeasure L r s q).map (outPt L) = (torusPiMeasure L s Set.univ) • torusPiMeasure L (r+q) := by
  have h : (outPt L (r := r) (s := s) (q := q)) =
      (fun p : (Fin r → AddCircle L) × (Fin q → AddCircle L) => Fin.append p.1 p.2) ∘ Prod.fst := rfl
  rw [h, ← Measure.map_map (measurable_appendU L r q) measurable_fst, Measure.map_fst_prod,
    Measure.map_smul _ (measurable_appendU L r q).aemeasurable,
    (measurePreserving_appendU L r q).map_eq]

theorem map_inPt (r s q : ℕ) :
    (tripMeasure L r s q).map (inPt L) = (torusPiMeasure L r Set.univ) • torusPiMeasure L (s+q) := by
  have h : (inPt L (r := r) (s := s) (q := q)) =
      (fun p : (Fin s → AddCircle L) × (Fin q → AddCircle L) => Fin.append p.1 p.2) ∘
        (Prod.map id Prod.snd) ∘ Prod.swap := rfl
  have hm : Measurable (Prod.map (id : (Fin s → AddCircle L) → _)
      (Prod.snd : (Fin r → AddCircle L) × (Fin q → AddCircle L) → _)) :=
    measurable_id.prodMap measurable_snd
  rw [h, ← Measure.map_map (measurable_appendU L s q) (hm.comp measurable_swap),
    ← Measure.map_map hm measurable_swap,
    (Measure.measurePreserving_swap (μ := (torusPiMeasure L r).prod (torusPiMeasure L q))
      (ν := torusPiMeasure L s)).map_eq,
    ← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
    Measure.map_snd_prod, Measure.prod_smul_right,
    Measure.map_smul _ (measurable_appendU L s q).aemeasurable,
    (measurePreserving_appendU L s q).map_eq]

theorem torus_univ_ne_top (n : ℕ) : torusPiMeasure L n Set.univ ≠ ∞ := measure_ne_top _ _

/-- `F ↦ F(x,w)` on the triple space. -/
def liftOut (r s q : ℕ) : L2TN L (r+q) →L[ℂ] Lp ℂ 2 (tripMeasure L r s q) :=
  pull (measurable_outPt L r s q) (torus_univ_ne_top L s) (map_outPt L r s q)

/-- `G ↦ G(y,w)` on the triple space. -/
def liftIn (r s q : ℕ) : L2TN L (s+q) →L[ℂ] Lp ℂ 2 (tripMeasure L r s q) :=
  pull (measurable_inPt L r s q) (torus_univ_ne_top L r) (map_inPt L r s q)

theorem coeFn_liftOut (r s q : ℕ) (F : L2TN L (r+q)) :
    (liftOut L r s q F : Trip L r s q → ℂ) =ᵐ[tripMeasure L r s q] fun p => F (outPt L p) :=
  coeFn_pull _ _ _ F

theorem coeFn_liftIn (r s q : ℕ) (G : L2TN L (s+q)) :
    (liftIn L r s q G : Trip L r s q → ℂ) =ᵐ[tripMeasure L r s q] fun p => G (inPt L p) :=
  coeFn_pull _ _ _ G

theorem qmp_outPt (r s q : ℕ) :
    Measure.QuasiMeasurePreserving (outPt L (r := r) (s := s) (q := q))
      (tripMeasure L r s q) (torusPiMeasure L (r+q)) :=
  qmp_of_map (measurable_outPt L r s q) (map_outPt L r s q)

theorem qmp_inPt (r s q : ℕ) :
    Measure.QuasiMeasurePreserving (inPt L (r := r) (s := s) (q := q))
      (tripMeasure L r s q) (torusPiMeasure L (s+q)) :=
  qmp_of_map (measurable_inPt L r s q) (map_inPt L r s q)

end Torus

end QuantumNLS.Ext002MonoLift

#print axioms QuantumNLS.Ext002MonoLift.pull
#print axioms QuantumNLS.Ext002MonoLift.norm_pull
#print axioms QuantumNLS.Ext002MonoLift.mulOp
#print axioms QuantumNLS.Ext002MonoLift.mulOp_add
#print axioms QuantumNLS.Ext002MonoLift.mulOp_smul
#print axioms QuantumNLS.Ext002MonoLift.mulOp_congr
#print axioms QuantumNLS.Ext002MonoLift.map_outPt
#print axioms QuantumNLS.Ext002MonoLift.map_inPt
#print axioms QuantumNLS.Ext002MonoLift.liftOut
#print axioms QuantumNLS.Ext002MonoLift.liftIn
