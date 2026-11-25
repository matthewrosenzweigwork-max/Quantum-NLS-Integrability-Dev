import NlsGge.Sobolev.SourceEmbeddings
import NlsGge.Sobolev.RealBasis
import Mathlib.Tactic

/-! Batch 38: a definitional synonym of the accepted real Sobolev carrier
`SobolevHilbert r` with ONE coherent real normed structure.

`SobolevHilbert r = RestrictScalars ℝ ℂ (WeightedHilbert _)` carries several
instance paths (`instAddCommMonoidRestrictScalars`, `RestrictScalars.module`,
and the normed group) which are definitionally but not instance-reducibly
equal; this blocks operator norms of continuous (multi)linear maps on it. The
synonym below has the same underlying set, addition, scalar action, norm and
topology (all by `rfl`), but only the normed-group and the accepted real
inner-product (`weightedRealBasisInnerProductSpace`) instances. No
mathematical content is changed. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Sobolev38

open NlsGge.Pilot

/-- Same type as `SobolevHilbert r`; only the instance path differs. -/
def SobolevCarrier38 (r : ℝ) : Type := SobolevHilbert r

instance sobolevCarrierNormedAddCommGroup38 (r : ℝ) :
    NormedAddCommGroup (SobolevCarrier38 r) :=
  inferInstanceAs (NormedAddCommGroup (SobolevHilbert r))

instance sobolevCarrierInnerProductSpace38 (r : ℝ) :
    InnerProductSpace ℝ (SobolevCarrier38 r) :=
  weightedRealBasisInnerProductSpace (sobolevModeWeight r)

/-- The identity map, viewed into the synonym. -/
def toCarrier38 (r : ℝ) (x : SobolevHilbert r) : SobolevCarrier38 r := x

/-- The identity map, viewed out of the synonym. -/
def ofCarrier38 (r : ℝ) (x : SobolevCarrier38 r) : SobolevHilbert r := x

@[simp] theorem ofCarrier_toCarrier38 (r : ℝ) (x : SobolevHilbert r) :
    ofCarrier38 r (toCarrier38 r x) = x := rfl

@[simp] theorem toCarrier_ofCarrier38 (r : ℝ) (x : SobolevCarrier38 r) :
    toCarrier38 r (ofCarrier38 r x) = x := rfl

theorem norm_toCarrier38 (r : ℝ) (x : SobolevHilbert r) :
    ‖toCarrier38 r x‖ = ‖x‖ := rfl

theorem continuous_toCarrier38 (r : ℝ) : Continuous (toCarrier38 r) :=
  continuous_id

theorem continuous_ofCarrier38 (r : ℝ) : Continuous (ofCarrier38 r) :=
  continuous_id

/-- Transport an accepted real CLM on `SobolevHilbert r` to the synonym. -/
def liftCLM38 {r : ℝ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : SobolevHilbert r →L[ℝ] Y) : SobolevCarrier38 r →L[ℝ] Y where
  toFun x := L (ofCarrier38 r x)
  map_add' x y := L.map_add x y
  map_smul' c x := L.map_smul c x
  cont := L.continuous

@[simp] theorem liftCLM38_apply {r : ℝ} {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (L : SobolevHilbert r →L[ℝ] Y) (x : SobolevCarrier38 r) :
    liftCLM38 L x = L (ofCarrier38 r x) := rfl

end NlsGge.Sobolev38
