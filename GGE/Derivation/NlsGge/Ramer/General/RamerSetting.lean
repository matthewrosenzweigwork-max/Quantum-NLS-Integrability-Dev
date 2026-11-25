import NlsGge.Ramer.General.RamerSettingA
import NlsGge.Ramer.General.RamerSettingB

/-!
# The general Ramer setting with anisotropic `E` (G0)

Umbrella module.  The development is split into
* `NlsGge.Ramer.General.RamerSettingA`: §1 `ModeForm`, §2 `RamerSetting`, §3 the spaces
  `H`, `E`, the coordinate API (`coord`, `E_ext`, `E_norm_sq`, `E_inner`, `memE`, `ofSeq`,
  `projE`, `projE_tendsto`), separability/Polishness of `E`;
* `NlsGge.Ramer.General.RamerSettingB`: §4 `incl`, Hilbert–Schmidt, tail bound; §5
  `ofWeights`, `ofCoefficients`, `fullWeightedEquiv`, regression statements, the F05
  instance `ofSobolevRates`.
-/
