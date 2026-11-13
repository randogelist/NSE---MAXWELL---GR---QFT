import SingularClosure.PeriodicFourierRealization
import SingularClosure.InitialCutoffBounds
import SingularClosure.FourierDecay
import SingularClosure.FourierSeriesCalculus
import SingularClosure.SobolevSmoothRealization
import SingularClosure.PeriodicFourierInjective
import SingularClosure.InfiniteFourierPressure
import SingularClosure.LatticeSobolevSummability

/-!
# Selected native Methlib endpoints

The imported modules retain their original `SingularClosure` namespace and
proof bodies. Their source dependency closure is recorded under
`NativeSources/methlib/SOURCE_MANIFEST.json`.

The selected Fourier endpoints do not instantiate `NSEMaxwell.Bridge.FourierHodgeLaws`.
The source package's separate mean-zero NSE definitions and `AX6Statement`
remain source declarations; no inhabitant is assumed or transferred.
-/
