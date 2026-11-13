import MaxwellEndpoint
import MethlibEndpoints

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

#print NSEMaxwell.Classical.MaxwellSolution
#print NSEMaxwell.Classical.MaxwellB
#print MaxwellEndpoint.MaxwellEquations

#check @NSEMaxwell.Classical.Vec
#print axioms NSEMaxwell.Classical.Vec

#check @NSEMaxwell.Classical.Field
#print axioms NSEMaxwell.Classical.Field

#check @NSEMaxwell.Classical.Velocity
#print axioms NSEMaxwell.Classical.Velocity

#check @NSEMaxwell.Classical.Pressure
#print axioms NSEMaxwell.Classical.Pressure

#check @NSEMaxwell.Classical.unitCube
#print axioms NSEMaxwell.Classical.unitCube

#check @NSEMaxwell.Classical.SpatialPeriodic
#print axioms NSEMaxwell.Classical.SpatialPeriodic

#check @NSEMaxwell.Classical.spatialMean
#print axioms NSEMaxwell.Classical.spatialMean

#check @NSEMaxwell.Classical.coordinateDerivative
#print axioms NSEMaxwell.Classical.coordinateDerivative

#check @NSEMaxwell.Classical.divergence
#print axioms NSEMaxwell.Classical.divergence

#check @NSEMaxwell.Classical.spatialCurl
#print axioms NSEMaxwell.Classical.spatialCurl

#check @NSEMaxwell.Classical.timeDerivative
#print axioms NSEMaxwell.Classical.timeDerivative

#check @NSEMaxwell.Classical.SmoothVelocity
#print axioms NSEMaxwell.Classical.SmoothVelocity

#check @NSEMaxwell.Classical.SmoothPressure
#print axioms NSEMaxwell.Classical.SmoothPressure

#check @NSEMaxwell.Classical.Data
#print axioms NSEMaxwell.Classical.Data

#check @NSEMaxwell.Classical.MagneticData
#print axioms NSEMaxwell.Classical.MagneticData

#check @NSEMaxwell.Classical.inverseLaplacianSymbol
#print axioms NSEMaxwell.Classical.inverseLaplacianSymbol

#check @NSEMaxwell.Classical.cosineKernel
#print axioms NSEMaxwell.Classical.cosineKernel

#check @NSEMaxwell.Classical.vectorL
#print axioms NSEMaxwell.Classical.vectorL

#check @NSEMaxwell.Classical.scalarL
#print axioms NSEMaxwell.Classical.scalarL

#check @NSEMaxwell.Classical.K
#print axioms NSEMaxwell.Classical.K

#check @NSEMaxwell.Classical.U
#print axioms NSEMaxwell.Classical.U

#check @NSEMaxwell.Classical.G
#print axioms NSEMaxwell.Classical.G

#check @NSEMaxwell.Classical.V
#print axioms NSEMaxwell.Classical.V

#check @NSEMaxwell.Classical.Q
#print axioms NSEMaxwell.Classical.Q

#check @NSEMaxwell.Classical.DG
#print axioms NSEMaxwell.Classical.DG

#check @NSEMaxwell.Classical.current
#print axioms NSEMaxwell.Classical.current

#check @NSEMaxwell.Classical.MaxwellSolution
#print axioms NSEMaxwell.Classical.MaxwellSolution

#check @NSEMaxwell.Classical.MaxwellB
#print axioms NSEMaxwell.Classical.MaxwellB

#check @MaxwellEndpoint.MaxwellEquations
#print axioms MaxwellEndpoint.MaxwellEquations

#check @MaxwellEndpoint.equations_of_solution
#print axioms MaxwellEndpoint.equations_of_solution

#check @MaxwellEndpoint.constitutive_fields_of_solution
#print axioms MaxwellEndpoint.constitutive_fields_of_solution

#check @MaxwellEndpoint.magnetic_evolution_of_solution
#print axioms MaxwellEndpoint.magnetic_evolution_of_solution

#check @MaxwellEndpoint.electric_evolution_of_solution
#print axioms MaxwellEndpoint.electric_evolution_of_solution

#check @MaxwellEndpoint.maxwellB_iff_native
#print axioms MaxwellEndpoint.maxwellB_iff_native

#check @MaxwellEndpoint.coordinateDerivative_zero
#print axioms MaxwellEndpoint.coordinateDerivative_zero

#check @MaxwellEndpoint.divergence_zero
#print axioms MaxwellEndpoint.divergence_zero

#check @MaxwellEndpoint.spatialCurl_zero
#print axioms MaxwellEndpoint.spatialCurl_zero

#check @MaxwellEndpoint.cross_zero_left
#print axioms MaxwellEndpoint.cross_zero_left

#check @MaxwellEndpoint.cross_zero_right
#print axioms MaxwellEndpoint.cross_zero_right

#check @MaxwellEndpoint.vectorL_zero
#print axioms MaxwellEndpoint.vectorL_zero

#check @MaxwellEndpoint.scalarL_zero
#print axioms MaxwellEndpoint.scalarL_zero

#check @MaxwellEndpoint.K_zero
#print axioms MaxwellEndpoint.K_zero

#check @MaxwellEndpoint.U_zero
#print axioms MaxwellEndpoint.U_zero

#check @MaxwellEndpoint.G_zero
#print axioms MaxwellEndpoint.G_zero

#check @MaxwellEndpoint.V_zero
#print axioms MaxwellEndpoint.V_zero

#check @MaxwellEndpoint.Q_zero
#print axioms MaxwellEndpoint.Q_zero

#check @MaxwellEndpoint.DG_zero
#print axioms MaxwellEndpoint.DG_zero

#check @MaxwellEndpoint.current_zero
#print axioms MaxwellEndpoint.current_zero

#check @MaxwellEndpoint.timeDerivative_zero
#print axioms MaxwellEndpoint.timeDerivative_zero

#check @MaxwellEndpoint.magneticData_zero
#print axioms MaxwellEndpoint.magneticData_zero

#check @MaxwellEndpoint.zero_solution
#print axioms MaxwellEndpoint.zero_solution

#check @MaxwellEndpoint.zero_datum_global_instance
#print axioms MaxwellEndpoint.zero_datum_global_instance

-- Selected native Methlib endpoints; semantic hypotheses remain explicit.

#check @SingularClosure.torusDatumComponent_fourierCoeff
#print axioms SingularClosure.torusDatumComponent_fourierCoeff

#check @SingularClosure.datumFourierCoeff_coordinateDerivative
#print axioms SingularClosure.datumFourierCoeff_coordinateDerivative

#check @SingularClosure.FOURIER_POLYNOMIAL_DECAY
#print axioms SingularClosure.FOURIER_POLYNOMIAL_DECAY

#check @SingularClosure.scalarFourierSeries_contDiff
#print axioms SingularClosure.scalarFourierSeries_contDiff

#check @SingularClosure.scalarFourierSeries_coefficient
#print axioms SingularClosure.scalarFourierSeries_coefficient

#check @SingularClosure.datumFourierCoeff_injective_continuous_periodic
#print axioms SingularClosure.datumFourierCoeff_injective_continuous_periodic

#check @SingularClosure.infiniteTransportPressure_recovery
#print axioms SingularClosure.infiniteTransportPressure_recovery

#check @SingularClosure.datumFourierCoeff_smoothFourierSynthesis
#print axioms SingularClosure.datumFourierCoeff_smoothFourierSynthesis

#check @SingularClosure.smoothFourierSynthesis_coordinateDerivative
#print axioms SingularClosure.smoothFourierSynthesis_coordinateDerivative

#check @SingularClosure.summable_torusSobolevWeight_inv_four
#print axioms SingularClosure.summable_torusSobolevWeight_inv_four
