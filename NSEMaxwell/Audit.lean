import NSEMaxwell

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

#print NSEMaxwell.Classical.Data
#print NSEMaxwell.Classical.MagneticData
#print NSEMaxwell.Classical.NSSolution
#print NSEMaxwell.Classical.MaxwellSolution
#print NSEMaxwell.Classical.FeffermanB
#print NSEMaxwell.Classical.MaxwellB
#print NSEMaxwell.Classical.ExactEquivalence
#print NSEMaxwell.Bridge.MagneticPath
#print NSEMaxwell.Bridge.CanonicalRegularity
#print NSEMaxwell.Bridge.PeriodicAnalyticLaws

#check @NSEMaxwell.Classical.velocity_slice_smooth
#print axioms NSEMaxwell.Classical.velocity_slice_smooth

#check @NSEMaxwell.Classical.pressure_slice_smooth
#print axioms NSEMaxwell.Classical.pressure_slice_smooth

#check @NSEMaxwell.Classical.timeDerivative_congr_field
#print axioms NSEMaxwell.Classical.timeDerivative_congr_field

#check @NSEMaxwell.Classical.scalarTimeDerivative_congr_field
#print axioms NSEMaxwell.Classical.scalarTimeDerivative_congr_field

#check @NSEMaxwell.Classical.vectorL_zero
#print axioms NSEMaxwell.Classical.vectorL_zero

#check @NSEMaxwell.Classical.scalarL_zero
#print axioms NSEMaxwell.Classical.scalarL_zero

#check @NSEMaxwell.Classical.K_zero
#print axioms NSEMaxwell.Classical.K_zero

#check @NSEMaxwell.Classical.DG_zero_direction
#print axioms NSEMaxwell.Classical.DG_zero_direction

#check @NSEMaxwell.Classical.NSSolution.slice_data
#print axioms NSEMaxwell.Classical.NSSolution.slice_data

#check @NSEMaxwell.Classical.MaxwellSolution.slice_magnetic_data
#print axioms NSEMaxwell.Classical.MaxwellSolution.slice_magnetic_data

#check @NSEMaxwell.Constitutive.cross_add_left
#print axioms NSEMaxwell.Constitutive.cross_add_left

#check @NSEMaxwell.Constitutive.cross_add_right
#print axioms NSEMaxwell.Constitutive.cross_add_right

#check @NSEMaxwell.Constitutive.DG_add_of_K_curl
#print axioms NSEMaxwell.Constitutive.DG_add_of_K_curl

#check @NSEMaxwell.Constitutive.DG_neg_of_K_curl
#print axioms NSEMaxwell.Constitutive.DG_neg_of_K_curl

#check @NSEMaxwell.Constitutive.ampere_factorization
#print axioms NSEMaxwell.Constitutive.ampere_factorization

#check @NSEMaxwell.Constitutive.ampere_zero_of_faraday
#print axioms NSEMaxwell.Constitutive.ampere_zero_of_faraday

#check @NSEMaxwell.Constitutive.canonical_faraday_of_maxwell
#print axioms NSEMaxwell.Constitutive.canonical_faraday_of_maxwell

#check @NSEMaxwell.Residual.hodge_momentum_factorization
#print axioms NSEMaxwell.Residual.hodge_momentum_factorization

#check @NSEMaxwell.Residual.momentum_factorization
#print axioms NSEMaxwell.Residual.momentum_factorization

#check @NSEMaxwell.Residual.reconstructed_zero_iff
#print axioms NSEMaxwell.Residual.reconstructed_zero_iff

#check @NSEMaxwell.Residual.factored_zero_iff
#print axioms NSEMaxwell.Residual.factored_zero_iff

#check @NSEMaxwell.Residual.momentum_pressure_change
#print axioms NSEMaxwell.Residual.momentum_pressure_change

#check @NSEMaxwell.Residual.gradient_split_zero_iff
#print axioms NSEMaxwell.Residual.gradient_split_zero_iff

#check @NSEMaxwell.Residual.ampere_factorization
#print axioms NSEMaxwell.Residual.ampere_factorization

#check @NSEMaxwell.Residual.full_maxwell_iff_faraday
#print axioms NSEMaxwell.Residual.full_maxwell_iff_faraday

#check @NSEMaxwell.Residual.momentum_zero_iff_full_maxwell
#print axioms NSEMaxwell.Residual.momentum_zero_iff_full_maxwell

#check @NSEMaxwell.ExistenceTransport.forall_iff_of_data_equiv
#print axioms NSEMaxwell.ExistenceTransport.forall_iff_of_data_equiv

#check @NSEMaxwell.ExistenceTransport.forall_exists_iff_of_data_equiv
#print axioms NSEMaxwell.ExistenceTransport.forall_exists_iff_of_data_equiv

#check @NSEMaxwell.ExistenceTransport.forall_nonempty_iff_of_solution_equiv
#print axioms NSEMaxwell.ExistenceTransport.forall_nonempty_iff_of_solution_equiv

#check @NSEMaxwell.Bridge.MagneticPath.slice
#print axioms NSEMaxwell.Bridge.MagneticPath.slice

#check @NSEMaxwell.Bridge.momentum_zero_of_ns
#print axioms NSEMaxwell.Bridge.momentum_zero_of_ns

#check @NSEMaxwell.Bridge.canonical_momentum_factorization
#print axioms NSEMaxwell.Bridge.canonical_momentum_factorization

#check @NSEMaxwell.Bridge.maxwell_of_faraday
#print axioms NSEMaxwell.Bridge.maxwell_of_faraday

#check @NSEMaxwell.Bridge.faraday_of_ns
#print axioms NSEMaxwell.Bridge.faraday_of_ns

#check @NSEMaxwell.Bridge.maxwell_of_ns
#print axioms NSEMaxwell.Bridge.maxwell_of_ns

#check @NSEMaxwell.Bridge.ns_of_maxwell
#print axioms NSEMaxwell.Bridge.ns_of_maxwell

#check @NSEMaxwell.Bridge.feffermanB_iff_maxwellB_of_periodicAnalyticLaws
#print axioms NSEMaxwell.Bridge.feffermanB_iff_maxwellB_of_periodicAnalyticLaws

#check @NSEMaxwell.Bridge.exact_equivalence_of_periodicAnalyticLaws
#print axioms NSEMaxwell.Bridge.exact_equivalence_of_periodicAnalyticLaws

#check @NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE
#print axioms NSEMaxwell.FEFFERMAN_B_MAXWELL_EQUIVALENCE

#check @NSEMaxwell.Classical.coordinateDerivative_neg
#print axioms NSEMaxwell.Classical.coordinateDerivative_neg

#check @NSEMaxwell.Classical.spatialCurl_neg
#print axioms NSEMaxwell.Classical.spatialCurl_neg

#check @NSEMaxwell.Classical.vectorL_neg
#print axioms NSEMaxwell.Classical.vectorL_neg

#check @NSEMaxwell.Classical.scalarL_neg
#print axioms NSEMaxwell.Classical.scalarL_neg

#check @NSEMaxwell.Classical.K_neg
#print axioms NSEMaxwell.Classical.K_neg

#check @NSEMaxwell.Classical.DG_neg
#print axioms NSEMaxwell.Classical.DG_neg

#check @NSEMaxwell.Classical.DG_curl_neg
#print axioms NSEMaxwell.Classical.DG_curl_neg

#check @NSEMaxwell.Lamb.vector_coordinate_decomposition
#print axioms NSEMaxwell.Lamb.vector_coordinate_decomposition

#check @NSEMaxwell.Lamb.convection_coordinate
#print axioms NSEMaxwell.Lamb.convection_coordinate

#check @NSEMaxwell.Lamb.kinetic_gradient_coordinate
#print axioms NSEMaxwell.Lamb.kinetic_gradient_coordinate

#check @NSEMaxwell.Lamb.lamb_identity_at
#print axioms NSEMaxwell.Lamb.lamb_identity_at

#check @NSEMaxwell.Lamb.lamb_identity
#print axioms NSEMaxwell.Lamb.lamb_identity

#check @NSEMaxwell.Lamb.lamb_identity_of_data
#print axioms NSEMaxwell.Lamb.lamb_identity_of_data

#check @NSEMaxwell.Lamb.reconstructed_lamb_identity
#print axioms NSEMaxwell.Lamb.reconstructed_lamb_identity

#check @NSEMaxwell.Classical.gradient_pressure_decomposition
#print axioms NSEMaxwell.Classical.gradient_pressure_decomposition

#check @NSEMaxwell.Classical.canonicalPressure_gradient
#print axioms NSEMaxwell.Classical.canonicalPressure_gradient

#check @NSEMaxwell.Classical.smooth_constant_velocity
#print axioms NSEMaxwell.Classical.smooth_constant_velocity

#check @NSEMaxwell.Classical.smooth_constant_pressure
#print axioms NSEMaxwell.Classical.smooth_constant_pressure

#check @NSEMaxwell.Classical.periodic_constant_velocity
#print axioms NSEMaxwell.Classical.periodic_constant_velocity

#check @NSEMaxwell.Classical.periodic_constant_pressure
#print axioms NSEMaxwell.Classical.periodic_constant_pressure

#check @NSEMaxwell.Constitutive.timeDerivative_eq_evolution_of_faraday
#print axioms NSEMaxwell.Constitutive.timeDerivative_eq_evolution_of_faraday

#check @NSEMaxwell.Constitutive.ampere_zero_of_faraday_chain
#print axioms NSEMaxwell.Constitutive.ampere_zero_of_faraday_chain

#check @NSEMaxwell.Bridge.MagneticPath.constant
#print axioms NSEMaxwell.Bridge.MagneticPath.constant

#check @NSEMaxwell.Bridge.PeriodicAnalyticLaws.curl_data
#print axioms NSEMaxwell.Bridge.PeriodicAnalyticLaws.curl_data

#check @NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruction_data
#print axioms NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruction_data

#check @NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruct_mean
#print axioms NSEMaxwell.Bridge.PeriodicAnalyticLaws.reconstruct_mean

#check @NSEMaxwell.Bridge.canonical_momentum_split
#print axioms NSEMaxwell.Bridge.canonical_momentum_split

#check @NSEMaxwell.Bridge.canonical_momentum_zero_of_faraday
#print axioms NSEMaxwell.Bridge.canonical_momentum_zero_of_faraday

#check @NSEMaxwell.CurlCurl.coordinateDerivative_smooth
#print axioms NSEMaxwell.CurlCurl.coordinateDerivative_smooth

#check @NSEMaxwell.CurlCurl.spatialCurl_smooth
#print axioms NSEMaxwell.CurlCurl.spatialCurl_smooth

#check @NSEMaxwell.CurlCurl.secondCoordinate_symm
#print axioms NSEMaxwell.CurlCurl.secondCoordinate_symm

#check @NSEMaxwell.CurlCurl.curl_curl
#print axioms NSEMaxwell.CurlCurl.curl_curl

#check @NSEMaxwell.CurlCurl.divergence_curl
#print axioms NSEMaxwell.CurlCurl.divergence_curl

#check @NSEMaxwell.CurlCurl.viscosity_identity_of_data
#print axioms NSEMaxwell.CurlCurl.viscosity_identity_of_data

#check @NSEMaxwell.CurlCurl.reconstructed_viscosity_identity
#print axioms NSEMaxwell.CurlCurl.reconstructed_viscosity_identity
