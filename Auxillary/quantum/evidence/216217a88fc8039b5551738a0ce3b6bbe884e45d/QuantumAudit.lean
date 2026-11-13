import QuantumAdapter.Phase
import QuantumAdapter.FiniteModel
import QuantumAdapter.Tangency
import QuantumAdapter.Energy
import QuantumAdapter.Born
import QuantumAdapter.Transport
import QuantumAdapter.L2Norm
import QuantumAdapter.L2Transport
import QuantumAdapter.Dynamics
import QuantumAdapter.RegularityContracts
import QuantumAdapter
import NSEQuantumForward
import NSEQuantumReverse
import NSEQuantumBridge

set_option pp.universes true
set_option pp.fullNames true

#check @QuantumAdapter.fullModes
#print axioms QuantumAdapter.fullModes
#check @QuantumAdapter.Mode
#print axioms QuantumAdapter.Mode
#check @QuantumAdapter.PhaseIndex
#print axioms QuantumAdapter.PhaseIndex
#check @QuantumAdapter.AmbientPhase
#print axioms QuantumAdapter.AmbientPhase
#check @QuantumAdapter.zero_mem_fullModes
#print axioms QuantumAdapter.zero_mem_fullModes
#check @QuantumAdapter.fullModes_neg_mem
#print axioms QuantumAdapter.fullModes_neg_mem
#check @QuantumAdapter.fullModes_neg_mem_iff
#print axioms QuantumAdapter.fullModes_neg_mem_iff
#check @QuantumAdapter.extendCoeff
#print axioms QuantumAdapter.extendCoeff
#check @QuantumAdapter.extendCoeff_zero
#print axioms QuantumAdapter.extendCoeff_zero
#check @QuantumAdapter.extendCoeff_add
#print axioms QuantumAdapter.extendCoeff_add
#check @QuantumAdapter.extendCoeff_real_smul
#print axioms QuantumAdapter.extendCoeff_real_smul
#check @QuantumAdapter.extendCoeff_injective
#print axioms QuantumAdapter.extendCoeff_injective
#check @QuantumAdapter.phaseSubmodule
#print axioms QuantumAdapter.phaseSubmodule
#check @QuantumAdapter.Phase
#print axioms QuantumAdapter.Phase
#check @QuantumAdapter.phaseCoeff
#print axioms QuantumAdapter.phaseCoeff
#check @QuantumAdapter.phaseCoeff_reality
#print axioms QuantumAdapter.phaseCoeff_reality
#check @QuantumAdapter.phaseCoeff_solenoidal
#print axioms QuantumAdapter.phaseCoeff_solenoidal
#check @QuantumAdapter.phaseCoeff_support
#print axioms QuantumAdapter.phaseCoeff_support
#check @QuantumAdapter.phaseCoeff_zero
#print axioms QuantumAdapter.phaseCoeff_zero
#check @QuantumAdapter.meanAmbient
#print axioms QuantumAdapter.meanAmbient
#check @QuantumAdapter.meanAmbient_coeff
#print axioms QuantumAdapter.meanAmbient_coeff
#check @QuantumAdapter.meanAmbient_mem
#print axioms QuantumAdapter.meanAmbient_mem
#check @QuantumAdapter.meanPhase
#print axioms QuantumAdapter.meanPhase
#check @QuantumAdapter.meanPhase_coeff
#print axioms QuantumAdapter.meanPhase_coeff
#check @QuantumAdapter.meanPhase_injective
#print axioms QuantumAdapter.meanPhase_injective
#check @QuantumAdapter.phase_finrank_pos
#print axioms QuantumAdapter.phase_finrank_pos
#check @QuantumAdapter.datumFourierCoeff_solenoidal
#print axioms QuantumAdapter.datumFourierCoeff_solenoidal
#check @QuantumAdapter.initialAmbient
#print axioms QuantumAdapter.initialAmbient
#check @QuantumAdapter.initialAmbient_coeff
#print axioms QuantumAdapter.initialAmbient_coeff
#check @QuantumAdapter.initialAmbient_mem
#print axioms QuantumAdapter.initialAmbient_mem
#check @QuantumAdapter.initialPhase
#print axioms QuantumAdapter.initialPhase
#check @QuantumAdapter.initialPhase_coeff
#print axioms QuantumAdapter.initialPhase_coeff
#check @QuantumAdapter.initialPhase_mean
#print axioms QuantumAdapter.initialPhase_mean
#check @QuantumAdapter.initialPhaseData
#print axioms QuantumAdapter.initialPhaseData
#check @QuantumAdapter.initialPhaseData_mean
#print axioms QuantumAdapter.initialPhaseData_mean
#check @QuantumAdapter.laplaceSymbol
#print axioms QuantumAdapter.laplaceSymbol
#check @QuantumAdapter.laplaceSymbol_nonneg
#print axioms QuantumAdapter.laplaceSymbol_nonneg
#check @QuantumAdapter.h3Weight
#print axioms QuantumAdapter.h3Weight
#check @QuantumAdapter.h3Weight_pos
#print axioms QuantumAdapter.h3Weight_pos
#check @QuantumAdapter.energy3
#print axioms QuantumAdapter.energy3
#check @QuantumAdapter.energy3_nonneg
#print axioms QuantumAdapter.energy3_nonneg
#check @QuantumAdapter.energy3_zero
#print axioms QuantumAdapter.energy3_zero
#check @QuantumAdapter.synthesis
#print axioms QuantumAdapter.synthesis
#check @QuantumAdapter.meanVector
#print axioms QuantumAdapter.meanVector
#check @QuantumAdapter.synthesis_eq_mean_add_source
#print axioms QuantumAdapter.synthesis_eq_mean_add_source
#check @QuantumAdapter.synthesis_zero
#print axioms QuantumAdapter.synthesis_zero
#check @QuantumAdapter.gradientSquare
#print axioms QuantumAdapter.gradientSquare
#check @QuantumAdapter.gradientObservable
#print axioms QuantumAdapter.gradientObservable
#check @QuantumAdapter.fullTransport
#print axioms QuantumAdapter.fullTransport
#check @QuantumAdapter.fullTransport_eq_source_add_mean
#print axioms QuantumAdapter.fullTransport_eq_source_add_mean
#check @QuantumAdapter.fullTransport_eq_source_of_mean_zero
#print axioms QuantumAdapter.fullTransport_eq_source_of_mean_zero
#check @QuantumAdapter.fullTransport_zero
#print axioms QuantumAdapter.fullTransport_zero
#check @QuantumAdapter.fullTransport_zero_fun
#print axioms QuantumAdapter.fullTransport_zero_fun
#check @QuantumAdapter.rawRhs
#print axioms QuantumAdapter.rawRhs
#check @QuantumAdapter.rawRhs_mean
#print axioms QuantumAdapter.rawRhs_mean
#check @QuantumAdapter.rawRhs_zero
#print axioms QuantumAdapter.rawRhs_zero
#check @QuantumAdapter.RawRhsTangent
#print axioms QuantumAdapter.RawRhsTangent
#check @QuantumAdapter.drift
#print axioms QuantumAdapter.drift
#check @QuantumAdapter.drift_zero
#print axioms QuantumAdapter.drift_zero
#check @QuantumAdapter.drift_eq_rawRhs_of_tangent
#print axioms QuantumAdapter.drift_eq_rawRhs_of_tangent
#check @QuantumAdapter.IsTrajectory
#print axioms QuantumAdapter.IsTrajectory
#check @QuantumAdapter.zero_isTrajectory
#print axioms QuantumAdapter.zero_isTrajectory
#check @QuantumAdapter.cotangentHamiltonian
#print axioms QuantumAdapter.cotangentHamiltonian
#check @QuantumAdapter.cotangent_momentum_increment
#print axioms QuantumAdapter.cotangent_momentum_increment
#check @QuantumAdapter.cotangent_hasFDerivAt_momentum
#print axioms QuantumAdapter.cotangent_hasFDerivAt_momentum
#check @QuantumAdapter.cotangent_fderiv_momentum
#print axioms QuantumAdapter.cotangent_fderiv_momentum
#check @QuantumAdapter.cotangent_zero_momentum
#print axioms QuantumAdapter.cotangent_zero_momentum
#check @QuantumAdapter.cotangent_zero_configuration
#print axioms QuantumAdapter.cotangent_zero_configuration
#check @QuantumAdapter.fullTransport_zero_frequency
#print axioms QuantumAdapter.fullTransport_zero_frequency
#check @QuantumAdapter.fullTransport_reality
#print axioms QuantumAdapter.fullTransport_reality
#check @QuantumAdapter.frequencySquare_ne_zero
#print axioms QuantumAdapter.frequencySquare_ne_zero
#check @QuantumAdapter.coefficientLeray_solenoidal
#print axioms QuantumAdapter.coefficientLeray_solenoidal
#check @QuantumAdapter.rawRhs_coeff
#print axioms QuantumAdapter.rawRhs_coeff
#check @QuantumAdapter.rawRhs_all_modes
#print axioms QuantumAdapter.rawRhs_all_modes
#check @QuantumAdapter.rawRhs_reality
#print axioms QuantumAdapter.rawRhs_reality
#check @QuantumAdapter.rawRhs_solenoidal
#print axioms QuantumAdapter.rawRhs_solenoidal
#check @QuantumAdapter.rawRhs_tangent
#print axioms QuantumAdapter.rawRhs_tangent
#check @QuantumAdapter.drift_eq_rawRhs
#print axioms QuantumAdapter.drift_eq_rawRhs
#check @QuantumAdapter.drift_mean
#print axioms QuantumAdapter.drift_mean
#check @QuantumAdapter.fullTransport_complex_energy_zero
#print axioms QuantumAdapter.fullTransport_complex_energy_zero
#check @QuantumAdapter.fullLerayTransport_complex_energy_zero
#print axioms QuantumAdapter.fullLerayTransport_complex_energy_zero
#check @QuantumAdapter.fullLerayTransport_real_energy_zero
#print axioms QuantumAdapter.fullLerayTransport_real_energy_zero
#check @QuantumAdapter.energy0
#print axioms QuantumAdapter.energy0
#check @QuantumAdapter.dissipation
#print axioms QuantumAdapter.dissipation
#check @QuantumAdapter.energy0_nonneg
#print axioms QuantumAdapter.energy0_nonneg
#check @QuantumAdapter.dissipation_nonneg
#print axioms QuantumAdapter.dissipation_nonneg
#check @QuantumAdapter.rawRhs_energy_rate
#print axioms QuantumAdapter.rawRhs_energy_rate
#check @QuantumAdapter.rawRhs_energy_rate_nonpos
#print axioms QuantumAdapter.rawRhs_energy_rate_nonpos
#check @QuantumAdapter.phaseCoordinate
#print axioms QuantumAdapter.phaseCoordinate
#check @QuantumAdapter.phaseCoordinate_apply
#print axioms QuantumAdapter.phaseCoordinate_apply
#check @QuantumAdapter.IsTrajectory.coefficient_hasDerivWithinAt
#print axioms QuantumAdapter.IsTrajectory.coefficient_hasDerivWithinAt
#check @QuantumAdapter.IsTrajectory.energy0_identity
#print axioms QuantumAdapter.IsTrajectory.energy0_identity
#check @QuantumAdapter.IsTrajectory.energy0_antitoneOn
#print axioms QuantumAdapter.IsTrajectory.energy0_antitoneOn
#check @QuantumAdapter.IsTrajectory.energy0_le_initial
#print axioms QuantumAdapter.IsTrajectory.energy0_le_initial
#check @QuantumAdapter.Wave
#print axioms QuantumAdapter.Wave
#check @QuantumAdapter.bornDensity
#print axioms QuantumAdapter.bornDensity
#check @QuantumAdapter.expectation
#print axioms QuantumAdapter.expectation
#check @QuantumAdapter.WaveAdmissible
#print axioms QuantumAdapter.WaveAdmissible
#check @QuantumAdapter.ObservableIntegrable
#print axioms QuantumAdapter.ObservableIntegrable
#check @QuantumAdapter.MultiplierDomain
#print axioms QuantumAdapter.MultiplierDomain
#check @QuantumAdapter.bornDensity_nonneg
#print axioms QuantumAdapter.bornDensity_nonneg
#check @QuantumAdapter.bornDensity_zero
#print axioms QuantumAdapter.bornDensity_zero
#check @QuantumAdapter.bornDensity_const_mul
#print axioms QuantumAdapter.bornDensity_const_mul
#check @QuantumAdapter.bornDensity_unit_phase
#print axioms QuantumAdapter.bornDensity_unit_phase
#check @QuantumAdapter.WaveAdmissible.density_integrable
#print axioms QuantumAdapter.WaveAdmissible.density_integrable
#check @QuantumAdapter.not_waveAdmissible_zero
#print axioms QuantumAdapter.not_waveAdmissible_zero
#check @QuantumAdapter.WaveAdmissible.toL2
#print axioms QuantumAdapter.WaveAdmissible.toL2
#check @QuantumAdapter.WaveAdmissible.coe_toL2
#print axioms QuantumAdapter.WaveAdmissible.coe_toL2
#check @QuantumAdapter.expectation_congr_ae
#print axioms QuantumAdapter.expectation_congr_ae
#check @QuantumAdapter.WaveAdmissible.expectation_toL2
#print axioms QuantumAdapter.WaveAdmissible.expectation_toL2
#check @QuantumAdapter.expectation_nonneg
#print axioms QuantumAdapter.expectation_nonneg
#check @QuantumAdapter.expectation_const_mul_wave
#print axioms QuantumAdapter.expectation_const_mul_wave
#check @QuantumAdapter.expectation_unit_phase
#print axioms QuantumAdapter.expectation_unit_phase
#check @QuantumAdapter.expectation_const
#print axioms QuantumAdapter.expectation_const
#check @QuantumAdapter.expectation_mono
#print axioms QuantumAdapter.expectation_mono
#check @QuantumAdapter.expectation_add
#print axioms QuantumAdapter.expectation_add
#check @QuantumAdapter.expectation_le_bound
#print axioms QuantumAdapter.expectation_le_bound
#check @QuantumAdapter.bound_le_expectation
#print axioms QuantumAdapter.bound_le_expectation
#check @QuantumAdapter.halfDensityPullback
#print axioms QuantumAdapter.halfDensityPullback
#check @QuantumAdapter.halfDensityPullback_zero
#print axioms QuantumAdapter.halfDensityPullback_zero
#check @QuantumAdapter.halfDensityPullback_add
#print axioms QuantumAdapter.halfDensityPullback_add
#check @QuantumAdapter.halfDensityPullback_inverse
#print axioms QuantumAdapter.halfDensityPullback_inverse
#check @QuantumAdapter.bornDensity_halfDensityPullback
#print axioms QuantumAdapter.bornDensity_halfDensityPullback
#check @QuantumAdapter.IntegralPullbackLaw
#print axioms QuantumAdapter.IntegralPullbackLaw
#check @QuantumAdapter.MemLpPullbackLaw
#print axioms QuantumAdapter.MemLpPullbackLaw
#check @QuantumAdapter.WaveAdmissible.halfDensityPullback
#print axioms QuantumAdapter.WaveAdmissible.halfDensityPullback
#check @QuantumAdapter.expectation_halfDensityPullback
#print axioms QuantumAdapter.expectation_halfDensityPullback
#check @QuantumAdapter.memLp_bornDensity_integrable
#print axioms QuantumAdapter.memLp_bornDensity_integrable
#check @QuantumAdapter.memLp_toLp_norm_sq
#print axioms QuantumAdapter.memLp_toLp_norm_sq
#check @QuantumAdapter.WaveAdmissible.norm_toL2
#print axioms QuantumAdapter.WaveAdmissible.norm_toL2
#check @QuantumAdapter.halfDensityPullback_toLp_norm
#print axioms QuantumAdapter.halfDensityPullback_toLp_norm
#check @QuantumAdapter.halfDensityPullback_congr_ae
#print axioms QuantumAdapter.halfDensityPullback_congr_ae
#check @QuantumAdapter.l2Pullback
#print axioms QuantumAdapter.l2Pullback
#check @QuantumAdapter.l2Pullback_coe
#print axioms QuantumAdapter.l2Pullback_coe
#check @QuantumAdapter.l2Pullback_toLp
#print axioms QuantumAdapter.l2Pullback_toLp
#check @QuantumAdapter.l2Pullback_norm
#print axioms QuantumAdapter.l2Pullback_norm
#check @QuantumAdapter.l2Pullback_add_vectors
#print axioms QuantumAdapter.l2Pullback_add_vectors
#check @QuantumAdapter.l2Pullback_smul
#print axioms QuantumAdapter.l2Pullback_smul
#check @QuantumAdapter.l2PullbackIsometry
#print axioms QuantumAdapter.l2PullbackIsometry
#check @QuantumAdapter.l2Pullback_zero
#print axioms QuantumAdapter.l2Pullback_zero
#check @QuantumAdapter.l2Pullback_add_times
#print axioms QuantumAdapter.l2Pullback_add_times
#check @QuantumAdapter.l2PullbackEquiv
#print axioms QuantumAdapter.l2PullbackEquiv
#check @QuantumAdapter.l2PullbackEquiv_apply
#print axioms QuantumAdapter.l2PullbackEquiv_apply
#check @QuantumAdapter.l2PullbackEquiv_symm_apply
#print axioms QuantumAdapter.l2PullbackEquiv_symm_apply
#check @QuantumAdapter.phaseDimension
#print axioms QuantumAdapter.phaseDimension
#check @QuantumAdapter.phaseVolume
#print axioms QuantumAdapter.phaseVolume
#check @QuantumAdapter.QuantumHilbert
#print axioms QuantumAdapter.QuantumHilbert
#check @QuantumAdapter.cutoffSobolevFactor
#print axioms QuantumAdapter.cutoffSobolevFactor
#check @QuantumAdapter.cutoffSobolevFactor_pos
#print axioms QuantumAdapter.cutoffSobolevFactor_pos
#check @QuantumAdapter.canonicalScale
#print axioms QuantumAdapter.canonicalScale
#check @QuantumAdapter.canonicalScale_pos
#print axioms QuantumAdapter.canonicalScale_pos
#check @QuantumAdapter.gaussianAmplitude
#print axioms QuantumAdapter.gaussianAmplitude
#check @QuantumAdapter.gaussianAmplitude_pos
#print axioms QuantumAdapter.gaussianAmplitude_pos
#check @QuantumAdapter.canonicalPacket
#print axioms QuantumAdapter.canonicalPacket
#check @QuantumAdapter.canonicalPacket_im
#print axioms QuantumAdapter.canonicalPacket_im
#check @QuantumAdapter.canonicalPacket_center
#print axioms QuantumAdapter.canonicalPacket_center
#check @QuantumAdapter.canonicalPacket_re_pos
#print axioms QuantumAdapter.canonicalPacket_re_pos
#check @QuantumAdapter.finiteLaplaceTrace
#print axioms QuantumAdapter.finiteLaplaceTrace
#check @QuantumAdapter.finiteLaplaceTrace_nonneg
#print axioms QuantumAdapter.finiteLaplaceTrace_nonneg
#check @QuantumAdapter.phaseDecayRate
#print axioms QuantumAdapter.phaseDecayRate
#check @QuantumAdapter.driftDivergence
#print axioms QuantumAdapter.driftDivergence
#check @QuantumAdapter.PhaseFlow
#print axioms QuantumAdapter.PhaseFlow
#check @QuantumAdapter.transport
#print axioms QuantumAdapter.transport
#check @QuantumAdapter.transportedPacket
#print axioms QuantumAdapter.transportedPacket
#check @QuantumAdapter.quantumEnergy
#print axioms QuantumAdapter.quantumEnergy
#check @QuantumAdapter.quantumAdmissible
#print axioms QuantumAdapter.quantumAdmissible
#check @QuantumAdapter.quantumEnergy_nonneg
#print axioms QuantumAdapter.quantumEnergy_nonneg
#check @QuantumAdapter.transport_zero
#print axioms QuantumAdapter.transport_zero
#check @QuantumAdapter.transportedPacket_zero
#print axioms QuantumAdapter.transportedPacket_zero
#check @QuantumAdapter.transport_add
#print axioms QuantumAdapter.transport_add
#check @QuantumAdapter.transport_inverse
#print axioms QuantumAdapter.transport_inverse
#check @QuantumAdapter.phaseFlow_isTrajectory
#print axioms QuantumAdapter.phaseFlow_isTrajectory
#check @QuantumAdapter.hamiltonianExpression
#print axioms QuantumAdapter.hamiltonianExpression
#check @QuantumAdapter.HamiltonianTestDomain
#print axioms QuantumAdapter.HamiltonianTestDomain
#check @QuantumAdapter.hamiltonianExpression_zero
#print axioms QuantumAdapter.hamiltonianExpression_zero
#check @QuantumAdapter.PhaseTransportLaws
#print axioms QuantumAdapter.PhaseTransportLaws
#check @QuantumAdapter.quantumUnitary
#print axioms QuantumAdapter.quantumUnitary
#check @QuantumAdapter.quantumUnitary_zero
#print axioms QuantumAdapter.quantumUnitary_zero
#check @QuantumAdapter.quantumUnitary_add
#print axioms QuantumAdapter.quantumUnitary_add
#check @QuantumAdapter.transport_waveAdmissible
#print axioms QuantumAdapter.transport_waveAdmissible
#check @QuantumAdapter.quantumEnergy_conjugacy
#print axioms QuantumAdapter.quantumEnergy_conjugacy
#check @QuantumAdapter.centralEnergy
#print axioms QuantumAdapter.centralEnergy
#check @QuantumAdapter.packetEnergy
#print axioms QuantumAdapter.packetEnergy
#check @QuantumAdapter.GalerkinBoundAt
#print axioms QuantumAdapter.GalerkinBoundAt
#check @QuantumAdapter.G3
#print axioms QuantumAdapter.G3
#check @QuantumAdapter.QREG
#print axioms QuantumAdapter.QREG
#check @QuantumAdapter.forwardPacketBound
#print axioms QuantumAdapter.forwardPacketBound
#check @QuantumAdapter.packetGradientBudget
#print axioms QuantumAdapter.packetGradientBudget
#check @QuantumAdapter.reversePacketBound
#print axioms QuantumAdapter.reversePacketBound
#check @QuantumAdapter.forwardPacketBound_nonneg
#print axioms QuantumAdapter.forwardPacketBound_nonneg
#check @QuantumAdapter.reversePacketBound_nonneg
#print axioms QuantumAdapter.reversePacketBound_nonneg
#check @QuantumAdapter.PacketBounds
#print axioms QuantumAdapter.PacketBounds
#check @QuantumAdapter.InitialProjectionBounds
#print axioms QuantumAdapter.InitialProjectionBounds
#check @QuantumAdapter.GalerkinAnalyticLaws
#print axioms QuantumAdapter.GalerkinAnalyticLaws
#check @QuantumAdapter.ExactQuantumEquivalence
#print axioms QuantumAdapter.ExactQuantumEquivalence
#check @QuantumAdapter.Directions.feffermanB_implies_galerkin_of_analyticLaws
#print axioms QuantumAdapter.Directions.feffermanB_implies_galerkin_of_analyticLaws
#check @QuantumAdapter.Directions.galerkin_implies_quantum_of_packetBounds
#print axioms QuantumAdapter.Directions.galerkin_implies_quantum_of_packetBounds
#check @QuantumAdapter.Directions.feffermanB_implies_quantum_of_analyticLaws
#print axioms QuantumAdapter.Directions.feffermanB_implies_quantum_of_analyticLaws
#check @QuantumAdapter.Directions.quantum_implies_galerkin_of_packetBounds
#print axioms QuantumAdapter.Directions.quantum_implies_galerkin_of_packetBounds
#check @QuantumAdapter.Directions.galerkin_implies_feffermanB_of_analyticLaws
#print axioms QuantumAdapter.Directions.galerkin_implies_feffermanB_of_analyticLaws
#check @QuantumAdapter.Directions.quantum_implies_feffermanB_of_analyticLaws
#print axioms QuantumAdapter.Directions.quantum_implies_feffermanB_of_analyticLaws
#check @QuantumAdapter.feffermanB_iff_qreg_of_analytic_bounds
#print axioms QuantumAdapter.feffermanB_iff_qreg_of_analytic_bounds
#check @QuantumAdapter.exactQuantumEquivalence_of_analytic_bounds
#print axioms QuantumAdapter.exactQuantumEquivalence_of_analytic_bounds
#check @QuantumAdapter.exact_quantum_conditional_root
#print axioms QuantumAdapter.exact_quantum_conditional_root
