import QuantumAdapter.Obligations.GalerkinContinuumSmooth
import QuantumAdapter.Obligations.JointFourierBounds
import SingularClosure.InfiniteFourierPressure

/-!
# Jointly smooth pressure from the actual smooth physical convection

The pressure time tower is constructed by differentiating the actual physical
field and its Fourier integrals. No additional pressure-regularity premise is used.
-/
set_option autoImplicit false
set_option Elab.async true
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff

namespace QuantumAdapter.Obligations
open SingularClosure QuantumAdapter.Assembly
open NSEMaxwell.Classical (SmoothVelocity SmoothPressure)
noncomputable section

def physicalTimeJet : ℕ → Velocity → Velocity
  | 0, u => u
  | n + 1, u => timeDerivative (physicalTimeJet n u)

theorem SmoothVelocity.physicalTimeJet {u : Velocity} (h : SmoothVelocity u) (n : ℕ) :
    SmoothVelocity (physicalTimeJet n u) := by
  induction n with
  | zero => exact h
  | succ n ih => exact SmoothVelocity.timeDerivative_smooth ih

theorem timeDerivative_periodic {u : Velocity}
    (hp : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)) :
    ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (timeDerivative u t) := by
  intro t ht x j
  exact derivWithin_congr (fun s hs => hp s hs x j) (hp t ht x j)

theorem physicalTimeJet_periodic {u : Velocity}
    (hp : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)) (n : ℕ) :
    ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (physicalTimeJet n u t) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact timeDerivative_periodic ih

/-- The actual physical nonlinear term is jointly smooth on the closed halfspace. -/
theorem SmoothVelocity.convection {u : Velocity} (h : SmoothVelocity u) :
    SmoothVelocity (fun t => SingularClosure.convection (u t)) := by
  have hsum : ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      ∑ j : Fin 3, u z.1 z.2 j • forwardSpatialDerivative (fun y => u y.1 y.2) j z)
      forwardSpacetime := by
    apply ContDiffOn.sum
    intro j hj
    exact ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).contDiff.comp_contDiffOn h).smul
      (forwardSpatialDerivative_smooth h j)
  apply hsum.congr
  intro z hz
  rw [convection_eq_sum_coordinateDerivative]
  apply Finset.sum_congr rfl
  intro j hj
  rw [forwardSpatialDerivative_slice h j z.1 hz z.2]

/-- A scalar pressure coefficient is duplicated in the three vector coordinates solely to reuse
the already proved vector Fourier-tower reconstruction. -/
def physicalPressureTimeTower (u : Velocity) (n : ℕ) (t : ℝ) : FourierCoeff :=
  fun k _ => pressureFromTransport k (datumFourierCoeff (physicalTimeJet n u t) k)

theorem physicalPressureTimeTower_derivative {u : Velocity} (h : SmoothVelocity u) :
    FourierTimeTowerDerivative (physicalPressureTimeTower u) := by
  intro n t ht k i
  have hc (j : Fin 3) := SmoothVelocity.fourierCoeff_hasDerivWithinAt (SmoothVelocity.physicalTimeJet h n) t ht k j
  unfold physicalPressureTimeTower pressureFromTransport
  by_cases hk : k = 0
  · simp only [hk, ite_true]
    exact hasDerivWithinAt_const t _ _
  · simp only [hk, ite_false]
    simpa only [physicalTimeJet] using!
      ((HasDerivWithinAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
        (hc j).const_mul (k j : ℂ))).const_mul Complex.I).div_const
          (((2 * Real.pi : ℝ) : ℂ) * ∑ j : Fin 3, (k j : ℂ) ^ 2)

theorem physicalPressureTimeTower_bounds {u : Velocity} (h : SmoothVelocity u)
    (hp : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)) :
    FourierTimeTowerBounds (physicalPressureTimeTower u) := by
  intro n m T hT
  obtain ⟨C, hC, hbound⟩ := SmoothVelocity.exists_uniform_smoothDatumDecayConstant (SmoothVelocity.physicalTimeJet h n) m T
  let W : ℝ := ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4
  have hW : 0 ≤ W := tsum_nonneg (fun _ => by positivity)
  refine ⟨3 * (9 * C ^ 2) * W, by positivity, ?_⟩
  intro t ht htT I
  apply finite_fourierIndex_sum_le_lattice_majorant
    (fun ki => ‖sobolevWeightedCoeff m (physicalPressureTimeTower u n t) ki‖ ^ 2)
    (9 * C ^ 2) (by positivity) _ I
  intro ki
  have hpoint (j : Fin 3) :
      torusSobolevWeight ki.1 ^ m * ‖datumFourierCoeff (physicalTimeJet n u t) ki.1 j‖ ≤
        C * (torusSobolevWeight ki.1)⁻¹ ^ 2 := by
    have he := smooth_datum_weightedCoeff_norm_le m (physicalTimeJet n u t)
      (SmoothVelocity.spatial_contDiff (SmoothVelocity.physicalTimeJet h n) t ht) (physicalTimeJet_periodic hp n t ht) (ki.1, j)
    rw [sobolevWeightedCoeff_norm_eq] at he
    exact he.trans (mul_le_mul_of_nonneg_right (hbound t ht htT) (by positivity))
  have hn : ‖sobolevWeightedCoeff m (physicalPressureTimeTower u n t) ki‖ ≤
      3 * C * (torusSobolevWeight ki.1)⁻¹ ^ 2 := by
    rw [sobolevWeightedCoeff_norm_eq]
    change torusSobolevWeight ki.1 ^ m *
      ‖pressureFromTransport ki.1 (datumFourierCoeff (physicalTimeJet n u t) ki.1)‖ ≤ _
    calc
      _ ≤ torusSobolevWeight ki.1 ^ m *
          (∑ j : Fin 3, ‖datumFourierCoeff (physicalTimeJet n u t) ki.1 j‖) :=
        mul_le_mul_of_nonneg_left (pressureFromTransport_norm_le _ _) (by positivity)
      _ = ∑ j : Fin 3, torusSobolevWeight ki.1 ^ m *
          ‖datumFourierCoeff (physicalTimeJet n u t) ki.1 j‖ := Finset.mul_sum ..
      _ ≤ ∑ _j : Fin 3, C * (torusSobolevWeight ki.1)⁻¹ ^ 2 :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = _ := by simp; ring
  calc
    _ ≤ (3 * C * (torusSobolevWeight ki.1)⁻¹ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by ring

/-- The actual pressure reconstruction of an arbitrary smooth periodic physical field is jointly
smooth, including the initial boundary. -/
theorem infiniteTransportPressure_joint_smooth {u : Velocity} (h : SmoothVelocity u)
    (hp : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)) :
    SmoothPressure (fun t => infiniteTransportPressure (datumFourierCoeff (u t))) := by
  have hs := Complex.reCLM.contDiff.comp_contDiffOn
    (fourierJetSynthesis_contDiffOn (physicalPressureTimeTower_derivative h)
      (physicalPressureTimeTower_bounds h hp) ⟨0, [], 0⟩)
  simpa only [fourierJetSynthesis, fourierJetTerm, fourierWordSymbol_nil,
    physicalPressureTimeTower, physicalTimeJet, one_mul, infiniteTransportPressure,
    realFourierSeries, scalarFourierSeries, infinitePressureCoefficient,
    Function.comp_apply] using! hs

def physicalConvectionPressure (u : Velocity) : Pressure :=
  fun t => infiniteTransportPressure (datumFourierCoeff (SingularClosure.convection (u t)))

theorem physicalConvectionPressure_smooth {u : Velocity} (h : SmoothVelocity u)
    (hp : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)) :
    SmoothPressure (physicalConvectionPressure u) :=
  infiniteTransportPressure_joint_smooth (SmoothVelocity.convection h)
    (fun t ht => convection_periodic (u t) (hp t ht))

theorem physicalConvectionPressure_periodic (u : Velocity) (t : ℝ) :
    SpatialPeriodic (physicalConvectionPressure u t) :=
  infiniteTransportPressure_periodic _

theorem physicalConvectionPressure_eq_fullTransportPressure
    {d : ℕ → ℝ → FourierCoeff} (hb : FourierTimeTowerBounds d)
    (t : ℝ) (ht : 0 ≤ t) (hr : SpectralReality (d 0 t)) (hs : SpectralSolenoidal (d 0 t)) :
    physicalConvectionPressure (fun r => smoothFourierSynthesis (d 0 r)) t =
      fullTransportPressure ⟨d 0 t, hb.mem_sobolev 0 0 t ht⟩ := by
  unfold physicalConvectionPressure fullTransportPressure
  rw [smoothFourierSynthesis_convection_coeff
    (⟨d 0 t, hb.mem_sobolev 0 0 t ht⟩ : TorusSobolev 0)
    (fun m => hb.mem_sobolev 0 m t ht) hr hs]

end
end QuantumAdapter.Obligations
