import MaxwellEndpoint.System

/-!
# Native constrained-Maxwell endpoints

Every operator in this module is the concrete Mathlib-derivative, integral,
or Fourier-series operator in `NSEMaxwell.Classical`. No NSE adapter or
unproved Hodge instance is imported.

The zero-field solution is an actual unconditional instance, for arbitrary
viscosity, wave speed, and harmonic velocity mean. It does not assert the
global existence proposition `MaxwellB` for arbitrary magnetic data.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace MaxwellEndpoint

open NSEMaxwell.Classical

noncomputable section

/-- The four native differential equations, on the full nonnegative time domain. -/
def MaxwellEquations (c : ℝ) (B E : Velocity) (ρ : Pressure) (J : Velocity) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (B t) x = 0) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative B t x + spatialCurl (E t) x = 0) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (E t) x = ρ t x) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative E t x - c ^ 2 • spatialCurl (B t) x = -J t x)

theorem equations_of_solution
    (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity)
    (h : MaxwellSolution ν c m B₀ B E ρ J) :
    MaxwellEquations c B E ρ J :=
  ⟨h.magnetic_gauss, h.faraday, h.electric_gauss, h.ampere⟩

/-- Electric field, charge, and current are fixed by the magnetic trajectory. -/
theorem constitutive_fields_of_solution
    (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity)
    (h : MaxwellSolution ν c m B₀ B E ρ J) :
    ∀ t : ℝ, 0 ≤ t →
      E t = G ν m (B t) ∧
      ρ t = Q ν m (B t) ∧
      J t = current ν c m (B t) := by
  intro t ht
  exact ⟨h.constitutive_electric t ht,
    h.constitutive_charge t ht, h.constitutive_current t ht⟩

/-- Faraday gives the exact prescribed magnetic evolution, including at zero. -/
theorem magnetic_evolution_of_solution
    (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity)
    (h : MaxwellSolution ν c m B₀ B E ρ J)
    (t : ℝ) (ht : 0 ≤ t) :
    timeDerivative B t = V ν m (B t) := by
  funext x
  have hF := h.faraday t ht x
  rw [h.constitutive_electric t ht] at hF
  change timeDerivative B t x = -spatialCurl (G ν m (B t)) x
  calc
    timeDerivative B t x =
        (timeDerivative B t x + spatialCurl (G ν m (B t)) x) -
          spatialCurl (G ν m (B t)) x := by abel
    _ = -spatialCurl (G ν m (B t)) x := by rw [hF]; simp

/-- Ampere and the induced current determine the exact electric evolution. -/
theorem electric_evolution_of_solution
    (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity)
    (h : MaxwellSolution ν c m B₀ B E ρ J)
    (t : ℝ) (ht : 0 ≤ t) :
    timeDerivative E t = DG ν m (B t) (V ν m (B t)) := by
  funext x
  have hA := h.ampere t ht x
  rw [h.constitutive_current t ht] at hA
  change timeDerivative E t x - c ^ 2 • spatialCurl (B t) x =
    -(c ^ 2 • spatialCurl (B t) x - DG ν m (B t) (V ν m (B t)) x) at hA
  calc
    timeDerivative E t x =
        (timeDerivative E t x - c ^ 2 • spatialCurl (B t) x) +
          c ^ 2 • spatialCurl (B t) x := by abel
    _ = -(c ^ 2 • spatialCurl (B t) x -
        DG ν m (B t) (V ν m (B t)) x) +
          c ^ 2 • spatialCurl (B t) x := by rw [hA]
    _ = DG ν m (B t) (V ν m (B t)) x := by abel

/-- The endpoint is the exact concrete quantified proposition. -/
theorem maxwellB_iff_native (ν c : ℝ) :
    MaxwellB ν c ↔
      ∀ (m : Vec) (B₀ : Field), MagneticData B₀ →
        ∃ (B E : Velocity) (ρ : Pressure) (J : Velocity),
          MaxwellSolution ν c m B₀ B E ρ J :=
  Iff.rfl

@[simp] theorem coordinateDerivative_zero (i : Fin 3) :
    coordinateDerivative (0 : Field) i = 0 := by
  funext x
  simp [coordinateDerivative]

@[simp] theorem divergence_zero : divergence (0 : Field) = 0 := by
  funext x
  simp [divergence]

@[simp] theorem spatialCurl_zero : spatialCurl (0 : Field) = 0 := by
  funext x
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [spatialCurl, PiLp.toLp_apply]

@[simp] theorem cross_zero_left (a : Vec) : cross 0 a = 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [cross, PiLp.toLp_apply]

@[simp] theorem cross_zero_right (a : Vec) : cross a 0 = 0 := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [cross, PiLp.toLp_apply]

@[simp] theorem vectorL_zero : vectorL (0 : Field) = 0 := by
  funext x
  simp [vectorL]

@[simp] theorem scalarL_zero : scalarL (0 : ScalarField) = 0 := by
  funext x
  simp [scalarL]

@[simp] theorem K_zero : K (0 : Field) = 0 := by
  simp [K]

@[simp] theorem U_zero (m : Vec) :
    U m (0 : Field) = (fun _ : Vec => m) := by
  funext x
  simp [U]

@[simp] theorem G_zero (ν : ℝ) (m : Vec) : G ν m (0 : Field) = 0 := by
  funext x
  simp [G]

@[simp] theorem V_zero (ν : ℝ) (m : Vec) : V ν m (0 : Field) = 0 := by
  funext x
  simp [V]

@[simp] theorem Q_zero (ν : ℝ) (m : Vec) : Q ν m (0 : Field) = 0 := by
  simp [Q]

@[simp] theorem DG_zero (ν : ℝ) (m : Vec) (B : Field) :
    DG ν m B (0 : Field) = 0 := by
  funext x
  simp [DG]

@[simp] theorem current_zero (ν c : ℝ) (m : Vec) :
    current ν c m (0 : Field) = 0 := by
  funext x
  simp [current]

@[simp] theorem timeDerivative_zero : timeDerivative (0 : Velocity) = 0 := by
  funext t x
  simp [timeDerivative]

/-- The actual zero field belongs to the native magnetic-data class. -/
theorem magneticData_zero : MagneticData (0 : Field) where
  smooth := contDiff_const
  periodic := by intro x i; rfl
  divergence_free := by intro x; simp
  mean_zero := by simp [spatialMean]

/-- A complete concrete solution instance, independent of every Hodge obligation. -/
theorem zero_solution (ν c : ℝ) (m : Vec) :
    MaxwellSolution ν c m (0 : Field)
      (0 : Velocity) (0 : Velocity) (0 : Pressure) (0 : Velocity) where
  magnetic_smooth := contDiffOn_const
  electric_smooth := contDiffOn_const
  charge_smooth := contDiffOn_const
  current_smooth := contDiffOn_const
  magnetic_periodic := by intro t ht x i; rfl
  electric_periodic := by intro t ht x i; rfl
  charge_periodic := by intro t ht x i; rfl
  current_periodic := by intro t ht x i; rfl
  magnetic_mean_zero := by intro t ht; simp [spatialMean]
  magnetic_gauss := by intro t ht x; simp
  faraday := by intro t ht x; simp
  electric_gauss := by intro t ht x; simp
  ampere := by intro t ht x; simp
  constitutive_electric := by intro t ht; simp
  constitutive_charge := by intro t ht; simp
  constitutive_current := by intro t ht; simp
  initial := rfl

/-- Nonempty native solution class for the admissible zero magnetic datum. -/
theorem zero_datum_global_instance (ν c : ℝ) (m : Vec) :
    MagneticData (0 : Field) ∧
      ∃ (B E : Velocity) (ρ : Pressure) (J : Velocity),
        MaxwellSolution ν c m (0 : Field) B E ρ J :=
  ⟨magneticData_zero, 0, 0, 0, 0, zero_solution ν c m⟩

end

end MaxwellEndpoint
