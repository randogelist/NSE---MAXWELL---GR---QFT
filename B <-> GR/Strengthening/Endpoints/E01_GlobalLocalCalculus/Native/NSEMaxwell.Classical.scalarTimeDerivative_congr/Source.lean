import NSEMaxwell.Classical

/-!
# Concrete kinematic lemmas

These lemmas use the actual Mathlib derivatives and the actual closed forward
spacetime domain. In particular, spatial slice smoothness is obtained by
composition with `x ↦ (t, x)`, and time-derivative congruence uses equality on
the entire nonnegative time domain, including its endpoint.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace NSEMaxwell.Classical

noncomputable section

theorem velocity_slice_smooth {u : Velocity} (hu : SmoothVelocity u)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (u t) := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) forwardSpacetime at hu
  have hslice : ContDiff ℝ ∞ (fun x : Vec => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hmem : ∀ x : Vec, (t, x) ∈ forwardSpacetime := fun _ => ht
  simpa only [Function.comp_def] using hu.comp_contDiff hslice hmem

theorem pressure_slice_smooth {p : Pressure} (hp : SmoothPressure p)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (p t) := by
  change ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) forwardSpacetime at hp
  have hslice : ContDiff ℝ ∞ (fun x : Vec => (t, x)) :=
    contDiff_const.prodMk contDiff_id
  have hmem : ∀ x : Vec, (t, x) ∈ forwardSpacetime := fun _ => ht
  simpa only [Function.comp_def] using hp.comp_contDiff hslice hmem

/-- Equality on nonnegative times suffices, including at the one-sided endpoint. -/
theorem timeDerivative_congr {u v : Velocity}
    (h : ∀ s : ℝ, 0 ≤ s → u s = v s)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    timeDerivative u t x = timeDerivative v t x := by
  unfold timeDerivative
  apply derivWithin_congr
  · intro s hs
    exact congrFun (h s hs) x
  · exact congrFun (h t ht) x

theorem timeDerivative_congr_field {u v : Velocity}
    (h : ∀ s : ℝ, 0 ≤ s → u s = v s)
    {t : ℝ} (ht : 0 ≤ t) :
    timeDerivative u t = timeDerivative v t := by
  funext x
  exact timeDerivative_congr h ht x

theorem scalarTimeDerivative_congr {p q : Pressure}
    (h : ∀ s : ℝ, 0 ≤ s → p s = q s)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    scalarTimeDerivative p t x = scalarTimeDerivative q t x := by
  unfold scalarTimeDerivative
  apply derivWithin_congr
  · intro s hs
    exact congrFun (h s hs) x
  · exact congrFun (h t ht) x

theorem scalarTimeDerivative_congr_field {p q : Pressure}
    (h : ∀ s : ℝ, 0 ≤ s → p s = q s)
    {t : ℝ} (ht : 0 ≤ t) :
    scalarTimeDerivative p t = scalarTimeDerivative q t := by
  funext x
  exact scalarTimeDerivative_congr h ht x

@[simp] theorem coordinateDerivative_const (a : Vec) (i : Fin 3) :
    coordinateDerivative (fun _ : Vec => a) i = 0 := by
  funext x
  simp [coordinateDerivative]

@[simp] theorem divergence_const (a : Vec) :
    divergence (fun _ : Vec => a) = 0 := by
  funext x
  simp [divergence, coordinateDerivative]

@[simp] theorem gradient_const (a : ℝ) :
    gradient (fun _ : Vec => a) = 0 := by
  funext x
  ext i
  change (fderiv ℝ (fun _ : Vec => a) x) (unitVector i) = 0
  simp

@[simp] theorem laplacian_const (a : Vec) :
    laplacian (fun _ : Vec => a) = 0 := by
  funext x
  simp [laplacian, coordinateDerivative]

@[simp] theorem convection_const (a : Vec) :
    convection (fun _ : Vec => a) = 0 := by
  funext x
  simp [convection]

@[simp] theorem spatialCurl_const (a : Vec) :
    spatialCurl (fun _ : Vec => a) = 0 := by
  funext x
  ext i
  simp [spatialCurl, coordinateDerivative, PiLp.toLp_apply]

@[simp] theorem coordinateDerivative_zero (i : Fin 3) :
    coordinateDerivative (0 : Field) i = 0 := by
  exact coordinateDerivative_const (0 : Vec) i

@[simp] theorem divergence_zero : divergence (0 : Field) = 0 := by
  exact divergence_const (0 : Vec)

@[simp] theorem gradient_zero : gradient (0 : ScalarField) = 0 := by
  exact gradient_const (0 : ℝ)

@[simp] theorem laplacian_zero : laplacian (0 : Field) = 0 := by
  exact laplacian_const (0 : Vec)

@[simp] theorem convection_zero : convection (0 : Field) = 0 := by
  exact convection_const (0 : Vec)

@[simp] theorem spatialCurl_zero : spatialCurl (0 : Field) = 0 := by
  exact spatialCurl_const (0 : Vec)

@[simp] theorem cross_zero_left (a : Vec) : cross 0 a = 0 := by
  ext i
  simp [cross, PiLp.toLp_apply]

@[simp] theorem cross_zero_right (a : Vec) : cross a 0 = 0 := by
  ext i
  simp [cross, PiLp.toLp_apply]

@[simp] theorem timeDerivative_const (a : Field) (t : ℝ) :
    timeDerivative (fun _ : ℝ => a) t = 0 := by
  funext x
  simp [timeDerivative]

@[simp] theorem scalarTimeDerivative_const (a : ScalarField) (t : ℝ) :
    scalarTimeDerivative (fun _ : ℝ => a) t = 0 := by
  funext x
  simp [scalarTimeDerivative]

@[simp] theorem spatialMean_zero : spatialMean (0 : Field) = 0 := by
  simp [spatialMean]

@[simp] theorem scalarMean_zero : scalarMean (0 : ScalarField) = 0 := by
  simp [scalarMean]

/-- Vanishing input needs no convergence premise: every series term vanishes. -/
@[simp] theorem vectorL_zero : vectorL (0 : Field) = 0 := by
  funext x
  simp [vectorL]

@[simp] theorem scalarL_zero : scalarL (0 : ScalarField) = 0 := by
  funext x
  simp [scalarL]

@[simp] theorem K_zero : K (0 : Field) = 0 := by
  simp [K]

@[simp] theorem U_zero (m : Vec) : U m (0 : Field) = fun _ : Vec => m := by
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

@[simp] theorem DG_zero_direction (ν : ℝ) (m : Vec) (B : Field) :
    DG ν m B (0 : Field) = 0 := by
  funext x
  simp [DG]

@[simp] theorem current_zero (ν c : ℝ) (m : Vec) :
    current ν c m (0 : Field) = 0 := by
  funext x
  simp [current]

theorem NSSolution.slice_data {ν : ℝ} {a : Field} {u : Velocity} {p : Pressure}
    (h : NSSolution ν a u p) {t : ℝ} (ht : 0 ≤ t) : Data (u t) := by
  exact ⟨velocity_slice_smooth h.velocity_smooth ht,
    h.velocity_periodic t ht, h.divergence_free t ht⟩

theorem MaxwellSolution.slice_magnetic_data
    {ν c : ℝ} {m : Vec} {B₀ : Field}
    {B E : Velocity} {ρ : Pressure} {J : Velocity}
    (h : MaxwellSolution ν c m B₀ B E ρ J)
    {t : ℝ} (ht : 0 ≤ t) : MagneticData (B t) := by
  exact ⟨⟨velocity_slice_smooth h.magnetic_smooth ht,
    h.magnetic_periodic t ht, h.magnetic_gauss t ht⟩,
    h.magnetic_mean_zero t ht⟩

end

end NSEMaxwell.Classical
