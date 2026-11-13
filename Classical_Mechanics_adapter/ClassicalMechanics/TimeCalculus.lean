import ClassicalMechanics.FiniteSlab

/-! Native chain rules on the closed finite slab, including both endpoints. -/

set_option autoImplicit false

namespace ClassicalMechanics

open NSEMaxwell.Classical Set
open scoped ContDiff

noncomputable section

theorem uniqueDiffOn_finiteSpacetime {T : ℝ} (hT : 0 < T) :
    UniqueDiffOn ℝ (finiteSpacetime T) := by
  have heq : finiteSpacetime T = Icc (0 : ℝ) T ×ˢ (univ : Set Vec) := by
    ext z
    simp [finiteSpacetime]
  rw [heq]
  exact (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ

theorem finite_spatial_restriction_fderiv {T : ℝ} {u : Velocity}
    (hu : SmoothVelocityOn T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (x v : Vec) :
    fderiv ℝ (u t) x v =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (finiteSpacetime T) (t, x) (0, v) := by
  have hd := (hu.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt
  have he := (hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x)
  have hc := hd.comp_hasFDerivAt x he (Filter.Eventually.of_forall (fun _ => ht))
  have hv := congrArg (fun L : Vec →L[ℝ] Vec => L v) hc.fderiv
  simpa [Function.comp_def] using hv

theorem finite_time_hasDerivWithinAt {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Vec) :
    HasDerivWithinAt (fun s : ℝ => u s x)
      (finiteTimeDerivative T u t x) (Icc (0 : ℝ) T) t := by
  have hd := (hu.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt
  have he : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) (Icc 0 T) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have hc := hd.comp_hasDerivWithinAt t he (fun _ hs => hs)
  have hv := hc.derivWithin (uniqueDiffOn_Icc hT t ht)
  change derivWithin (fun s : ℝ => u s x) (Icc (0 : ℝ) T) t = _ at hv
  rw [← hv] at hc
  exact hc

theorem finite_time_restriction_fderiv {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Vec) :
    finiteTimeDerivative T u t x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (finiteSpacetime T) (t, x) (1, 0) := by
  have hd := (hu.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt
  have he : HasDerivWithinAt (fun s : ℝ => (s, x)) (1, 0) (Icc 0 T) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  exact (hd.comp_hasDerivWithinAt t he (fun _ hs => hs)).derivWithin
    (uniqueDiffOn_Icc hT t ht)

theorem finiteTimeDerivative_congr {T : ℝ} {u v : Velocity}
    (h : ∀ s ∈ Icc (0 : ℝ) T, u s = v s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Vec) :
    finiteTimeDerivative T u t x = finiteTimeDerivative T v t x := by
  unfold finiteTimeDerivative
  apply derivWithin_congr
  · intro s hs
    exact congrFun (h s hs) x
  · exact congrFun (h t ht) x

/-- The actual derivative of a velocity field along a supplied integral curve. -/
theorem finite_material_chain_rule {T : ℝ} (hT : 0 < T)
    {u : Velocity} (hu : SmoothVelocityOn T u) {eta : ℝ → Vec}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (heta : HasDerivWithinAt eta (u t (eta t)) (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt (fun s : ℝ => u s (eta s))
      (finiteMaterialAcceleration T u t (eta t)) (Icc (0 : ℝ) T) t := by
  have hd := (hu.differentiableOn (by simp) (t, eta t) ht).hasFDerivWithinAt
  have he := (hasDerivAt_id t).hasDerivWithinAt.prodMk heta
  have hc := hd.comp_hasDerivWithinAt t he (fun _ hs => hs)
  have hv :
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
          (finiteSpacetime T) (t, eta t) (1, u t (eta t)) =
        finiteMaterialAcceleration T u t (eta t) := by
    rw [show (1, u t (eta t)) = (1, (0 : Vec)) + (0, u t (eta t)) by simp,
      map_add]
    rw [← finite_time_restriction_fderiv hT hu ht (eta t),
      ← finite_spatial_restriction_fderiv hu ht (eta t) (u t (eta t))]
    rfl
  rw [hv] at hc
  exact hc

/-- Acceleration pullback follows from actual smoothness and the flow ODE. -/
theorem finite_flow_acceleration {T : ℝ} (hT : 0 < T)
    {u eta : Velocity} (hu : SmoothVelocityOn T u) (heta : SmoothVelocityOn T eta)
    (hflow : ∀ s ∈ Icc (0 : ℝ) T, ∀ a : Vec,
      finiteTimeDerivative T eta s a = u s (eta s a))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Vec) :
    finiteTimeDerivative T (finiteTimeDerivative T eta) t a =
      finiteMaterialAcceleration T u t (eta t a) := by
  have he := finite_time_hasDerivWithinAt hT heta ht a
  rw [hflow t ht a] at he
  have hc := finite_material_chain_rule hT hu ht he
  have hd := hc.derivWithin (uniqueDiffOn_Icc hT t ht)
  calc
    finiteTimeDerivative T (finiteTimeDerivative T eta) t a =
        finiteTimeDerivative T (fun s b => u s (eta s b)) t a := by
      apply finiteTimeDerivative_congr _ ht a
      intro s hs
      funext b
      exact hflow s hs b
    _ = finiteMaterialAcceleration T u t (eta t a) := hd

end

end ClassicalMechanics
