import GRAssembly.NativeCKNormalization
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
Coordinate invariance of the literal first-order analytic CK problem.
The final theorem consumes LI01 explicitly. No new analytic existence result
is inserted by changing the finite-dimensional coordinate representation.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.NativeLiterature

noncomputable section

variable {E V E' V' : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup V'] [NormedSpace ℝ V'] [CompleteSpace V']

def ckTimeEquiv (e : E ≃L[ℝ] E') : (ℝ × E) ≃L[ℝ] (ℝ × E') :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e

def ckJetEquiv (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V') :
    CKJet E V ≃L[ℝ] CKJet E' V' :=
  (ckTimeEquiv e).prodCongr (a.prodCongr (e.arrowCongr a))

def ckTransformInitial (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (u₀ : E → V) : E' → V' := fun x => a (u₀ (e.symm x))

def ckTransformSolution (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (u : ℝ × E → V) : ℝ × E' → V' := fun z => a (u (z.1, e.symm z.2))

def ckTransformRHS (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (F : CKRHS E V) : CKRHS E' V' := fun J => a (F ((ckJetEquiv e a).symm J))

@[simp] theorem ckTimeEquiv_apply (e : E ≃L[ℝ] E') (z : ℝ × E) :
    ckTimeEquiv e z = (z.1, e z.2) := rfl

@[simp] theorem ckTimeEquiv_symm_apply (e : E ≃L[ℝ] E') (z : ℝ × E') :
    (ckTimeEquiv e).symm z = (z.1, e.symm z.2) := rfl

@[simp] theorem ckJetEquiv_apply (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (J : CKJet E V) :
    ckJetEquiv e a J = ((J.1.1, e J.1.2), (a J.2.1, (e.arrowCongr a) J.2.2)) := rfl

@[simp] theorem ckJetEquiv_symm_apply (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (J : CKJet E' V') :
    (ckJetEquiv e a).symm J =
      ((J.1.1, e.symm J.1.2), (a.symm J.2.1, (e.symm.arrowCongr a.symm) J.2.2)) := rfl

theorem ckTransformInitial_fderiv (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (u₀ : E → V) (x : E') :
    fderiv ℝ (ckTransformInitial e a u₀) x =
      (e.arrowCongr a) (fderiv ℝ u₀ (e.symm x)) := by
  change fderiv ℝ (a ∘ (u₀ ∘ e.symm)) x = _
  rw [a.comp_fderiv, e.symm.comp_right_fderiv]
  rfl

theorem ckTransformSolution_spaceDerivative (e : E ≃L[ℝ] E')
    (a : V ≃L[ℝ] V') (u : ℝ × E → V) (z : ℝ × E') :
    fderiv ℝ (fun x => ckTransformSolution e a u (z.1, x)) z.2 =
      (e.arrowCongr a) (fderiv ℝ (fun x => u (z.1, x)) (e.symm z.2)) :=
  ckTransformInitial_fderiv e a (fun x => u (z.1, x)) z.2

theorem ckTransformSolution_timeDerivative (e : E ≃L[ℝ] E')
    (a : V ≃L[ℝ] V') (u : ℝ × E → V) (z : ℝ × E') :
    deriv (fun t => ckTransformSolution e a u (t, z.2)) z.1 =
      a (deriv (fun t => u (t, e.symm z.2)) z.1) := by
  change (fderiv ℝ (a ∘ (fun t => u (t, e.symm z.2))) z.1) 1 = _
  rw [a.comp_fderiv]
  rfl

theorem ckTransformInitial_analyticAt (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    {u₀ : E → V} {x₀ : E} (hu₀ : AnalyticAt ℝ u₀ x₀) :
    AnalyticAt ℝ (ckTransformInitial e a u₀) (e x₀) := by
  have hx : AnalyticAt ℝ u₀ (e.symm (e x₀)) := by simpa using hu₀
  exact (a.toContinuousLinearMap.analyticAt _).comp
    (hx.comp (e.symm.toContinuousLinearMap.analyticAt _))

theorem ckTransformSolution_analyticAt (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    {u : ℝ × E → V} {z : ℝ × E} (hu : AnalyticAt ℝ u z) :
    AnalyticAt ℝ (ckTransformSolution e a u) (ckTimeEquiv e z) := by
  have hz : AnalyticAt ℝ u ((ckTimeEquiv e).symm (ckTimeEquiv e z)) := by
    simpa using hu
  exact (a.toContinuousLinearMap.analyticAt _).comp
    (hz.comp ((ckTimeEquiv e).symm.toContinuousLinearMap.analyticAt _))

theorem ckTransformInitial_jet (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (u₀ : E → V) (t₀ : ℝ) (x₀ : E) :
    ckInitialJet t₀ (e x₀) (ckTransformInitial e a u₀) =
      ckJetEquiv e a (ckInitialJet t₀ x₀ u₀) := by
  simp [ckInitialJet, ckTransformInitial_fderiv, ckTransformInitial]

theorem ckTransformRHS_analyticAt (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    {F : CKRHS E V} {u₀ : E → V} {t₀ : ℝ} {x₀ : E}
    (hF : AnalyticAt ℝ F (ckInitialJet t₀ x₀ u₀)) :
    AnalyticAt ℝ (ckTransformRHS e a F)
      (ckInitialJet t₀ (e x₀) (ckTransformInitial e a u₀)) := by
  rw [ckTransformInitial_jet]
  have hJ : AnalyticAt ℝ F
      ((ckJetEquiv e a).symm (ckJetEquiv e a (ckInitialJet t₀ x₀ u₀))) := by
    simpa using hF
  exact (a.toContinuousLinearMap.analyticAt _).comp
    (hJ.comp ((ckJetEquiv e a).symm.toContinuousLinearMap.analyticAt _))

theorem ckTransformSolution_isSolution (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    {F : CKRHS E V} {u₀ : E → V} {t₀ : ℝ} {x₀ : E} {u : ℝ × E → V}
    (hu : CKLocalSolution F u₀ t₀ x₀ u) :
    CKLocalSolution (ckTransformRHS e a F) (ckTransformInitial e a u₀)
      t₀ (e x₀) (ckTransformSolution e a u) := by
  have hx : Tendsto e.symm (𝓝 (e x₀)) (𝓝 x₀) := by
    simpa using e.symm.continuous.continuousAt.tendsto
  have hz : Tendsto (ckTimeEquiv e).symm (𝓝 (t₀, e x₀)) (𝓝 (t₀, x₀)) := by
    simpa using (ckTimeEquiv e).symm.continuous.continuousAt.tendsto
  refine ⟨ckTransformSolution_analyticAt e a hu.analytic, ?_, ?_⟩
  · filter_upwards [hx.eventually hu.initial] with x hux
    exact congrArg a hux
  · filter_upwards [hz.eventually hu.equation] with z hzu
    rw [ckTransformSolution_timeDerivative, ckTransformSolution_spaceDerivative]
    simpa [ckTransformRHS, ckTransformSolution, ContinuousLinearEquiv.arrowCongr_apply]
      using congrArg a hzu

@[simp] theorem ckTransformInitial_inverse (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (u₀ : E → V) :
    ckTransformInitial e.symm a.symm (ckTransformInitial e a u₀) = u₀ := by
  funext x
  simp [ckTransformInitial]

@[simp] theorem ckTransformSolution_inverse (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (u : ℝ × E → V) :
    ckTransformSolution e.symm a.symm (ckTransformSolution e a u) = u := by
  funext z
  simp [ckTransformSolution]

@[simp] theorem ckTransformRHS_inverse (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    (F : CKRHS E V) : ckTransformRHS e.symm a.symm (ckTransformRHS e a F) = F := by
  funext J
  simp only [ckTransformRHS, ckJetEquiv_symm_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.symm_apply_apply]
  congr 2
  ext x
  simp

theorem ckTransformSolution_germ (e : E ≃L[ℝ] E') (a : V ≃L[ℝ] V')
    {u v : ℝ × E → V} {z : ℝ × E} (h : u =ᶠ[𝓝 z] v) :
    ckTransformSolution e a u =ᶠ[𝓝 (ckTimeEquiv e z)] ckTransformSolution e a v := by
  have ht : Tendsto (ckTimeEquiv e).symm (𝓝 (ckTimeEquiv e z)) (𝓝 z) := by
    simpa using (ckTimeEquiv e).symm.continuous.continuousAt.tendsto
  filter_upwards [ht.eventually h] with y hy
  exact congrArg a hy

/-- Literal LI01 implies its coordinate-free finite-dimensional version. -/
theorem ckLocal_exists_unique_of_literatureCK
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [Nontrivial E] [Nontrivial V]
    (input : LiteratureAnalyticCKInput)
    (F : CKRHS E V) (u₀ : E → V) (t₀ : ℝ) (x₀ : E)
    (hu₀ : AnalyticAt ℝ u₀ x₀)
    (hF : AnalyticAt ℝ F (ckInitialJet t₀ x₀ u₀)) :
    ∃ u : ℝ × E → V, CKLocalSolution F u₀ t₀ x₀ u ∧
      ∀ v : ℝ × E → V, CKLocalSolution F u₀ t₀ x₀ v → u =ᶠ[𝓝 (t₀, x₀)] v := by
  let e : E ≃L[ℝ] LiteratureSpace (Module.finrank ℝ E) := toEuclidean
  let a : V ≃L[ℝ] LiteratureSpace (Module.finrank ℝ V) := toEuclidean
  obtain ⟨u, hu, huniq⟩ := input.exists_unique
    (Module.finrank ℝ E) (Module.finrank ℝ V)
    Module.finrank_pos Module.finrank_pos
    (ckTransformRHS e a F) (ckTransformInitial e a u₀) t₀ (e x₀)
    (ckTransformInitial_analyticAt e a hu₀) (ckTransformRHS_analyticAt e a hF)
  have hu' : CKLocalSolution (ckTransformRHS e a F) (ckTransformInitial e a u₀)
      t₀ (e x₀) u := ⟨hu.analytic, hu.initial, hu.equation⟩
  refine ⟨ckTransformSolution e.symm a.symm u, ?_, ?_⟩
  · simpa using ckTransformSolution_isSolution e.symm a.symm hu'
  · intro v hv
    have hv' := ckTransformSolution_isSolution e a hv
    have heq := huniq (ckTransformSolution e a v)
      ⟨hv'.analytic, hv'.initial, hv'.equation⟩
    simpa using ckTransformSolution_germ e.symm a.symm heq

end

end NSEGR.NativeLiterature
