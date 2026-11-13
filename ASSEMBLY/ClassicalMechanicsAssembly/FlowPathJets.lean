import ClassicalMechanicsAssembly.FlowSmooth
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual label jets of a smooth path-valued map

The jets are the evaluated iterated Fréchet derivatives of the supplied map
into `C([0,T], Vec)`. Finite-dimensionality of the label space supplies the
joint operator-norm continuity through multilinear currying.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set ClassicalMechanics NSEMaxwell.Classical
open scoped Topology ContDiff

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- A continuous family of path-valued multilinear maps evaluates jointly continuously. -/
theorem flow_multilinearPath_continuous_evaluation {T : ℝ}
    {X : Type*} [TopologicalSpace X] :
    ∀ r : ℕ, ∀ L : X → Vec [×r]→L[ℝ] C(Icc (0 : ℝ) T, Vec),
      Continuous L → Continuous (fun z : Icc (0 : ℝ) T × X =>
        (ContinuousMap.evalCLM ℝ z.1).compContinuousMultilinearMap (L z.2)) := by
  intro r
  induction r with
  | zero =>
      intro L hL
      have hc : Continuous (fun z : Icc (0 : ℝ) T × X =>
          ((ContinuousMap.evalCLM ℝ z.1).compContinuousMultilinearMap (L z.2)).curry0) := by
        exact (((continuousMultilinearCurryFin0 ℝ Vec
          C(Icc (0 : ℝ) T, Vec)).continuous.comp hL).comp continuous_snd).eval continuous_fst
      have hb := (continuousMultilinearCurryFin0 ℝ Vec Vec).symm.continuous.comp hc
      simpa only [Function.comp_def, continuousMultilinearCurryFin0_symm_apply,
        ContinuousMultilinearMap.uncurry0_curry0] using hb
  | succ r ih =>
      intro L hL
      let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Vec) Vec
      have hc : Continuous (fun z : Icc (0 : ℝ) T × X =>
          e ((ContinuousMap.evalCLM ℝ z.1).compContinuousMultilinearMap (L z.2))) := by
        apply continuous_clm_apply.mpr
        intro h
        have hh : Continuous (fun x => (L x).curryLeft h) :=
          (ContinuousLinearMap.apply ℝ (Vec [×r]→L[ℝ] C(Icc (0 : ℝ) T, Vec)) h).continuous.comp
              ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Vec)
                C(Icc (0 : ℝ) T, Vec)).continuous.comp hL)
        convert ih (fun x => (L x).curryLeft h) hh using 1 <;> rfl
      have hb := e.symm.continuous.comp hc
      simpa only [Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using hb

/-- The actual evaluated `r`th label derivative of a continuous-path family. -/
def evaluatedFlowJet {T : ℝ} (Γ : Vec → C(Icc (0 : ℝ) T, Vec))
    (r : ℕ) (t : Icc (0 : ℝ) T) (a : Vec) : FlowJet r :=
  (ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap (iteratedFDeriv ℝ r Γ a)

/-- The actual evaluated jets are jointly continuous, including endpoint times. -/
theorem evaluatedFlowJet_continuous {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ) (r : ℕ) :
    Continuous (fun z : Icc (0 : ℝ) T × Vec => evaluatedFlowJet Γ r z.1 z.2) := by
  exact flow_multilinearPath_continuous_evaluation r (iteratedFDeriv ℝ r Γ)
    (ContDiff.continuous_iteratedFDeriv (n := ∞)
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl r) hΓ)

/-- Differentiating an evaluated actual jet gives the curried next actual jet. -/
theorem evaluatedFlowJet_hasFDerivAt {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, Vec)} (hΓ : ContDiff ℝ ∞ Γ)
    (r : ℕ) (t : Icc (0 : ℝ) T) (a : Vec) :
    HasFDerivAt (evaluatedFlowJet Γ r t)
      (evaluatedFlowJet Γ (r + 1) t a).curryLeft a := by
  let post := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin r => Vec) C(Icc (0 : ℝ) T, Vec) Vec (ContinuousMap.evalCLM ℝ t)
  have hd := ((ContDiff.differentiable_iteratedFDeriv (n := ∞) (m := r)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl r) hΓ) a).hasFDerivAt
  have he : post.comp (fderiv ℝ (iteratedFDeriv ℝ r Γ) a) =
      (evaluatedFlowJet Γ (r + 1) t a).curryLeft := by
    ext h v
    rfl
  exact (post.hasFDerivAt.comp a hd).congr_fderiv he

/-- The zeroth actual evaluated jet represents the path value exactly. -/
theorem evaluatedFlowJet_zero {T : ℝ}
    (Γ : Vec → C(Icc (0 : ℝ) T, Vec)) (t : Icc (0 : ℝ) T) (a : Vec) :
    continuousMultilinearCurryFin0 ℝ Vec Vec (evaluatedFlowJet Γ 0 t a) = Γ a t := by
  rfl

end

end ClassicalMechanicsAssembly
