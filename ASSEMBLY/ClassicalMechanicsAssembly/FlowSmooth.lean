import ClassicalMechanics.TimeCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Closed-slab jet regularity

The statements in this module retain actual derivative and remainder hypotheses.
They do not construct the ODE jets or assert the flow-existence contract `L1`.
The final induction uses every label order at the preceding joint regularity
order; it does not assume the next joint regularity order.
-/

set_option autoImplicit false

namespace ClassicalMechanicsAssembly

open Set Filter ClassicalMechanics NSEMaxwell.Classical
open scoped Topology ContDiff

noncomputable section

section PathEvaluation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fixed-time evaluation preserves the actual label derivative of a path map. -/
theorem flowPath_hasFDerivAt_evaluation {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, F)}
    {A : Vec →L[ℝ] C(Icc (0 : ℝ) T, F)} {a : Vec}
    (hΓ : HasFDerivAt Γ A a) (t : Icc (0 : ℝ) T) :
    HasFDerivAt (fun b => Γ b t) ((ContinuousMap.evalCLM ℝ t).comp A) a := by
  exact (ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp a hΓ

/-- Fixed-time evaluation preserves all label regularity orders. -/
theorem flowPath_contDiff_evaluation {T : ℝ} {n : ℕ∞ω}
    {Γ : Vec → C(Icc (0 : ℝ) T, F)} (hΓ : ContDiff ℝ n Γ)
    (t : Icc (0 : ℝ) T) : ContDiff ℝ n (fun a => Γ a t) := by
  exact (ContinuousMap.evalCLM ℝ t).contDiff.comp hΓ

/-- Evaluation is jointly continuous on the closed time interval and labels. -/
theorem flowPath_continuous_evaluation {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, F)} (hΓ : Continuous Γ) :
    Continuous (fun z : Icc (0 : ℝ) T × Vec => Γ z.2 z.1) := by
  exact (hΓ.comp continuous_snd).eval continuous_fst

/-- A total representative inherits joint slab continuity from its path map. -/
theorem flowPath_continuousOn_representative {T : ℝ}
    {Γ : Vec → C(Icc (0 : ℝ) T, F)} (hΓ : Continuous Γ)
    {J : ℝ × Vec → F}
    (hJ : ∀ t (ht : t ∈ Icc (0 : ℝ) T) a, J (t, a) = Γ a ⟨t, ht⟩) :
    ContinuousOn J (finiteSpacetime T) := by
  rw [continuousOn_iff_continuous_restrict]
  have he : Continuous (fun z : finiteSpacetime T => Γ z.1.2 ⟨z.1.1, z.2⟩) := by
    exact (hΓ.comp continuous_subtype_val.snd).eval
      (continuous_subtype_val.fst.subtype_mk (fun z => z.2))
  convert he using 1
  funext z
  exact hJ z.1.1 z.2 z.1.2

end PathEvaluation

section JointDerivative

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual time-plus-label linear map used in the closed-slab increment. -/
def flowJointDerivative (p : F) (A : Vec →L[ℝ] F) : (ℝ × Vec) →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ ℝ Vec).smulRight p +
    A.comp (ContinuousLinearMap.snd ℝ ℝ Vec)

@[simp]
theorem flowJointDerivative_apply (p : F) (A : Vec →L[ℝ] F) (z : ℝ × Vec) :
    flowJointDerivative p A z = z.1 • p + A z.2 := rfl

/--
The joint derivative follows from the actual label derivative and the uniform
time-increment remainder. The latter remains an explicit analytic hypothesis;
ordinary pointwise time differentiability is not substituted for it.
-/
theorem flow_hasFDerivWithinAt_of_time_remainder {T : ℝ}
    {J : ℝ × Vec → F} {t : ℝ} {a : Vec} {p : F} {A : Vec →L[ℝ] F}
    (hlabel : HasFDerivAt (fun b => J (t, b)) A a)
    (htime : (fun z : ℝ × Vec => J z - J (t, z.2) - (z.1 - t) • p)
      =o[𝓝[finiteSpacetime T] (t, a)] (fun z => z - (t, a))) :
    HasFDerivWithinAt J (flowJointDerivative p A) (finiteSpacetime T) (t, a) := by
  have hg : HasFDerivWithinAt (fun z : ℝ × Vec => J z - J (t, z.2))
      ((ContinuousLinearMap.fst ℝ ℝ Vec).smulRight p)
      (finiteSpacetime T) (t, a) := by
    apply HasFDerivWithinAt.of_isLittleO
    simpa using htime
  have hl : HasFDerivAt (fun z : ℝ × Vec => J (t, z.2))
      (A.comp (ContinuousLinearMap.snd ℝ ℝ Vec)) (t, a) := by
    have hs : HasFDerivAt (fun z : ℝ × Vec => z.2)
        (ContinuousLinearMap.snd ℝ ℝ Vec) (t, a) :=
      (ContinuousLinearMap.snd ℝ ℝ Vec).hasFDerivAt
    simpa only [Function.comp_def] using hlabel.comp (t, a) hs
  simpa only [Pi.add_apply, sub_add_cancel, flowJointDerivative] using
    hg.add hl.hasFDerivWithinAt

end JointDerivative

/-- Label jets use the actual finite-dimensional continuous multilinear spaces. -/
abbrev FlowJet (r : ℕ) := Vec [×r]→L[ℝ] Vec

/-- The derivative field `τ Pᵣ + Jᵣ₊₁(h,...)` of the joint jet induction. -/
def flowJetDerivative (r : ℕ) (p : FlowJet r) (next : FlowJet (r + 1)) :
    (ℝ × Vec) →L[ℝ] FlowJet r :=
  flowJointDerivative p next.curryLeft

/-- Currying and assembly of a joint jet derivative preserve finite regularity. -/
theorem flowJetDerivative_contDiffOn {T : ℝ} {r : ℕ} {n : ℕ∞ω}
    {P : ℝ × Vec → FlowJet r} {J : ℝ × Vec → FlowJet (r + 1)}
    (hP : ContDiffOn ℝ n P (finiteSpacetime T))
    (hJ : ContDiffOn ℝ n J (finiteSpacetime T)) :
    ContDiffOn ℝ n (fun z => flowJetDerivative r (P z) (J z))
      (finiteSpacetime T) := by
  have hc : ContDiffOn ℝ n (fun z => (J z).curryLeft) (finiteSpacetime T) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r + 1) => Vec) Vec).contDiff
      |>.comp_contDiffOn hJ
  exact (contDiffOn_const.smulRight hP).add (hc.clm_comp contDiffOn_const)

/--
Simultaneous finite-order induction for actual joint jets on the closed slab.
`hforcing` is the explicit remaining regularity closure of the forcing terms;
the ODE partition formulas must discharge it in a concrete flow construction.
-/
theorem flowJet_tower_contDiffOn {T : ℝ} (hT : 0 < T)
    (J P : ∀ r : ℕ, ℝ × Vec → FlowJet r)
    (hcontinuous : ∀ r, ContinuousOn (J r) (finiteSpacetime T))
    (hderiv : ∀ r z, z ∈ finiteSpacetime T →
      HasFDerivWithinAt (J r) (flowJetDerivative r (P r z) (J (r + 1) z))
        (finiteSpacetime T) z)
    (hforcing : ∀ n : ℕ,
      (∀ r, ContDiffOn ℝ n (J r) (finiteSpacetime T)) →
      ∀ r, ContDiffOn ℝ n (P r) (finiteSpacetime T)) :
    ∀ r, ContDiffOn ℝ ∞ (J r) (finiteSpacetime T) := by
  have hall : ∀ n : ℕ, ∀ r, ContDiffOn ℝ n (J r) (finiteSpacetime T) := by
    intro n
    induction n with
    | zero =>
        intro r
        exact contDiffOn_zero.mpr (hcontinuous r)
    | succ n ih =>
        intro r
        have hd : ContDiffOn ℝ n
            (fun z => flowJetDerivative r (P r z) (J (r + 1) z))
            (finiteSpacetime T) :=
          flowJetDerivative_contDiffOn (hforcing n ih r) (ih (r + 1))
        have hs : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (J r) (finiteSpacetime T) :=
          (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
            (uniqueDiffOn_finiteSpacetime hT)).mpr
              ⟨by simp, _, hd, hderiv r⟩
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hs
  intro r
  exact contDiffOn_infty.mpr (fun n => hall n r)

/--
Concrete velocity regularity follows from the zeroth actual jet. The derivative
and forcing hypotheses remain visible; this theorem does not assert `L1`.
-/
theorem smoothVelocityOn_of_flowJet_tower {T : ℝ} (hT : 0 < T)
    {η : Velocity} (J P : ∀ r : ℕ, ℝ × Vec → FlowJet r)
    (hcontinuous : ∀ r, ContinuousOn (J r) (finiteSpacetime T))
    (hderiv : ∀ r z, z ∈ finiteSpacetime T →
      HasFDerivWithinAt (J r) (flowJetDerivative r (P r z) (J (r + 1) z))
        (finiteSpacetime T) z)
    (hforcing : ∀ n : ℕ,
      (∀ r, ContDiffOn ℝ n (J r) (finiteSpacetime T)) →
      ∀ r, ContDiffOn ℝ n (P r) (finiteSpacetime T))
    (hzero : ∀ z ∈ finiteSpacetime T,
      η z.1 z.2 = continuousMultilinearCurryFin0 ℝ Vec Vec (J 0 z)) :
    SmoothVelocityOn T η := by
  have hj := flowJet_tower_contDiffOn hT J P hcontinuous hderiv hforcing 0
  have hv := (continuousMultilinearCurryFin0 ℝ Vec Vec).contDiff.comp_contDiffOn hj
  exact hv.congr hzero

end

end ClassicalMechanicsAssembly
