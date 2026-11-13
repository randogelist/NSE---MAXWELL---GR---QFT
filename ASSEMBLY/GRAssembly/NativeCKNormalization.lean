import GRAdapter.LiteratureInputs

/-!
Affine normalization of the literal finite-dimensional analytic CK problem.
All operators are actual derivatives. No CK existence theorem is assumed.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1600000

open Set Filter
open scoped Topology ContDiff

namespace NSEGR.NativeLiterature

noncomputable section

variable {E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

abbrev CKJet (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  (ℝ × E) × (V × (E →L[ℝ] V))

abbrev CKRHS (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] := CKJet E V → V

def ckInitialJet (t₀ : ℝ) (x₀ : E) (u₀ : E → V) : CKJet E V :=
  ((t₀, x₀), (u₀ x₀, fderiv ℝ u₀ x₀))

structure CKLocalSolution (F : CKRHS E V) (u₀ : E → V)
    (t₀ : ℝ) (x₀ : E) (u : ℝ × E → V) : Prop where
  analytic : AnalyticAt ℝ u (t₀, x₀)
  initial : ∀ᶠ x in 𝓝 x₀, u (t₀, x) = u₀ x
  equation : ∀ᶠ z in 𝓝 (t₀, x₀),
    deriv (fun t : ℝ => u (t, z.2)) z.1 =
      F (z, (u z, fderiv ℝ (fun x => u (z.1, x)) z.2))

def ckInitialVelocity (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) : V :=
  F (ckInitialJet t₀ x₀ u₀)

def ckNormalizeJet (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (J : CKJet E V) : CKJet E V :=
  ((t₀ + J.1.1, x₀ + J.1.2),
    (u₀ (x₀ + J.1.2) + J.1.1 • ckInitialVelocity F u₀ t₀ x₀ + J.2.1,
      fderiv ℝ u₀ (x₀ + J.1.2) + J.2.2))

def ckNormalizeRHS (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) : CKRHS E V :=
  fun J => F (ckNormalizeJet F u₀ t₀ x₀ J) - ckInitialVelocity F u₀ t₀ x₀

def ckNormalizeSolution (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (u : ℝ × E → V) :
    ℝ × E → V :=
  fun z => u (t₀ + z.1, x₀ + z.2) - u₀ (x₀ + z.2) -
    z.1 • ckInitialVelocity F u₀ t₀ x₀

def ckDenormalizeSolution (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (w : ℝ × E → V) :
    ℝ × E → V :=
  fun z => u₀ z.2 + (z.1 - t₀) • ckInitialVelocity F u₀ t₀ x₀ +
    w (z.1 - t₀, z.2 - x₀)

abbrev CKNormalizedSolution (g : CKRHS E V)
    (w : ℝ × E → V) : Prop :=
  CKLocalSolution g (fun _ => 0) 0 0 w

@[simp] theorem ckNormalizeJet_zero (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) :
    ckNormalizeJet F u₀ t₀ x₀ 0 = ckInitialJet t₀ x₀ u₀ := by
  simp [ckNormalizeJet, ckInitialJet]

@[simp] theorem ckNormalizeRHS_zero (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) : ckNormalizeRHS F u₀ t₀ x₀ 0 = 0 := by
  simp [ckNormalizeRHS, ckInitialVelocity]

theorem ckNormalizeJet_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (hu₀ : AnalyticAt ℝ u₀ x₀) :
    AnalyticAt ℝ (ckNormalizeJet F u₀ t₀ x₀) 0 := by
  have ht : AnalyticAt ℝ (fun J : CKJet E V => J.1.1) 0 :=
    analyticAt_fst.comp analyticAt_fst
  have hx : AnalyticAt ℝ (fun J : CKJet E V => J.1.2) 0 :=
    analyticAt_snd.comp analyticAt_fst
  have hy : AnalyticAt ℝ (fun J : CKJet E V => J.2.1) 0 :=
    analyticAt_fst.comp analyticAt_snd
  have hz : AnalyticAt ℝ (fun J : CKJet E V => J.2.2) 0 :=
    analyticAt_snd.comp analyticAt_snd
  have hxs : AnalyticAt ℝ (fun J : CKJet E V => x₀ + J.1.2) 0 :=
    analyticAt_const.add hx
  have hu : AnalyticAt ℝ (fun J : CKJet E V => u₀ (x₀ + J.1.2)) 0 :=
    (by simpa using hu₀).comp hxs
  have hdu : AnalyticAt ℝ
      (fun J : CKJet E V => fderiv ℝ u₀ (x₀ + J.1.2)) 0 :=
    (by simpa using hu₀.fderiv).comp hxs
  exact ((analyticAt_const.add ht).prod hxs).prod
    (((hu.add (ht.smul analyticAt_const)).add hy).prod (hdu.add hz))

theorem ckNormalizeRHS_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (hu₀ : AnalyticAt ℝ u₀ x₀)
    (hF : AnalyticAt ℝ F (ckInitialJet t₀ x₀ u₀)) :
    AnalyticAt ℝ (ckNormalizeRHS F u₀ t₀ x₀) 0 := by
  have hF' : AnalyticAt ℝ F (ckNormalizeJet F u₀ t₀ x₀ 0) := by
    simpa using hF
  exact (hF'.comp (ckNormalizeJet_analyticAt F u₀ t₀ x₀ hu₀)).sub analyticAt_const

@[simp] theorem ckDenormalize_normalize (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (u : ℝ × E → V) :
    ckDenormalizeSolution F u₀ t₀ x₀ (ckNormalizeSolution F u₀ t₀ x₀ u) = u := by
  funext z
  simp only [ckDenormalizeSolution, ckNormalizeSolution, add_sub_cancel,
    sub_add_cancel, add_sub_cancel_left]
  abel

@[simp] theorem ckNormalize_denormalize (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) (w : ℝ × E → V) :
    ckNormalizeSolution F u₀ t₀ x₀ (ckDenormalizeSolution F u₀ t₀ x₀ w) = w := by
  funext z
  simp only [ckNormalizeSolution, ckDenormalizeSolution, add_sub_cancel_left]
  abel

theorem ckNormalizeSolution_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {u : ℝ × E → V}
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hu : AnalyticAt ℝ u (t₀, x₀)) :
    AnalyticAt ℝ (ckNormalizeSolution F u₀ t₀ x₀ u) 0 := by
  have hxs : AnalyticAt ℝ (fun z : ℝ × E => x₀ + z.2) 0 :=
    analyticAt_const.add analyticAt_snd
  have hts : AnalyticAt ℝ (fun z : ℝ × E => t₀ + z.1) 0 :=
    analyticAt_const.add analyticAt_fst
  have hua : AnalyticAt ℝ (fun z : ℝ × E =>
      u (t₀ + z.1, x₀ + z.2)) 0 :=
    (by simpa using hu).comp (hts.prod hxs)
  have hu₀a : AnalyticAt ℝ (fun z : ℝ × E => u₀ (x₀ + z.2)) 0 :=
    (by simpa using hu₀).comp hxs
  exact (hua.sub hu₀a).sub (analyticAt_fst.smul analyticAt_const)

theorem ckDenormalizeSolution_analyticAt (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {w : ℝ × E → V}
    (hu₀ : AnalyticAt ℝ u₀ x₀) (hw : AnalyticAt ℝ w 0) :
    AnalyticAt ℝ (ckDenormalizeSolution F u₀ t₀ x₀ w) (t₀, x₀) := by
  have hts : AnalyticAt ℝ (fun z : ℝ × E => z.1 - t₀) (t₀, x₀) :=
    analyticAt_fst.sub analyticAt_const
  have hxs : AnalyticAt ℝ (fun z : ℝ × E => z.2 - x₀) (t₀, x₀) :=
    analyticAt_snd.sub analyticAt_const
  have hwa : AnalyticAt ℝ (fun z : ℝ × E =>
      w (z.1 - t₀, z.2 - x₀)) (t₀, x₀) :=
    (by simpa using hw).comp (hts.prod hxs)
  exact ((hu₀.comp analyticAt_snd).add (hts.smul analyticAt_const)).add hwa

theorem ckNormalizeSolution_timeDerivative (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {u : ℝ × E → V}
    (z : ℝ × E)
    (hu : DifferentiableAt ℝ (fun t => u (t, x₀ + z.2)) (t₀ + z.1)) :
    deriv (fun t => ckNormalizeSolution F u₀ t₀ x₀ u (t, z.2)) z.1 =
      deriv (fun t => u (t, x₀ + z.2)) (t₀ + z.1) -
        ckInitialVelocity F u₀ t₀ x₀ := by
  have ht := hu.hasDerivAt.comp_const_add t₀ z.1
  have hc := (hasDerivAt_id z.1).smul_const (ckInitialVelocity F u₀ t₀ x₀)
  simpa only [ckNormalizeSolution, one_smul] using
    ((ht.sub_const (u₀ (x₀ + z.2))).sub hc).deriv

theorem ckNormalizeSolution_spaceDerivative (F : CKRHS E V)
    (u₀ : E → V) (t₀ : ℝ)
    (x₀ : E) {u : ℝ × E → V}
    (z : ℝ × E)
    (hu : DifferentiableAt ℝ (fun x => u (t₀ + z.1, x)) (x₀ + z.2))
    (hu₀ : DifferentiableAt ℝ u₀ (x₀ + z.2)) :
    fderiv ℝ (fun x => ckNormalizeSolution F u₀ t₀ x₀ u (z.1, x)) z.2 =
      fderiv ℝ (fun x => u (t₀ + z.1, x)) (x₀ + z.2) -
        fderiv ℝ u₀ (x₀ + z.2) := by
  have hu' := (hasFDerivAt_comp_add_left x₀).mpr hu.hasFDerivAt
  have hu₀' := (hasFDerivAt_comp_add_left x₀).mpr hu₀.hasFDerivAt
  exact ((hu'.sub hu₀').sub_const (z.1 • ckInitialVelocity F u₀ t₀ x₀)).fderiv

end

end NSEGR.NativeLiterature
