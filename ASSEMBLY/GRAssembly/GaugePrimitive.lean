import GRAdapter.ScalarCompatibility

/-!
GC21. A normalized analytic double primitive of a time-only pressure gauge.
LI01 is specialized to the literal two-component first-order system
`a_t = b`, `b_t = γ(t)` with one unused spatial coordinate and zero data.
The endpoint concerns the actual ordinary derivatives, as a time germ.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace NSEGR.Assembly
noncomputable section

abbrev GaugeCKState := LiteratureSpace 2
abbrev GaugeCKJet := LiteratureCKJet 1 2

def gaugeCKRHS (γ : ℝ → ℝ) : LiteratureCKRHS 1 2 :=
  fun J => WithLp.toLp 2
    (Fin.cases (J.2.1 1) (fun _ : Fin 1 => γ J.1.1))

theorem gaugeCKRHS_potential (γ : ℝ → ℝ) (J : GaugeCKJet) :
    gaugeCKRHS γ J 0 = J.2.1 1 := rfl

theorem gaugeCKRHS_velocity (γ : ℝ → ℝ) (J : GaugeCKJet) :
    gaugeCKRHS γ J 1 = γ J.1.1 := rfl

theorem analyticAt_gaugeCKRHS {γ : ℝ → ℝ} {J : GaugeCKJet}
    (hγ : AnalyticAt ℝ γ J.1.1) :
    AnalyticAt ℝ (gaugeCKRHS γ) J := by
  have hs : AnalyticAt ℝ (fun Y : GaugeCKJet => Y.2.1) J :=
    analyticAt_fst.comp analyticAt_snd
  have hv : AnalyticAt ℝ (fun Y : GaugeCKJet => Y.2.1 1) J :=
    ((EuclideanSpace.proj (1 : Fin 2)).analyticAt _).comp hs
  have ht : AnalyticAt ℝ (fun Y : GaugeCKJet => γ Y.1.1) J :=
    hγ.comp (analyticAt_fst.comp analyticAt_fst)
  have hall : AnalyticAt ℝ
      (fun Y : GaugeCKJet =>
        (Fin.cases (Y.2.1 1) (fun _ : Fin 1 => γ Y.1.1) : Fin 2 → ℝ)) J := by
    apply AnalyticAt.pi
    intro k
    exact Fin.cases hv (fun _ => ht) k
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.analyticAt _).comp hall

theorem gaugeCK_exists_unique_firstOrder
    (input : LiteratureAnalyticCKInput) {γ : ℝ → ℝ} {t0 : ℝ}
    (hγ : AnalyticAt ℝ γ t0) :
    ∃ W : ℝ × LiteratureSpace 1 → GaugeCKState,
      LiteratureCKSolution (gaugeCKRHS γ)
        (fun _ : LiteratureSpace 1 => (0 : GaugeCKState))
        t0 (0 : LiteratureSpace 1) W ∧
      ∀ V : ℝ × LiteratureSpace 1 → GaugeCKState,
        LiteratureCKSolution (gaugeCKRHS γ)
          (fun _ : LiteratureSpace 1 => (0 : GaugeCKState))
          t0 (0 : LiteratureSpace 1) V →
        W =ᶠ[𝓝 (t0, (0 : LiteratureSpace 1))] V := by
  apply input.exists_unique 1 2 (by norm_num) (by norm_num)
    (gaugeCKRHS γ) (fun _ : LiteratureSpace 1 => (0 : GaugeCKState))
    t0 (0 : LiteratureSpace 1) analyticAt_const
  exact analyticAt_gaugeCKRHS hγ

theorem gaugeCK_coordinate_timeDerivative
    {W : ℝ × LiteratureSpace 1 → GaugeCKState}
    {z : ℝ × LiteratureSpace 1} (hW : AnalyticAt ℝ W z) (k : Fin 2) :
    deriv (fun t : ℝ => W (t, z.2) k) z.1 =
      deriv (fun t : ℝ => W (t, z.2)) z.1 k := by
  let ev : GaugeCKState →L[ℝ] ℝ := EuclideanSpace.proj k
  exact (ev.hasFDerivAt.comp_hasDerivAt z.1
    hW.curry_left.differentiableAt.hasDerivAt).deriv

/-- The actual coordinate time derivatives satisfy the specialized system. -/
theorem gaugeCK_solution_transport
    {γ : ℝ → ℝ} {t0 : ℝ}
    {W : ℝ × LiteratureSpace 1 → GaugeCKState}
    (hW : LiteratureCKSolution (gaugeCKRHS γ)
      (fun _ : LiteratureSpace 1 => (0 : GaugeCKState))
      t0 (0 : LiteratureSpace 1) W) :
    ∀ᶠ t in 𝓝 t0,
      deriv (fun s : ℝ => W (s, 0) 0) t = W (t, 0) 1 ∧
      deriv (fun s : ℝ => W (s, 0) 1) t = γ t := by
  have hs : ∀ᶠ t in 𝓝 t0,
      AnalyticAt ℝ W (t, (0 : LiteratureSpace 1)) ∧
      deriv (fun s : ℝ => W (s, (0 : LiteratureSpace 1))) t =
        gaugeCKRHS γ ((t, 0), (W (t, 0),
          fderiv ℝ (fun x => W (t, x)) 0)) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually
      (hW.analytic.eventually_analyticAt.and hW.equation)
  filter_upwards [hs] with t ht
  constructor
  · rw [gaugeCK_coordinate_timeDerivative ht.1, ht.2]
    exact gaugeCKRHS_potential γ _
  · rw [gaugeCK_coordinate_timeDerivative ht.1, ht.2]
    exact gaugeCKRHS_velocity γ _

/-- LI01 supplies a normalized double primitive with no additional solution premise. -/
theorem analytic_double_primitive_of_literatureCK
    (input : LiteratureAnalyticCKInput) {γ : ℝ → ℝ} {t0 : ℝ}
    (hγ : AnalyticAt ℝ γ t0) :
    ∃ a : ℝ → ℝ, AnalyticAt ℝ a t0 ∧ a t0 = 0 ∧
      deriv a t0 = 0 ∧ deriv (deriv a) =ᶠ[𝓝 t0] γ := by
  obtain ⟨W, hW, _⟩ := gaugeCK_exists_unique_firstOrder input hγ
  let a : ℝ → ℝ := fun t => W (t, 0) 0
  let b : ℝ → ℝ := fun t => W (t, 0) 1
  have ha : AnalyticAt ℝ a t0 :=
    ((EuclideanSpace.proj (0 : Fin 2)).analyticAt _).comp hW.analytic.curry_left
  have h0 : W (t0, (0 : LiteratureSpace 1)) = 0 :=
    Filter.EventuallyEq.eq_of_nhds hW.initial
  have htrans := gaugeCK_solution_transport hW
  have hab : deriv a =ᶠ[𝓝 t0] b := htrans.mono (fun _ h => h.1)
  have hbγ : deriv b =ᶠ[𝓝 t0] γ := htrans.mono (fun _ h => h.2)
  refine ⟨a, ha, ?_, ?_, hab.deriv.trans hbγ⟩
  · exact congrArg (fun q : GaugeCKState => q 0) h0
  · calc
      deriv a t0 = b t0 := hab.eq_of_nhds
      _ = 0 := congrArg (fun q : GaugeCKState => q 1) h0

end
end NSEGR.Assembly
