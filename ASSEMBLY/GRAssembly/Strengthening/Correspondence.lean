import GRAssembly.Strengthening.RelationCarrier

/-!
Biunique physical correspondence.

The relation is equality after application of the actual coherent-family
boundary decoder. The carrier equivalence is derived from the relation.
-/

set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Strengthening
noncomputable section

def analyticForwardNSEFamily
    {ν : ℝ} {a : Field} (s : AnalyticForwardTrajectory ν a) :
    NSEForwardFamily ν a :=
  profileToNSEFamily (analyticForwardToPositiveProfile s)

noncomputable def analyticForwardGRFamilyEquiv
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field)
    (ha : NSEMaxwell.Classical.Data a) :
    AnalyticForwardTrajectory ν a ≃ GRForwardFamily ν ρ a :=
  (analyticForwardProfileEquiv ν a ha).trans
    (positiveProfileGRFamilyEquiv ν ρ hρ a)

@[simp]
theorem analyticForwardGRFamilyEquiv_apply
    (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field)
    (ha : NSEMaxwell.Classical.Data a)
    (s : AnalyticForwardTrajectory ν a) :
    analyticForwardGRFamilyEquiv ν ρ hρ a ha s =
      coherentFamilyEquiv ν ρ hρ a (analyticForwardNSEFamily s) := rfl

def NSEGRCorresponds
    {ν ρ : ℝ} {a : Field} (hρ : ρ ≠ 0)
    (s : AnalyticForwardTrajectory ν a)
    (γ : GRForwardFamily ν ρ a) : Prop :=
  (coherentFamilyEquiv ν ρ hρ a).symm γ =
    analyticForwardNSEFamily s

theorem nseGRCorresponds_iff_decode
    {ν ρ : ℝ} {a : Field} (hρ : ρ ≠ 0)
    (s : AnalyticForwardTrajectory ν a)
    (γ : GRForwardFamily ν ρ a) :
    NSEGRCorresponds hρ s γ ↔
      decodeGRFamily ν ρ hρ γ.val =
        (analyticForwardNSEFamily s).val := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

theorem nseGRCorresponds_iff_equiv_eq
    {ν ρ : ℝ} {a : Field} (hρ : ρ ≠ 0)
    (ha : NSEMaxwell.Classical.Data a)
    (s : AnalyticForwardTrajectory ν a)
    (γ : GRForwardFamily ν ρ a) :
    NSEGRCorresponds hρ s γ ↔
      analyticForwardGRFamilyEquiv ν ρ hρ a ha s = γ := by
  rw [analyticForwardGRFamilyEquiv_apply]
  constructor
  · intro h
    have h' := congrArg (coherentFamilyEquiv ν ρ hρ a) h
    simpa using h'.symm
  · intro h
    have h' := congrArg (coherentFamilyEquiv ν ρ hρ a).symm h
    simpa using h'.symm

theorem nseGRCorresponds_source_existsUnique
    {ν ρ : ℝ} {a : Field} (hρ : ρ ≠ 0)
    (ha : NSEMaxwell.Classical.Data a)
    (s : AnalyticForwardTrajectory ν a) :
    ∃! γ : GRForwardFamily ν ρ a, NSEGRCorresponds hρ s γ := by
  let E := analyticForwardGRFamilyEquiv ν ρ hρ a ha
  refine ⟨E s, ?_, ?_⟩
  · exact (nseGRCorresponds_iff_equiv_eq hρ ha s (E s)).2 rfl
  · intro γ hγ
    exact ((nseGRCorresponds_iff_equiv_eq hρ ha s γ).1 hγ).symm

theorem nseGRCorresponds_target_existsUnique
    {ν ρ : ℝ} {a : Field} (hρ : ρ ≠ 0)
    (ha : NSEMaxwell.Classical.Data a)
    (γ : GRForwardFamily ν ρ a) :
    ∃! s : AnalyticForwardTrajectory ν a, NSEGRCorresponds hρ s γ := by
  let E := analyticForwardGRFamilyEquiv ν ρ hρ a ha
  refine ⟨E.symm γ, ?_, ?_⟩
  · exact (nseGRCorresponds_iff_equiv_eq hρ ha (E.symm γ) γ).2
      (E.apply_symm_apply γ)
  · intro s hs
    apply E.injective
    have h := (nseGRCorresponds_iff_equiv_eq hρ ha s γ).1 hs
    simpa using h

theorem NSE_GR_POSITIVE_TIME_BIUNIQUE_CORRESPONDENCE
    (ν ρ : ℝ) (_hν : 0 < ν) (hρ : ρ ≠ 0)
    (a : Field) (ha : NSEMaxwell.Classical.Data a) :
    (∀ s : AnalyticForwardTrajectory ν a,
      ∃! γ : GRForwardFamily ν ρ a, NSEGRCorresponds hρ s γ) ∧
    (∀ γ : GRForwardFamily ν ρ a,
      ∃! s : AnalyticForwardTrajectory ν a, NSEGRCorresponds hρ s γ) :=
  ⟨nseGRCorresponds_source_existsUnique hρ ha,
    nseGRCorresponds_target_existsUnique hρ ha⟩

end
end NSEGR.Strengthening
