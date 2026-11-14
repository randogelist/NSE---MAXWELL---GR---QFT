import GRAssembly.NSE_GR_NATIVE_LITERATURE_CLOSURE
import GRAssembly.RootClosure
import GRAssembly.NativeGluingAtlas

/-!
Exact center evaluations and the actual physical local equivalence.
The native law packages are constructed; no additional law hypothesis remains.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace NSEGR

noncomputable section

theorem sameFlowAt_center_velocity {ν t0 : ℝ}
    {a b : NSERepresentative ν t0}
    (h : SameFlowAt t0 a.velocity a.pressure b.velocity b.pressure) :
    a.velocity t0 = b.velocity t0 := by
  have hv : a.velocity =ᶠ[𝓝 t0] b.velocity := h.mono (fun _ ht => ht.1)
  exact hv.eq_of_nhds

def NSEgerm.velocityAtCenter {ν t0 : ℝ} : NSEgerm ν t0 → Field :=
  Quotient.lift (fun a : NSERepresentative ν t0 => a.velocity t0)
    (fun _ _ h => sameFlowAt_center_velocity h)

@[simp]
theorem NSEgerm.velocityAtCenter_mk {ν t0 : ℝ}
    (a : NSERepresentative ν t0) :
    NSEgerm.velocityAtCenter (NSEgerm.mk a) = a.velocity t0 := rfl

theorem sameMetricAt_center_velocity {ν ρ t0 : ℝ}
    {a b : CanonicalRepresentative ν ρ t0}
    (h : SameMetricAt t0 a.metric b.metric) :
    boundaryVelocity (boundaryK a.metric) t0 =
      boundaryVelocity (boundaryK b.metric) t0 := by
  have hflow := sameMetricAt_boundaryFields ρ h
  have hv : boundaryVelocity (boundaryK a.metric) =ᶠ[𝓝 t0]
      boundaryVelocity (boundaryK b.metric) := hflow.mono (fun _ ht => ht.1)
  exact hv.eq_of_nhds

def GRgerm.velocityAtCenter {ν ρ t0 : ℝ} : GRgerm ν ρ t0 → Field :=
  Quotient.lift
    (fun a : CanonicalRepresentative ν ρ t0 => boundaryVelocity (boundaryK a.metric) t0)
    (fun _ _ h => sameMetricAt_center_velocity h)

@[simp]
theorem GRgerm.velocityAtCenter_mk {ν ρ t0 : ℝ}
    (a : CanonicalRepresentative ν ρ t0) :
    GRgerm.velocityAtCenter (GRgerm.mk a) =
      boundaryVelocity (boundaryK a.metric) t0 := rfl

namespace Strengthening

structure NativeLocalPackage (ν ρ t0 : ℝ) where
  completion : ScalarBoundaryCompletionLaws ν ρ t0
  radial : AnalyticRadialExtensionLaws ρ t0
  reconstruction : GeometricReconstructionLaws ν ρ t0
  inverse : GermInverseLaws completion radial reconstruction

theorem nativeLocalPackage_nonempty (ν ρ t0 : ℝ) (hρ : ρ ≠ 0) :
    Nonempty (NativeLocalPackage ν ρ t0) := by
  obtain ⟨c, r, h, q⟩ := Assembly.nativeLawPackages_of_literatureInputs
    NativeLiterature.literatureInputs_native ν ρ t0 hρ
  exact ⟨⟨c, r, h, q⟩⟩

def nativeLocalPackage (ν ρ t0 : ℝ) (hρ : ρ ≠ 0) :
    NativeLocalPackage ν ρ t0 :=
  Classical.choice (nativeLocalPackage_nonempty ν ρ t0 hρ)

def nativeLocalEquiv (ν ρ t0 : ℝ) (hρ : ρ ≠ 0) :
    NSEgerm ν t0 ≃ GRgerm ν ρ t0 :=
  let p := nativeLocalPackage ν ρ t0 hρ
  exactSectorEquivOfContracts p.completion p.radial p.reconstruction p.inverse

@[simp]
theorem nativeLocalEquiv_mk (ν ρ t0 : ℝ) (hρ : ρ ≠ 0)
    (n : NSERepresentative ν t0) :
    nativeLocalEquiv ν ρ t0 hρ (NSEgerm.mk n) =
      GRgerm.mk (forwardRepresentative
        (nativeLocalPackage ν ρ t0 hρ).completion
        (nativeLocalPackage ν ρ t0 hρ).radial n) := rfl

@[simp]
theorem nativeLocalEquiv_symm_mk (ν ρ t0 : ℝ) (hρ : ρ ≠ 0)
    (g : CanonicalRepresentative ν ρ t0) :
    (nativeLocalEquiv ν ρ t0 hρ).symm (GRgerm.mk g) =
      NSEgerm.mk (reverseRepresentative
        (nativeLocalPackage ν ρ t0 hρ).reconstruction g) := rfl

theorem nativeLocalEquiv_velocityAtCenter (ν ρ t0 : ℝ) (hρ : ρ ≠ 0)
    (n : NSEgerm ν t0) :
    GRgerm.velocityAtCenter (nativeLocalEquiv ν ρ t0 hρ n) =
      NSEgerm.velocityAtCenter n := by
  refine Quotient.inductionOn n ?_
  intro a
  rw [nativeLocalEquiv_mk, GRgerm.velocityAtCenter_mk, NSEgerm.velocityAtCenter_mk]
  exact (forward_velocity_recovery
    (nativeLocalPackage ν ρ t0 hρ).completion
    (nativeLocalPackage ν ρ t0 hρ).radial a).eq_of_nhds

theorem nativeLocalEquiv_symm_velocityAtCenter (ν ρ t0 : ℝ) (hρ : ρ ≠ 0)
    (g : GRgerm ν ρ t0) :
    NSEgerm.velocityAtCenter ((nativeLocalEquiv ν ρ t0 hρ).symm g) =
      GRgerm.velocityAtCenter g := by
  refine Quotient.inductionOn g ?_
  intro a
  rfl

theorem nativeLocalEquiv_left_inverse (ν ρ t0 : ℝ) (hρ : ρ ≠ 0)
    (n : NSEgerm ν t0) :
    (nativeLocalEquiv ν ρ t0 hρ).symm (nativeLocalEquiv ν ρ t0 hρ n) = n :=
  (nativeLocalEquiv ν ρ t0 hρ).symm_apply_apply n

theorem nativeLocalEquiv_right_inverse (ν ρ t0 : ℝ) (hρ : ρ ≠ 0)
    (g : GRgerm ν ρ t0) :
    nativeLocalEquiv ν ρ t0 hρ ((nativeLocalEquiv ν ρ t0 hρ).symm g) = g :=
  (nativeLocalEquiv ν ρ t0 hρ).apply_symm_apply g

theorem forward_recovery_positive_interval {ν ρ t0 : ℝ}
    (ht0 : 0 < t0)
    (c : ScalarBoundaryCompletionLaws ν ρ t0)
    (r : AnalyticRadialExtensionLaws ρ t0)
    (n : NSERepresentative ν t0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ t0 / 2 ∧ d ≤ n.radius ∧
      d ≤ (forwardRepresentative c r n).timeRadius ∧
      ∀ t ∈ timeInterval t0 d,
        boundaryVelocity (boundaryK (forwardRepresentative c r n).metric) t = n.velocity t ∧
        ∀ x : Vec,
          boundaryPressure ρ (boundaryK (forwardRepresentative c r n).metric) t x -
            boundaryPressure ρ (boundaryK (forwardRepresentative c r n).metric) t 0 =
          n.pressure t x - n.pressure t 0 := by
  let g := forwardRepresentative c r n
  let W : Set ℝ := {t |
    boundaryVelocity (boundaryK g.metric) t = n.velocity t ∧
    ∀ x : Vec, boundaryPressure ρ (boundaryK g.metric) t x -
      boundaryPressure ρ (boundaryK g.metric) t 0 = n.pressure t x - n.pressure t 0}
  have hW : W ∈ 𝓝 t0 := by
    have hrec := (sameFlowAt_iff_origin_gauge t0
      (boundaryVelocity (boundaryK g.metric)) n.velocity
      (boundaryPressure ρ (boundaryK g.metric)) n.pressure).mp
        (forward_pressure_gauge_recovery c r n)
    filter_upwards [hrec] with t ht
    refine ⟨ht.1, ?_⟩
    intro x
    linarith [ht.2 x]
  have hcap : 0 < min (t0 / 2) (min n.radius g.timeRadius) :=
    lt_min (half_pos ht0) (lt_min n.solution.radius_pos g.geometry.time_radius_pos)
  obtain ⟨d, hd, hdCap, hsub⟩ := Assembly.positive_timeInterval_subset hcap hW
  refine ⟨d, hd, hdCap.trans (min_le_left _ _),
    hdCap.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hdCap.trans ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  exact fun t ht => hsub ht

end Strengthening

end
end NSEGR
