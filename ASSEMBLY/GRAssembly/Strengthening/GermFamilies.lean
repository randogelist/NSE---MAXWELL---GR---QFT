import GRAssembly.Strengthening.GermEvaluation
import SingularClosure.SmoothDatumSobolev

/-!
Coherent native NSE and actual geometric germ families, with their exact
all-spatial-Sobolev initial trace. The equivalence uses the native physical
maps; its target is not defined as an encoding image.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped Topology

namespace NSEGR.Strengthening

noncomputable section

abbrev PositiveTime := {t : ℝ // 0 < t}

abbrev PositiveTimeNSEGermFamily (ν : ℝ) :=
  (t : PositiveTime) → NSEgerm ν t.val

abbrev PositiveTimeGRGermFamily (ν ρ : ℝ) :=
  (t : PositiveTime) → GRgerm ν ρ t.val

def nseFamilyVelocity {ν : ℝ} (η : PositiveTimeNSEGermFamily ν) :
    PositiveTime → Field :=
  fun t => NSEgerm.velocityAtCenter (η t)

def grFamilyVelocity {ν ρ : ℝ} (γ : PositiveTimeGRGermFamily ν ρ) :
    PositiveTime → Field :=
  fun t => GRgerm.velocityAtCenter (γ t)

/-- Exact all-order Fourier Sobolev trace. The Sobolev curves are property
witnesses; every positive-time coefficient is the actual physical integral
coefficient. The zero Fourier mode is retained. -/
def SpatialSmoothInitialTrace (V : PositiveTime → Field) (a : Field) : Prop :=
  ∀ m : ℕ, ∃ U : ℝ → SingularClosure.TorusSobolev m,
    (∀ t : PositiveTime, (U t.val).val = SingularClosure.datumFourierCoeff (V t)) ∧
    (U 0).val = SingularClosure.datumFourierCoeff a ∧
    Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 (U 0))

theorem spatialSmoothInitialTrace_congr {V W : PositiveTime → Field} {a : Field}
    (hVW : V = W) : SpatialSmoothInitialTrace V a ↔ SpatialSmoothInitialTrace W a := by
  rw [hVW]

def NSEVelocityCoherent {ν : ℝ} (η : PositiveTimeNSEGermFamily ν) : Prop :=
  ∀ τ : PositiveTime, ∃ n : NSERepresentative ν τ.val,
    NSEgerm.mk n = η τ ∧
    ∃ d : ℝ, 0 < d ∧ d < τ.val ∧ d ≤ n.radius ∧
      ∀ t : PositiveTime, t.val ∈ timeInterval τ.val d →
        n.velocity t.val = nseFamilyVelocity η t

def DecodedVelocityCoherent {ν ρ : ℝ} (γ : PositiveTimeGRGermFamily ν ρ) : Prop :=
  ∀ τ : PositiveTime, ∃ g : CanonicalRepresentative ν ρ τ.val,
    GRgerm.mk g = γ τ ∧
    ∃ d : ℝ, 0 < d ∧ d < τ.val ∧ d ≤ g.timeRadius ∧
      ∀ t : PositiveTime, t.val ∈ timeInterval τ.val d →
        boundaryVelocity (boundaryK g.metric) t.val = grFamilyVelocity γ t

def NSEForwardFamily (ν : ℝ) (a : Field) :=
  {η : PositiveTimeNSEGermFamily ν //
    NSEVelocityCoherent η ∧ SpatialSmoothInitialTrace (nseFamilyVelocity η) a}

def GRForwardFamily (ν ρ : ℝ) (a : Field) :=
  {γ : PositiveTimeGRGermFamily ν ρ //
    DecodedVelocityCoherent γ ∧ SpatialSmoothInitialTrace (grFamilyVelocity γ) a}

theorem nseForwardFamily_ext {ν : ℝ} {a : Field}
    {η θ : NSEForwardFamily ν a} (h : ∀ t : PositiveTime, η.val t = θ.val t) :
    η = θ := by
  apply Subtype.ext
  exact funext h

theorem grForwardFamily_ext {ν ρ : ℝ} {a : Field}
    {γ ζ : GRForwardFamily ν ρ a} (h : ∀ t : PositiveTime, γ.val t = ζ.val t) :
    γ = ζ := by
  apply Subtype.ext
  exact funext h

theorem coherence_interval_transfer (τ : PositiveTime)
    (u v : Velocity) (V : PositiveTime → Field) {d r : ℝ}
    (hd : 0 < d) (hdτ : d < τ.val) (hr : 0 < r)
    (huv : u =ᶠ[𝓝 τ.val] v)
    (hu : ∀ t : PositiveTime, t.val ∈ timeInterval τ.val d → u t.val = V t) :
    ∃ e : ℝ, 0 < e ∧ e < τ.val ∧ e ≤ r ∧
      ∀ t : PositiveTime, t.val ∈ timeInterval τ.val e → v t.val = V t := by
  obtain ⟨e, he, heCap, hsub⟩ := Assembly.positive_timeInterval_subset
    (W := {t : ℝ | u t = v t}) (lt_min hd hr) huv
  have hed : e ≤ d := heCap.trans (min_le_left _ _)
  have her : e ≤ r := heCap.trans (min_le_right _ _)
  refine ⟨e, he, hed.trans_lt hdτ, her, ?_⟩
  intro t ht
  exact (hsub ht).symm.trans (hu t (timeInterval_mono hed ht))

theorem nse_coherence_any_representative {ν : ℝ}
    (η : PositiveTimeNSEGermFamily ν) (hη : NSEVelocityCoherent η)
    (τ : PositiveTime) (n : NSERepresentative ν τ.val) (hn : NSEgerm.mk n = η τ) :
    ∃ d : ℝ, 0 < d ∧ d < τ.val ∧ d ≤ n.radius ∧
      ∀ t : PositiveTime, t.val ∈ timeInterval τ.val d →
        n.velocity t.val = nseFamilyVelocity η t := by
  obtain ⟨n₀, hn₀, d, hd, hdτ, _, hv⟩ := hη τ
  have heq : NSEgerm.mk n₀ = NSEgerm.mk n := hn₀.trans hn.symm
  have hflow : SameFlowAt τ.val n₀.velocity n₀.pressure n.velocity n.pressure :=
    Quotient.exact heq
  exact coherence_interval_transfer τ n₀.velocity n.velocity (nseFamilyVelocity η)
    hd hdτ n.solution.radius_pos (hflow.mono (fun _ ht => ht.1)) hv

theorem gr_coherence_any_representative {ν ρ : ℝ}
    (γ : PositiveTimeGRGermFamily ν ρ) (hγ : DecodedVelocityCoherent γ)
    (τ : PositiveTime) (g : CanonicalRepresentative ν ρ τ.val)
    (hg : GRgerm.mk g = γ τ) :
    ∃ d : ℝ, 0 < d ∧ d < τ.val ∧ d ≤ g.timeRadius ∧
      ∀ t : PositiveTime, t.val ∈ timeInterval τ.val d →
        boundaryVelocity (boundaryK g.metric) t.val = grFamilyVelocity γ t := by
  obtain ⟨g₀, hg₀, d, hd, hdτ, _, hv⟩ := hγ τ
  have heq : GRgerm.mk g₀ = GRgerm.mk g := hg₀.trans hg.symm
  have hmetric : SameMetricAt τ.val g₀.metric g.metric := Quotient.exact heq
  have hflow := sameMetricAt_boundaryFields ρ hmetric
  exact coherence_interval_transfer τ (boundaryVelocity (boundaryK g₀.metric))
    (boundaryVelocity (boundaryK g.metric)) (grFamilyVelocity γ)
    hd hdτ g.geometry.time_radius_pos (hflow.mono (fun _ ht => ht.1)) hv

def encodeNSEFamily (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (η : PositiveTimeNSEGermFamily ν) : PositiveTimeGRGermFamily ν ρ :=
  fun τ => nativeLocalEquiv ν ρ τ.val hρ (η τ)

def decodeGRFamily (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : PositiveTimeGRGermFamily ν ρ) : PositiveTimeNSEGermFamily ν :=
  fun τ => (nativeLocalEquiv ν ρ τ.val hρ).symm (γ τ)

theorem encodeNSEFamily_velocity (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (η : PositiveTimeNSEGermFamily ν) :
    grFamilyVelocity (encodeNSEFamily ν ρ hρ η) = nseFamilyVelocity η := by
  funext τ
  exact nativeLocalEquiv_velocityAtCenter ν ρ τ.val hρ (η τ)

theorem decodeGRFamily_velocity (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : PositiveTimeGRGermFamily ν ρ) :
    nseFamilyVelocity (decodeGRFamily ν ρ hρ γ) = grFamilyVelocity γ := by
  funext τ
  exact nativeLocalEquiv_symm_velocityAtCenter ν ρ τ.val hρ (γ τ)

theorem decodeGRFamily_encodeNSEFamily (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (η : PositiveTimeNSEGermFamily ν) :
    decodeGRFamily ν ρ hρ (encodeNSEFamily ν ρ hρ η) = η := by
  funext τ
  exact nativeLocalEquiv_left_inverse ν ρ τ.val hρ (η τ)

theorem encodeNSEFamily_decodeGRFamily (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : PositiveTimeGRGermFamily ν ρ) :
    encodeNSEFamily ν ρ hρ (decodeGRFamily ν ρ hρ γ) = γ := by
  funext τ
  exact nativeLocalEquiv_right_inverse ν ρ τ.val hρ (γ τ)

theorem encodeNSEFamily_coherent (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (η : PositiveTimeNSEGermFamily ν) (hη : NSEVelocityCoherent η) :
    DecodedVelocityCoherent (encodeNSEFamily ν ρ hρ η) := by
  intro τ
  obtain ⟨n, hn, d, hd, hdτ, hdn, hcoh⟩ := hη τ
  let p := nativeLocalPackage ν ρ τ.val hρ
  let g := forwardRepresentative p.completion p.radial n
  obtain ⟨e, he, heτ, hen, heg, hrec⟩ :=
    forward_recovery_positive_interval τ.property p.completion p.radial n
  refine ⟨g, ?_, min d e, lt_min hd he,
    (min_le_left d e).trans_lt hdτ, (min_le_right d e).trans heg, ?_⟩
  · change GRgerm.mk g = nativeLocalEquiv ν ρ τ.val hρ (η τ)
    rw [← hn]
    rfl
  · intro t ht
    have htd : t.val ∈ timeInterval τ.val d :=
      timeInterval_mono (min_le_left d e) ht
    have hte : t.val ∈ timeInterval τ.val e :=
      timeInterval_mono (min_le_right d e) ht
    calc
      boundaryVelocity (boundaryK g.metric) t.val = n.velocity t.val := (hrec t.val hte).1
      _ = nseFamilyVelocity η t := hcoh t htd
      _ = grFamilyVelocity (encodeNSEFamily ν ρ hρ η) t :=
        (congrFun (encodeNSEFamily_velocity ν ρ hρ η) t).symm

theorem decodeGRFamily_coherent (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : PositiveTimeGRGermFamily ν ρ) (hγ : DecodedVelocityCoherent γ) :
    NSEVelocityCoherent (decodeGRFamily ν ρ hρ γ) := by
  intro τ
  obtain ⟨g, hg, d, hd, hdτ, hdg, hcoh⟩ := hγ τ
  let n := reverseRepresentative (nativeLocalPackage ν ρ τ.val hρ).reconstruction g
  refine ⟨n, ?_, d, hd, hdτ, hdg, ?_⟩
  · change NSEgerm.mk n = (nativeLocalEquiv ν ρ τ.val hρ).symm (γ τ)
    rw [← hg]
    rfl
  · intro t ht
    change boundaryVelocity (boundaryK g.metric) t.val =
      nseFamilyVelocity (decodeGRFamily ν ρ hρ γ) t
    exact (hcoh t ht).trans (congrFun (decodeGRFamily_velocity ν ρ hρ γ) t).symm

theorem encodeNSEFamily_trace (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (η : PositiveTimeNSEGermFamily ν) (a : Field)
    (h : SpatialSmoothInitialTrace (nseFamilyVelocity η) a) :
    SpatialSmoothInitialTrace (grFamilyVelocity (encodeNSEFamily ν ρ hρ η)) a := by
  rw [encodeNSEFamily_velocity]
  exact h

theorem decodeGRFamily_trace (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (γ : PositiveTimeGRGermFamily ν ρ) (a : Field)
    (h : SpatialSmoothInitialTrace (grFamilyVelocity γ) a) :
    SpatialSmoothInitialTrace (nseFamilyVelocity (decodeGRFamily ν ρ hρ γ)) a := by
  rw [decodeGRFamily_velocity]
  exact h

/-- The exact native NSE/GR coherent germ-family equivalence. All geometry
contracts are discharged by the native local construction. -/
def coherentFamilyEquiv (ν ρ : ℝ) (hρ : ρ ≠ 0) (a : Field) :
    NSEForwardFamily ν a ≃ GRForwardFamily ν ρ a where
  toFun η := ⟨encodeNSEFamily ν ρ hρ η.val,
    ⟨encodeNSEFamily_coherent ν ρ hρ η.val η.property.1,
     encodeNSEFamily_trace ν ρ hρ η.val a η.property.2⟩⟩
  invFun γ := ⟨decodeGRFamily ν ρ hρ γ.val,
    ⟨decodeGRFamily_coherent ν ρ hρ γ.val γ.property.1,
     decodeGRFamily_trace ν ρ hρ γ.val a γ.property.2⟩⟩
  left_inv η := by
    apply Subtype.ext
    exact decodeGRFamily_encodeNSEFamily ν ρ hρ η.val
  right_inv γ := by
    apply Subtype.ext
    exact encodeNSEFamily_decodeGRFamily ν ρ hρ γ.val

theorem NSE_GR_COHERENT_FAMILY_EQUIVALENCE (ν ρ : ℝ)
    (_hν : 0 < ν) (hρ : ρ ≠ 0) (a : Field) :
    Nonempty (NSEForwardFamily ν a ≃ GRForwardFamily ν ρ a) :=
  ⟨coherentFamilyEquiv ν ρ hρ a⟩

theorem coherentFamilyEquiv_velocity (ν ρ : ℝ) (hρ : ρ ≠ 0)
    (a : Field) (η : NSEForwardFamily ν a) :
    grFamilyVelocity (coherentFamilyEquiv ν ρ hρ a η).val =
      nseFamilyVelocity η.val :=
  encodeNSEFamily_velocity ν ρ hρ η.val

end
end NSEGR.Strengthening
