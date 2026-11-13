import GRAdapter.Sector

/-!
# Full-spatial-slice analytic germ carriers

The flow relation retains pressure gauge and equality on an actual common
time neighborhood. The metric relation retains the fixed marking and
equality on an actual common radial/time neighborhood. Neither carrier is
defined as the image of a construction map.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace NSEGR

noncomputable section

structure NSERepresentative (ν t0 : ℝ) where
  radius : ℝ
  velocity : Velocity
  pressure : Pressure
  solution : LocalNSE ν t0 radius velocity pressure

/-- Equality on a full spatial slice, modulo one spatially constant pressure shift. -/
def SameFlowAt (t0 : ℝ) (u : Velocity) (p : Pressure)
    (v : Velocity) (q : Pressure) : Prop :=
  ∀ᶠ t in 𝓝 t0, u t = v t ∧ ∃ c : ℝ, ∀ x : Vec, p t x = q t x + c

theorem sameFlowAt_refl (t0 : ℝ) (u : Velocity) (p : Pressure) :
    SameFlowAt t0 u p u p := by
  apply Filter.Eventually.of_forall
  intro t
  exact ⟨rfl, 0, by intro x; simp⟩

theorem sameFlowAt_symm {t0 : ℝ} {u v : Velocity} {p q : Pressure}
    (h : SameFlowAt t0 u p v q) : SameFlowAt t0 v q u p := by
  unfold SameFlowAt at h ⊢
  filter_upwards [h] with t ht
  rcases ht with ⟨huv, c, hp⟩
  refine ⟨huv.symm, -c, ?_⟩
  intro x
  rw [hp x]
  ring

theorem sameFlowAt_trans {t0 : ℝ} {u v w : Velocity} {p q r : Pressure}
    (h₁ : SameFlowAt t0 u p v q) (h₂ : SameFlowAt t0 v q w r) :
    SameFlowAt t0 u p w r := by
  unfold SameFlowAt at h₁ h₂ ⊢
  filter_upwards [h₁, h₂] with t ht₁ ht₂
  rcases ht₁ with ⟨huv, c, hp⟩
  rcases ht₂ with ⟨hvw, d, hq⟩
  refine ⟨huv.trans hvw, c + d, ?_⟩
  intro x
  rw [hp x, hq x]
  ring

/-- A pressure-gauge witness is fixed by its value at the spatial origin. -/
theorem sameFlowAt_iff_origin_gauge (t0 : ℝ) (u v : Velocity) (p q : Pressure) :
    SameFlowAt t0 u p v q ↔
      ∀ᶠ t in 𝓝 t0, u t = v t ∧
        ∀ x : Vec, p t x = q t x + (p t 0 - q t 0) := by
  constructor
  · intro h
    unfold SameFlowAt at h
    filter_upwards [h] with t ht
    rcases ht with ⟨huv, c, hp⟩
    refine ⟨huv, ?_⟩
    intro x
    rw [hp x, hp 0]
    ring
  · intro h
    unfold SameFlowAt
    filter_upwards [h] with t ht
    exact ⟨ht.1, p t 0 - q t 0, ht.2⟩

def NSERepresentative.setoid (ν t0 : ℝ) : Setoid (NSERepresentative ν t0) where
  r a b := SameFlowAt t0 a.velocity a.pressure b.velocity b.pressure
  iseqv := {
    refl := fun a => sameFlowAt_refl t0 a.velocity a.pressure
    symm := by
      intro a b h
      exact sameFlowAt_symm h
    trans := by
      intro a b c hab hbc
      exact sameFlowAt_trans hab hbc }

abbrev NSEgerm (ν t0 : ℝ) := Quotient (NSERepresentative.setoid ν t0)

def NSEgerm.mk {ν t0 : ℝ} (a : NSERepresentative ν t0) : NSEgerm ν t0 :=
  Quotient.mk (NSERepresentative.setoid ν t0) a

theorem NSEgerm.sound {ν t0 : ℝ} {a b : NSERepresentative ν t0}
    (h : SameFlowAt t0 a.velocity a.pressure b.velocity b.pressure) :
    NSEgerm.mk a = NSEgerm.mk b :=
  Quotient.sound h

/-- Equality is uniform over the full spatial slice in the fixed marking. -/
def SameMetricAt (t0 : ℝ) (g h : Metric) : Prop :=
  ∀ᶠ rt : ℝ × ℝ in 𝓝 ((0 : ℝ), t0), ∀ x : Vec,
    g (bulkPoint rt.1 rt.2 x) = h (bulkPoint rt.1 rt.2 x)

theorem sameMetricAt_refl (t0 : ℝ) (g : Metric) : SameMetricAt t0 g g := by
  apply Filter.Eventually.of_forall
  intro rt x
  rfl

theorem sameMetricAt_symm {t0 : ℝ} {g h : Metric}
    (hgh : SameMetricAt t0 g h) : SameMetricAt t0 h g := by
  unfold SameMetricAt at hgh ⊢
  filter_upwards [hgh] with rt hrt
  intro x
  exact (hrt x).symm

theorem sameMetricAt_trans {t0 : ℝ} {g h k : Metric}
    (hgh : SameMetricAt t0 g h) (hhk : SameMetricAt t0 h k) :
    SameMetricAt t0 g k := by
  unfold SameMetricAt at hgh hhk ⊢
  filter_upwards [hgh, hhk] with rt hrt₁ hrt₂
  intro x
  exact (hrt₁ x).trans (hrt₂ x)

def CanonicalRepresentative.setoid (ν ρ t0 : ℝ) :
    Setoid (CanonicalRepresentative ν ρ t0) where
  r a b := SameMetricAt t0 a.metric b.metric
  iseqv := {
    refl := fun a => sameMetricAt_refl t0 a.metric
    symm := by
      intro a b h
      exact sameMetricAt_symm h
    trans := by
      intro a b c hab hbc
      exact sameMetricAt_trans hab hbc }

abbrev GRgerm (ν ρ t0 : ℝ) :=
  Quotient (CanonicalRepresentative.setoid ν ρ t0)

def GRgerm.mk {ν ρ t0 : ℝ} (a : CanonicalRepresentative ν ρ t0) :
    GRgerm ν ρ t0 :=
  Quotient.mk (CanonicalRepresentative.setoid ν ρ t0) a

theorem GRgerm.sound {ν ρ t0 : ℝ} {a b : CanonicalRepresentative ν ρ t0}
    (h : SameMetricAt t0 a.metric b.metric) : GRgerm.mk a = GRgerm.mk b :=
  Quotient.sound h

def constantNSERepresentative (ν t0 : ℝ) (m : Vec) (c : ℝ) :
    NSERepresentative ν t0 where
  radius := 1
  velocity := fun _ _ => m
  pressure := fun _ _ => c
  solution := localNSE_const ν t0 1 (by norm_num) m c

/-- The local analytic flow germ carrier is inhabited by actual constant solutions. -/
theorem nonempty_NSEgerm (ν t0 : ℝ) : Nonempty (NSEgerm ν t0) :=
  ⟨NSEgerm.mk (constantNSERepresentative ν t0 0 0)⟩

end

end NSEGR
