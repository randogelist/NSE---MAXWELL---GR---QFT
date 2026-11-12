import NSEMaxwell.Kinematics

/-!
# Concrete constitutive algebra

This module uses the actual fields and differential operators of Classical.lean.
The cross-product identities and the zero-input identities are elementary.
Additivity and negation of DG are reduced to explicit identities for K and curl
on the named inputs. No global linearity of the total Fourier formulas is
asserted.

The Ampere factorization requires an explicit time-chain-rule equality and the
two displayed differential identities. These are hypotheses, not analytic
certificates supplied by this module.

Compilation status: A_TIER_CANDIDATE; no local Lean or Lake execution.
-/

set_option autoImplicit false

namespace NSEMaxwell.Constitutive

open NSEMaxwell.Classical

noncomputable section

theorem cross_add_left (a b c : Vec) :
    cross (a + b) c = cross a c + cross b c := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [cross, PiLp.toLp_apply] <;> ring

theorem cross_add_right (a b c : Vec) :
    cross a (b + c) = cross a b + cross a c := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [cross, PiLp.toLp_apply] <;> ring

theorem cross_neg_left (a b : Vec) : cross (-a) b = -cross a b := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [cross, PiLp.toLp_apply] <;> ring

theorem cross_neg_right (a b : Vec) : cross a (-b) = -cross a b := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [cross, PiLp.toLp_apply] <;> ring

/-- DG additivity follows from the specified K and curl equalities. -/
theorem DG_add_of_K_curl
    (ν : ℝ) (m : Vec) (B h k : Field)
    (hK : K (h + k) = K h + K k)
    (hCurl : spatialCurl (h + k) = spatialCurl h + spatialCurl k) :
    DG ν m B (h + k) = DG ν m B h + DG ν m B k := by
  funext x
  simp only [DG, hK, hCurl, Pi.add_apply,
    cross_add_left, cross_add_right, smul_add]
  abel

/-- DG negation follows from the specified K and curl equalities. -/
theorem DG_neg_of_K_curl
    (ν : ℝ) (m : Vec) (B h : Field)
    (hK : K (-h) = -K h)
    (hCurl : spatialCurl (-h) = -spatialCurl h) :
    DG ν m B (-h) = -DG ν m B h := by
  funext x
  simp only [DG, hK, hCurl, Pi.neg_apply,
    cross_neg_left, cross_neg_right, smul_neg]
  abel

theorem V_eq_neg_curl_G (ν : ℝ) (m : Vec) (B : Field) :
    V ν m B = -spatialCurl (G ν m B) := rfl

theorem current_add_differential
    (ν c : ℝ) (m : Vec) (B : Field) (x : Vec) :
    current ν c m B x + DG ν m B (V ν m B) x =
      c ^ 2 • spatialCurl B x := by
  unfold current
  abel

@[simp]
theorem canonical_electric_eq (ν : ℝ) (m : Vec) (B : Velocity) (t : ℝ) :
    canonicalElectric ν m B t = G ν m (B t) := rfl

@[simp]
theorem canonical_charge_eq (ν : ℝ) (m : Vec) (B : Velocity) (t : ℝ) :
    canonicalCharge ν m B t = Q ν m (B t) := rfl

@[simp]
theorem canonical_current_eq (ν c : ℝ) (m : Vec) (B : Velocity) (t : ℝ) :
    canonicalCurrent ν c m B t = current ν c m (B t) := rfl

/-- Electric Gauss is an identity on the canonical constitutive graph. -/
theorem canonical_electric_gauss
    (ν : ℝ) (m : Vec) (B : Velocity) (t : ℝ) (x : Vec) :
    divergence (canonicalElectric ν m B t) x =
      canonicalCharge ν m B t x := rfl

/-- The concrete Faraday residual on the constitutive graph. -/
def faradayResidual (ν : ℝ) (m : Vec) (B : Velocity) (t : ℝ) : Field :=
  fun x => timeDerivative B t x + spatialCurl (G ν m (B t)) x

/-- The concrete Ampere residual on the constitutive graph. -/
def ampereResidual (ν c : ℝ) (m : Vec) (B : Velocity) (t : ℝ) : Field :=
  fun x => timeDerivative (canonicalElectric ν m B) t x -
    c ^ 2 • spatialCurl (B t) x + current ν c m (B t) x

/--
Exact Ampere factorization. The three analytic equalities appear explicitly:
the time chain rule, additivity on the named inputs, and negation on curl G.
-/
theorem ampere_factorization
    (ν c : ℝ) (m : Vec) (B : Velocity) (t : ℝ)
    (hChain : timeDerivative (canonicalElectric ν m B) t =
      DG ν m (B t) (timeDerivative B t))
    (hAdd : DG ν m (B t)
        (timeDerivative B t + spatialCurl (G ν m (B t))) =
      DG ν m (B t) (timeDerivative B t) +
        DG ν m (B t) (spatialCurl (G ν m (B t))))
    (hNeg : DG ν m (B t) (-spatialCurl (G ν m (B t))) =
      -DG ν m (B t) (spatialCurl (G ν m (B t)))) :
    ampereResidual ν c m B t =
      DG ν m (B t) (faradayResidual ν m B t) := by
  funext x
  change
    timeDerivative (canonicalElectric ν m B) t x -
        c ^ 2 • spatialCurl (B t) x +
      (c ^ 2 • spatialCurl (B t) x -
        DG ν m (B t) (-spatialCurl (G ν m (B t))) x) =
      DG ν m (B t)
        (timeDerivative B t + spatialCurl (G ν m (B t))) x
  rw [hChain, hAdd, hNeg]
  simp only [Pi.add_apply, Pi.neg_apply]
  abel

theorem ampere_zero_of_faraday
    (ν c : ℝ) (m : Vec) (B : Velocity) (t : ℝ)
    (hChain : timeDerivative (canonicalElectric ν m B) t =
      DG ν m (B t) (timeDerivative B t))
    (hAdd : DG ν m (B t)
        (timeDerivative B t + spatialCurl (G ν m (B t))) =
      DG ν m (B t) (timeDerivative B t) +
        DG ν m (B t) (spatialCurl (G ν m (B t))))
    (hNeg : DG ν m (B t) (-spatialCurl (G ν m (B t))) =
      -DG ν m (B t) (spatialCurl (G ν m (B t))))
    (hFaraday : faradayResidual ν m B t = 0) :
    ampereResidual ν c m B t = 0 := by
  rw [ampere_factorization ν c m B t hChain hAdd hNeg, hFaraday, DG_zero_direction]

/-- Residual zero is the canonical Ampere equation, pointwise. -/
theorem canonical_ampere_of_residual_zero
    (ν c : ℝ) (m : Vec) (B : Velocity) (t : ℝ)
    (hAmpere : ampereResidual ν c m B t = 0) (x : Vec) :
    timeDerivative (canonicalElectric ν m B) t x -
      c ^ 2 • spatialCurl (B t) x = -canonicalCurrent ν c m B t x := by
  have hx :
      (timeDerivative (canonicalElectric ν m B) t x -
        c ^ 2 • spatialCurl (B t) x) + current ν c m (B t) x = 0 :=
    congrFun hAmpere x
  change
    timeDerivative (canonicalElectric ν m B) t x -
      c ^ 2 • spatialCurl (B t) x = -current ν c m (B t) x
  calc
    timeDerivative (canonicalElectric ν m B) t x -
        c ^ 2 • spatialCurl (B t) x =
      ((timeDerivative (canonicalElectric ν m B) t x -
        c ^ 2 • spatialCurl (B t) x) + current ν c m (B t) x) -
        current ν c m (B t) x := by abel
    _ = 0 - current ν c m (B t) x := by rw [hx]
    _ = -current ν c m (B t) x := by abel

/--
Every exact constrained Maxwell solution has vanishing canonical Faraday
residual. Only its Faraday and electric constitutive fields are used.
-/
theorem canonical_faraday_of_maxwell
    (ν c : ℝ) (m : Vec) (B₀ : Field)
    (B E : Velocity) (ρ : Pressure) (J : Velocity)
    (h : MaxwellSolution ν c m B₀ B E ρ J)
    (t : ℝ) (ht : 0 ≤ t) :
    faradayResidual ν m B t = 0 := by
  funext x
  have hx := h.faraday t ht x
  rw [h.constitutive_electric t ht] at hx
  exact hx

end

end NSEMaxwell.Constitutive

