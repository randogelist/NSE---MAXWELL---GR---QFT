import QuantumAdapter.Obligations.EnergyDerivatives
import QuantumAdapter.Obligations.EnergyPhysical

/-! Tangency and spatial Leibniz law of the actual bilinear phase convection. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace QuantumAdapter.Obligations
noncomputable section
open SingularClosure

theorem fullBilinearTransport_reality (N : ℕ) (a b : FourierCoeff)
    (ha : SpectralReality a) (hb : SpectralReality b) :
    SpectralReality (fullBilinearTransport N a b) := by
  classical
  intro k i
  let term : Frequency → Frequency → ℂ := fun q p =>
    (∑ j : Fin 3, a p j * derivativeSymbol j (q - p)) * b (q - p) i
  have hterm (p : Frequency) : term (-k) (-p) = star (term k p) := by
    have hsub : -k - -p = -(k - p) := by abel
    have har (j : Fin 3) : a (-p) j = star (a p j) := ha p j
    have hbr : b (-(k - p)) i = star (b (k - p) i) := hb (k - p) i
    dsimp [term]
    simp only [hsub, har, hbr, derivativeSymbol_reality, Complex.star_def, map_mul, map_sum]
  change (∑ p ∈ fullModes N, term (-k) p) = star (∑ p ∈ fullModes N, term k p)
  rw [star_sum]
  apply Finset.sum_nbij' (fun p => -p) (fun p => -p)
    (fun p hp => fullModes_neg_mem hp) (fun p hp => fullModes_neg_mem hp)
  · intro p hp; simp
  · intro p hp; simp
  · intro p hp
    simpa only [neg_neg] using hterm (-p)

theorem fullBilinearTransport_zero_frequency (N : ℕ) (a b : FourierCoeff)
    (ha : SpectralSolenoidal a) (i : Fin 3) :
    fullBilinearTransport N a b 0 i = 0 := by
  unfold fullBilinearTransport
  apply Finset.sum_eq_zero
  intro p hp
  have hz : (∑ j : Fin 3, a p j * derivativeSymbol j ((0 : Frequency) - p)) = 0 := by
    calc
      _ = -(2 * (Real.pi : ℂ) * Complex.I) *
          ∑ j : Fin 3, (p j : ℂ) * a p j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [derivativeSymbol, Pi.sub_apply, Pi.zero_apply, zero_sub]
        push_cast
        ring
      _ = 0 := by rw [ha p, mul_zero]
  rw [hz, zero_mul]

theorem bilinearAmbient_coeff (N : ℕ) (q r : Phase N) (k : Frequency) (i : Fin 3) :
    extendCoeff (bilinearAmbient N q r) k i =
      if k ∈ fullModes N then if k = 0 then 0 else
        -coefficientLeray k (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k) i
      else 0 := by
  by_cases hk : k ∈ fullModes N <;> simp [extendCoeff, bilinearAmbient, hk]

theorem bilinearAmbient_reality (N : ℕ) (q r : Phase N) :
    SpectralReality (extendCoeff (bilinearAmbient N q r)) := by
  intro k i
  rw [bilinearAmbient_coeff, bilinearAmbient_coeff]
  by_cases hm : k ∈ fullModes N
  · rw [if_pos hm, if_pos (fullModes_neg_mem hm)]
    by_cases hk : k = 0
    · simp [hk]
    · rw [if_neg hk, if_neg (neg_ne_zero.mpr hk)]
      have ht : fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) (-k) =
          fun j => star (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k j) := by
        funext j
        exact fullBilinearTransport_reality N _ _ (phaseCoeff_reality q)
          (phaseCoeff_reality r) k j
      rw [ht, coefficientLeray_neg_star]
      simp only [star_neg]
  · rw [if_neg hm, if_neg ((fullModes_neg_mem_iff N k).not.mpr hm)]
    simp

theorem bilinearAmbient_solenoidal (N : ℕ) (q r : Phase N) :
    SpectralSolenoidal (extendCoeff (bilinearAmbient N q r)) := by
  intro k
  simp_rw [bilinearAmbient_coeff]
  by_cases hm : k ∈ fullModes N
  · simp only [if_pos hm]
    by_cases hk : k = 0
    · subst k; simp
    · simp only [if_neg hk, mul_neg, Finset.sum_neg_distrib]
      rw [coefficientLeray_solenoidal, neg_zero]
  · simp [hm]

theorem bilinearAmbient_tangent (N : ℕ) (q r : Phase N) :
    bilinearAmbient N q r ∈ phaseSubmodule N :=
  ⟨bilinearAmbient_reality N q r, bilinearAmbient_solenoidal N q r⟩

theorem bilinearConvection_val (N : ℕ) (q r : Phase N) :
    (bilinearConvection N q r).val = bilinearAmbient N q r := by
  have h := (phaseSubmodule N).orthogonalProjectionOnto_mem_subspace_eq_self
    (⟨bilinearAmbient N q r, bilinearAmbient_tangent N q r⟩ : Phase N)
  exact congrArg Subtype.val h

theorem phaseCoeff_bilinearConvection (N : ℕ) (q r : Phase N)
    (k : Frequency) (i : Fin 3) :
    phaseCoeff (bilinearConvection N q r) k i =
      if k ∈ fullModes N then
        -coefficientLeray k (fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k) i
      else 0 := by
  change extendCoeff (bilinearConvection N q r).val k i = _
  rw [bilinearConvection_val, bilinearAmbient_coeff]
  by_cases hk : k ∈ fullModes N
  · rw [if_pos hk, if_pos hk]
    by_cases hk0 : k = 0
    · subst k
      simp [coefficientLeray, fullBilinearTransport_zero_frequency N _ _
        (phaseCoeff_solenoidal q)]
    · rw [if_neg hk0]
  · rw [if_neg hk, if_neg hk]

theorem derivativeSymbol_add_native (j : Fin 3) (p q : Frequency) :
    derivativeSymbol j (p + q) = derivativeSymbol j p + derivativeSymbol j q := by
  simp only [derivativeSymbol, Pi.add_apply]
  push_cast
  ring

theorem fullBilinearTransport_spatial_leibniz (N : ℕ) (j : Fin 3)
    (a b : FourierCoeff) (k : Frequency) (i : Fin 3) :
    derivativeSymbol j k * fullBilinearTransport N a b k i =
      fullBilinearTransport N (spectralMultiplier (derivativeSymbol j) a) b k i +
      fullBilinearTransport N a (spectralMultiplier (derivativeSymbol j) b) k i := by
  unfold fullBilinearTransport
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hsym : derivativeSymbol j k =
      derivativeSymbol j p + derivativeSymbol j (k - p) := by
    rw [← derivativeSymbol_add_native]
    congr 1
    abel
  simp only [spectralMultiplier]
  have hs : (∑ l : Fin 3, (derivativeSymbol j p * a p l) * derivativeSymbol l (k - p)) =
      derivativeSymbol j p * ∑ l : Fin 3, a p l * derivativeSymbol l (k - p) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hs, hsym]
  ring

theorem coefficientLeray_complex_mul_native (k : Frequency) (s : ℂ) (a : Fin 3 → ℂ) :
    coefficientLeray k (fun i => s * a i) = fun i => s * coefficientLeray k a i := by
  classical
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, hk, if_false]
    have hsum : (∑ j : Fin 3, (k j : ℂ) * (s * a j)) =
        s * ∑ j : Fin 3, (k j : ℂ) * a j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring

theorem phaseDerivative_bilinearConvection (N : ℕ) (j : Fin 3) (q r : Phase N) :
    phaseDerivative N j (bilinearConvection N q r) =
      bilinearConvection N (phaseDerivative N j q) r +
        bilinearConvection N q (phaseDerivative N j r) := by
  apply Subtype.ext
  apply extendCoeff_injective N
  change phaseCoeff (phaseDerivative N j (bilinearConvection N q r)) =
    phaseCoeff (bilinearConvection N (phaseDerivative N j q) r +
      bilinearConvection N q (phaseDerivative N j r))
  rw [phaseCoeff_phaseDerivative, Assembly.phaseCoeff_add]
  funext k i
  simp only [Pi.add_apply, spectralMultiplier, phaseCoeff_bilinearConvection,
    phaseCoeff_phaseDerivative]
  by_cases hk : k ∈ fullModes N
  · simp only [if_pos hk]
    have hleib : (fun i => derivativeSymbol j k *
        fullBilinearTransport N (phaseCoeff q) (phaseCoeff r) k i) =
          fullBilinearTransport N (spectralMultiplier (derivativeSymbol j) (phaseCoeff q))
            (phaseCoeff r) k +
          fullBilinearTransport N (phaseCoeff q)
            (spectralMultiplier (derivativeSymbol j) (phaseCoeff r)) k := by
      funext l
      exact fullBilinearTransport_spatial_leibniz N j _ _ k l
    have hproj := congrArg (fun a : Fin 3 → ℂ => coefficientLeray k a i) hleib
    rw [coefficientLeray_complex_mul_native, coefficientLeray_add_native] at hproj
    simp only [Pi.add_apply] at hproj
    linear_combination -hproj
  · simp [hk]

theorem inner_bilinearConvection_eq_integral (N : ℕ) (q a b : Phase N) :
    inner ℝ q (bilinearConvection N a b) =
      -(∫ x in unitCube, inner ℝ (synthesis q x)
        (mixedConvection (synthesis a) (synthesis b) x)) := by
  rw [phase_inner_eq_sum, integral_synthesis_mixedConvection, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [phaseCoeff_bilinearConvection, if_pos hk, mul_neg, Complex.neg_re,
    Finset.sum_neg_distrib]
  congr 1
  simpa only [Complex.re_sum] using congrArg Complex.re
    (coefficientLeray_pairing k (phaseCoeff q k)
      (fullBilinearTransport N (phaseCoeff a) (phaseCoeff b) k)
      (phaseCoeff_solenoidal q k))

theorem inner_bilinearConvection_self_zero (N : ℕ) (a b : Phase N) :
    inner ℝ b (bilinearConvection N a b) = 0 := by
  rw [inner_bilinearConvection_eq_integral, integral_synthesis_transport_zero, neg_zero]

theorem inner_bilinearConvection_relative_le (N : ℕ) (q r : Phase N) :
    inner ℝ q (bilinearConvection N q r) ≤ gradientObservable r * ‖q‖^2 := by
  rw [inner_bilinearConvection_eq_integral]
  exact synthesis_relative_transport_integral N q r

end
end QuantumAdapter.Obligations
