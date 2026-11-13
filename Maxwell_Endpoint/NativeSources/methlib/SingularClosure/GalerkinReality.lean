import SingularClosure.GalerkinEnergy

/-!
# Reality of the actual finite Galerkin vector field

Conjugate symmetry is preserved by the concrete Fourier convolution, the
modewise Leray projection, and viscosity. The convolution identity is proved
by reindexing its actual symmetric cutoff, not assumed as a closure property.
-/

set_option autoImplicit false

open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem coefficientLeray_neg_star (k : Frequency) (v : Fin 3 → ℂ) :
    coefficientLeray (-k) (fun i => star (v i)) =
      fun i => star (coefficientLeray k v i) := by
  funext i
  by_cases hk : k = 0
  · subst k
    simp [coefficientLeray]
  · simp [coefficientLeray, hk, neg_ne_zero.mpr hk, Complex.star_def,
      map_sum, mul_comm, mul_left_comm, mul_assoc]

/-- The actual finite transport convolution respects real Fourier symmetry. -/
theorem coefficientTransport_reality (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) : SpectralReality (coefficientTransport N c) := by
  classical
  intro k i
  let term : Frequency → Frequency → ℂ := fun q p =>
    (∑ j : Fin 3, c p j *
      (((2 * Real.pi * ((q j - p j : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)) * c (q - p) i
  have hterm (p : Frequency) : term (-k) (-p) = star (term k p) := by
    have hsub : -k - -p = -(k - p) := by abel
    dsimp [term]
    rw [hsub, hc]
    simp only [Complex.star_def, map_mul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hc]
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_I,
      Pi.neg_apply]
    push_cast
    ring
  change (∑ p ∈ cutoffModes N, term (-k) p) =
    star (∑ p ∈ cutoffModes N, term k p)
  rw [star_sum]
  apply Finset.sum_nbij' (fun p => -p) (fun p => -p)
    (fun p hp => cutoffModes_neg_mem hp) (fun p hp => cutoffModes_neg_mem hp)
  · intro p hp
    simp
  · intro p hp
    simp
  · intro p hp
    simpa only [neg_neg] using hterm (-p)

/-- Both viscosity and projected transport preserve the real coefficient relation. -/
theorem galerkinRhs_reality (ν : ℝ) (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) : SpectralReality (galerkinRhs ν N c) := by
  intro k i
  have htrans : coefficientTransport N c (-k) =
      fun j => star (coefficientTransport N c k j) := by
    funext j
    exact coefficientTransport_reality N c hc k j
  unfold galerkinRhs
  rw [htrans, coefficientLeray_neg_star, hc]
  simp [galerkinFreqSq, Complex.star_def]

end

end SingularClosure
