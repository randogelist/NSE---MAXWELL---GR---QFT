import GRAssembly.HodgeTransport
import ME10.Endpoint
import ME11.Endpoint
import ME12.Endpoint
import ME17.E01.Endpoint
import ME17.E02.Endpoint
import ML022.Endpoint

/-!
GC02 ordinary-time conversion at interior points of the source halfspace.
These theorems state their global halfspace smoothness explicitly. They do
not identify a finite analytic slab with the entire source halfspace.
-/
set_option autoImplicit false
set_option Elab.async true

namespace NSEGR.Assembly
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
noncomputable section

/-- The source within derivative is the native ordinary derivative at t>0. -/
theorem scalarTimeDerivative_eq_local (f : Pressure) {t : ℝ} (ht : 0 < t) :
    NSEMaxwell.Classical.scalarTimeDerivative f t = scalarLocalTimeDerivative f t := by
  funext x
  exact GRTemp.ML022.endpoint (Ici_mem_nhds ht)

/-- ME10 transports the actual negative-symbol inverse on the source halfspace. -/
theorem poissonInverse_halfspace_smooth {f : Pressure}
    (hf : NSEMaxwell.Classical.SmoothPressure f)
    (hp : NSEMaxwell.Classical.PeriodicPressure f) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => poissonInverse (f z.1) z.2)
      NSEMaxwell.Classical.forwardSpacetime := by
  have h := (GRTemp.ME10.endpoint hf hp).neg
  change ContDiffOn ℝ ∞
    (fun z : ℝ × Vec => -NSEMaxwell.Classical.scalarL (f z.1) z.2)
    NSEMaxwell.Classical.forwardSpacetime at h
  simpa only [poissonInverse_eq_neg_scalarL, Pi.neg_apply] using h

/-- Actual ordinary-time scalar multiplier differentiation from ME11. -/
theorem scalarL_hasDerivAt_pos (f : Pressure)
    (hf : NSEMaxwell.Classical.SmoothPressure f)
    (hp : NSEMaxwell.Classical.PeriodicPressure f)
    {t : ℝ} (ht : 0 < t) (x : Vec) :
    HasDerivAt (fun s => NSEMaxwell.Classical.scalarL (f s) x)
      (NSEMaxwell.Classical.scalarL (scalarLocalTimeDerivative f t) x) t := by
  have hcurve : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hc := (GRTemp.ME11.endpoint f hf hp (z := (t, x)) ht).comp_hasDerivAt t hcurve
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hc
  have hD : (NSEMaxwell.HodgeProof.inverseScalarSeriesDerivative f (t, x) (1, 0)).re =
      NSEMaxwell.Classical.scalarL (scalarLocalTimeDerivative f t) x := by
    have he := congrFun (NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries
      (NSEMaxwell.Classical.scalarTimeDerivative f t)
      (NSEMaxwell.HodgeProof.cubeSlice_contDiff _
        (GRTemp.ME17.E01.endpoint hf) ht.le)
      (GRTemp.ME17.E02.endpoint hp t ht.le)) x
    rw [scalarTimeDerivative_eq_local f ht] at he
    simpa [NSEMaxwell.HodgeProof.inverseScalarSeriesDerivative,
      NSEMaxwell.HodgeProof.timeProjection, NSEMaxwell.HodgeProof.spaceProjection,
      NSEMaxwell.HodgeProof.inverseScalarSeries,
      SingularClosure.realFourierSeries, scalarTimeDerivative_eq_local f ht] using he.symm
  change HasDerivAt
    (fun s => (NSEMaxwell.HodgeProof.inverseScalarSeries f (s, x)).re)
    ((NSEMaxwell.HodgeProof.inverseScalarSeriesDerivative f (t, x) (1, 0)).re) t at hr
  rw [hD] at hr
  apply hr.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact congrFun (NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries (f s)
    (NSEMaxwell.HodgeProof.cubeSlice_contDiff f hf hs.le) (hp s hs.le)) x

/-- GC02: native G commutes with the ordinary derivative for positive times. -/
theorem poissonInverse_hasDerivAt_pos (f : Pressure)
    (hf : NSEMaxwell.Classical.SmoothPressure f)
    (hp : NSEMaxwell.Classical.PeriodicPressure f)
    {t : ℝ} (ht : 0 < t) (x : Vec) :
    HasDerivAt (fun s => poissonInverse (f s) x)
      (poissonInverse (scalarLocalTimeDerivative f t) x) t := by
  simpa only [poissonInverse_eq_neg_scalarL, Pi.neg_apply] using
    (scalarL_hasDerivAt_pos f hf hp ht x).neg

theorem poissonInverse_localTimeDerivative_pos (f : Pressure)
    (hf : NSEMaxwell.Classical.SmoothPressure f)
    (hp : NSEMaxwell.Classical.PeriodicPressure f)
    {t : ℝ} (ht : 0 < t) :
    scalarLocalTimeDerivative (fun s => poissonInverse (f s)) t =
      poissonInverse (scalarLocalTimeDerivative f t) := by
  funext x
  exact (poissonInverse_hasDerivAt_pos f hf hp ht x).deriv

/-- The cube mean commutes with the ordinary derivative on the same domain. -/
theorem scalarMean_hasDerivAt_pos (f : Pressure)
    (hf : NSEMaxwell.Classical.SmoothPressure f)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => scalarMean (f s))
      (scalarMean (scalarLocalTimeDerivative f t)) t := by
  have h := (GRTemp.ME12.endpoint f hf ht.le).hasDerivAt (Ici_mem_nhds ht)
  change HasDerivAt (fun s => scalarMean (f s))
    (scalarMean (NSEMaxwell.Classical.scalarTimeDerivative f t)) t at h
  rwa [scalarTimeDerivative_eq_local f ht] at h

end
end NSEGR.Assembly
