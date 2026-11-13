import QuantumAdapter.Obligations.TraceLaplacian
import QuantumAdapter.Obligations.EnergyBilinear
import QuantumAdapter.Assembly.GlobalDrift
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Finite differential expressions evaluated in the actual Galerkin phase.
Syntactic differentiation gives every time derivative of the native orbit;
no time-regularity or jet-existence premise is introduced.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace QuantumAdapter.Obligations

noncomputable section

inductive GalerkinExpr where
  | id : GalerkinExpr
  | add : GalerkinExpr → GalerkinExpr → GalerkinExpr
  | smul : ℝ → GalerkinExpr → GalerkinExpr
  | laplace : GalerkinExpr → GalerkinExpr
  | bilinear : GalerkinExpr → GalerkinExpr → GalerkinExpr

def GalerkinExpr.eval (N : ℕ) : GalerkinExpr → Phase N → Phase N
  | .id, q => q
  | .add e f, q => e.eval N q + f.eval N q
  | .smul a e, q => a • e.eval N q
  | .laplace e, q => phaseLaplacianCLM N (e.eval N q)
  | .bilinear e f, q => bilinearConvectionCLM N (e.eval N q) (f.eval N q)

def GalerkinExpr.driftExpr (ν : ℝ) : GalerkinExpr :=
  .add (.smul (-ν) (.laplace .id)) (.bilinear .id .id)

def GalerkinExpr.differentiate (ν : ℝ) : GalerkinExpr → GalerkinExpr
  | .id => driftExpr ν
  | .add e f => .add (e.differentiate ν) (f.differentiate ν)
  | .smul a e => .smul a (e.differentiate ν)
  | .laplace e => .laplace (e.differentiate ν)
  | .bilinear e f => .add (.bilinear (e.differentiate ν) f)
      (.bilinear e (f.differentiate ν))

theorem GalerkinExpr.eval_driftExpr (ν : ℝ) (N : ℕ) (q : Phase N) :
    (driftExpr ν).eval N q = drift ν N q := by
  simp only [driftExpr, eval, bilinearConvectionCLM_apply, bilinearConvection_self]
  rw [drift_eq_inviscid_sub_laplacian ν N q]
  simp only [neg_smul, sub_eq_add_neg]
  exact add_comm _ _

theorem GalerkinExpr.contDiff_eval (N : ℕ) (e : GalerkinExpr) :
    ContDiff ℝ ∞ (e.eval N) := by
  induction e with
  | id => exact contDiff_id
  | add e f he hf => exact he.add hf
  | smul a e he => exact he.const_smul a
  | laplace e he => exact (phaseLaplacianCLM N).contDiff.comp he
  | bilinear e f he hf =>
    exact ((bilinearConvectionCLM N).contDiff.comp he).clm_apply hf

theorem GalerkinExpr.hasDerivAt_eval_flow {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (t : ℝ) (e : GalerkinExpr) :
    HasDerivAt (fun r => e.eval N (F.map N r q))
      ((e.differentiate ν).eval N (F.map N t q)) t := by
  induction e with
  | id =>
    simpa only [eval, differentiate, eval_driftExpr] using F.orbit_derivative N q t
  | add e f he hf =>
    exact he.add hf
  | smul a e he =>
    exact he.const_smul a
  | laplace e he =>
    exact (phaseLaplacianCLM N).hasFDerivAt.comp_hasDerivAt t he
  | bilinear e f he hf =>
    exact HasDerivAt.clm_apply (F := Phase N) (G := Phase N)
      ((bilinearConvectionCLM N).hasFDerivAt.comp_hasDerivAt t he) hf

def GalerkinExpr.jetExpr (ν : ℝ) : ℕ → GalerkinExpr
  | 0 => .id
  | n + 1 => (jetExpr ν n).differentiate ν

def phaseTimeJet {ν : ℝ} (F : PhaseFlow ν) (N : ℕ) (q : Phase N)
    (n : ℕ) (t : ℝ) : Phase N :=
  (GalerkinExpr.jetExpr ν n).eval N (F.map N t q)

@[simp] theorem phaseTimeJet_zero {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (t : ℝ) : phaseTimeJet F N q 0 t = F.map N t q := rfl

theorem phaseTimeJet_one {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (t : ℝ) :
    phaseTimeJet F N q 1 t = drift ν N (F.map N t q) :=
  GalerkinExpr.eval_driftExpr ν N (F.map N t q)

theorem phaseTimeJet_hasDerivAt {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (n : ℕ) (t : ℝ) :
    HasDerivAt (phaseTimeJet F N q n) (phaseTimeJet F N q (n + 1) t) t :=
  GalerkinExpr.hasDerivAt_eval_flow F N q t (GalerkinExpr.jetExpr ν n)

theorem phaseTimeJet_contDiff {ν : ℝ} (F : PhaseFlow ν)
    (N : ℕ) (q : Phase N) (n : ℕ) : ContDiff ℝ ∞ (phaseTimeJet F N q n) :=
  (GalerkinExpr.contDiff_eval N (GalerkinExpr.jetExpr ν n)).comp
    (QuantumAdapter.Assembly.contDiff_complete_drift_orbit ν N (F.orbit_derivative N q))

end
end QuantumAdapter.Obligations
