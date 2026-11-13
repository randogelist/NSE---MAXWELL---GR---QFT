/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Constructions.SumProd

/-!
ML001: source proof/body extraction.
SOURCE = mem_nhds_prod_iff'
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Topology/Constructions/SumProd.lean#L290
SOURCE_SHA256 = 35d6365bebe8c5d331fe01289e857ccc81e6f6392b1f01835d834a35a6931666
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology TopologicalSpace Function
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem _root_.GRTemp.ML001.endpoint {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧ u ×ˢ v ⊆ s :=
  ((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans <| by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]

