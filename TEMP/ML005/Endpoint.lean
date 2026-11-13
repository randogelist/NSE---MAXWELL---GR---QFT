/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Compactness.Compact

/-!
ML005: source proof/body extraction.
SOURCE = IsCompact.mem_prod_nhdsSet_of_forall
PIN = de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11
SOURCE_URL = https://github.com/leanprover-community/mathlib4/blob/de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11/Mathlib/Topology/Compactness/Compact.lean#L427
SOURCE_SHA256 = 670d9e0723f9b803fd68e21c02b735475cafb7a4612aa0dac16733c5dedb49aa
STATUS = A_TIER_CANDIDATE
DEPENDENCIES = imported original definitions and helper theorems.
EXTRACTION = original command body; original target is not used as the whole proof.
No dependency-free or new compiler certification claim.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology TopologicalSpace Function
variable {Y : Type*} [TopologicalSpace Y]

theorem _root_.GRTemp.ML005.endpoint {K : Set Y} {X : Type*} {l : Filter X} {s : Set (X × Y)}
    (hK : IsCompact K) (hs : ∀ y ∈ K, s ∈ l ×ˢ 𝓝 y) : s ∈ l ×ˢ 𝓝ˢ K :=
  (hK.prod_nhdsSet_eq_biSup l).symm ▸ by simpa using hs

