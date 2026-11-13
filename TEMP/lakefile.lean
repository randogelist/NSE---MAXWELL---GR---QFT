import Lake

open Lake DSL

package nse_temp where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

lean_lib ML001 where
  globs := #[.submodules `ML001]

lean_lib ML002 where
  globs := #[.submodules `ML002]

lean_lib ML003 where
  globs := #[.submodules `ML003]

lean_lib ML004 where
  globs := #[.submodules `ML004]

lean_lib ML005 where
  globs := #[.submodules `ML005]

lean_lib ML006 where
  globs := #[.submodules `ML006]

lean_lib ML007 where
  globs := #[.submodules `ML007]

lean_lib ML008 where
  globs := #[.submodules `ML008]

lean_lib ML009 where
  globs := #[.submodules `ML009]

lean_lib ML010 where
  globs := #[.submodules `ML010]

lean_lib ML011 where
  globs := #[.submodules `ML011]

lean_lib ML012 where
  globs := #[.submodules `ML012]

lean_lib ML013 where
  globs := #[.submodules `ML013]

lean_lib ML014 where
  globs := #[.submodules `ML014]

lean_lib ML015 where
  globs := #[.submodules `ML015]

lean_lib ML016 where
  globs := #[.submodules `ML016]

lean_lib ML017 where
  globs := #[.submodules `ML017]

lean_lib ML018 where
  globs := #[.submodules `ML018]

lean_lib ML019 where
  globs := #[.submodules `ML019]

lean_lib ML020 where
  globs := #[.submodules `ML020]

lean_lib ML021 where
  globs := #[.submodules `ML021]

lean_lib ML022 where
  globs := #[.submodules `ML022]

lean_lib ML023 where
  globs := #[.submodules `ML023]

lean_lib ML024 where
  globs := #[.submodules `ML024]

lean_lib ML025 where
  globs := #[.submodules `ML025]

lean_lib ML026 where
  globs := #[.submodules `ML026]

lean_lib ML027 where
  globs := #[.submodules `ML027]

lean_lib ML028 where
  globs := #[.submodules `ML028]

lean_lib ML029 where
  globs := #[.submodules `ML029]

lean_lib ML030 where
  globs := #[.submodules `ML030]

lean_lib ML031 where
  globs := #[.submodules `ML031]

lean_lib ML032 where
  globs := #[.submodules `ML032]

lean_lib ML033 where
  globs := #[.submodules `ML033]

lean_lib ML034 where
  globs := #[.submodules `ML034]

lean_lib ML035 where
  globs := #[.submodules `ML035]

lean_lib ML036 where
  globs := #[.submodules `ML036]

lean_lib ML037 where
  globs := #[.submodules `ML037]

lean_lib ML038 where
  globs := #[.submodules `ML038]

lean_lib ML039 where
  globs := #[.submodules `ML039]

lean_lib ML040 where
  globs := #[.submodules `ML040]

lean_lib ML041 where
  globs := #[.submodules `ML041]

lean_lib ML042 where
  globs := #[.submodules `ML042]

lean_lib ML043 where
  globs := #[.submodules `ML043]

lean_lib ML044 where
  globs := #[.submodules `ML044]

lean_lib ML045 where
  globs := #[.submodules `ML045]

lean_lib ML046 where
  globs := #[.submodules `ML046]

lean_lib ML047 where
  globs := #[.submodules `ML047]

lean_lib ML048 where
  globs := #[.submodules `ML048]

lean_lib ML049 where
  globs := #[.submodules `ML049]

lean_lib ML050 where
  globs := #[.submodules `ML050]

lean_lib ML051 where
  globs := #[.submodules `ML051]

lean_lib ML052 where
  globs := #[.submodules `ML052]

lean_lib ML053 where
  globs := #[.submodules `ML053]

lean_lib ML054 where
  globs := #[.submodules `ML054]

lean_lib ML055 where
  globs := #[.submodules `ML055]

lean_lib ML056 where
  globs := #[.submodules `ML056]

lean_lib ML057 where
  globs := #[.submodules `ML057]

lean_lib ML058 where
  globs := #[.submodules `ML058]

lean_lib ML059 where
  globs := #[.submodules `ML059]

lean_lib ML060 where
  globs := #[.submodules `ML060]

lean_lib ML061 where
  globs := #[.submodules `ML061]

lean_lib ML062 where
  globs := #[.submodules `ML062]

lean_lib ML063 where
  globs := #[.submodules `ML063]

lean_lib ML064 where
  globs := #[.submodules `ML064]

lean_lib ML065 where
  globs := #[.submodules `ML065]

lean_lib ME01 where
  globs := #[.submodules `ME01]

lean_lib ME02 where
  globs := #[.submodules `ME02]

lean_lib ME03 where
  globs := #[.submodules `ME03]

lean_lib ME04 where
  globs := #[.submodules `ME04]

lean_lib ME05 where
  globs := #[.submodules `ME05]

lean_lib ME06 where
  globs := #[.submodules `ME06]

lean_lib ME07 where
  globs := #[.submodules `ME07]

lean_lib ME08 where
  globs := #[.submodules `ME08]

lean_lib ME09 where
  globs := #[.submodules `ME09]

lean_lib ME10 where
  globs := #[.submodules `ME10]

lean_lib ME11 where
  globs := #[.submodules `ME11]

lean_lib ME12 where
  globs := #[.submodules `ME12]

lean_lib ME13 where
  globs := #[.submodules `ME13]

lean_lib ME14 where
  globs := #[.submodules `ME14]

lean_lib ME15 where
  globs := #[.submodules `ME15]

lean_lib ME16 where
  globs := #[.submodules `ME16]

lean_lib ME17 where
  globs := #[.submodules `ME17]

lean_lib FourierHodgeLaws where
  globs := #[.submodules `FourierHodgeLaws]

lean_lib SingularClosure where
  globs := #[.submodules `SingularClosure]

lean_lib NSEMaxwell where
  globs := #[.submodules `NSEMaxwell]

lean_lib NSEMaxwellForward

lean_lib NSEMaxwellReverse

lean_lib MaxwellEndpoint where
  globs := #[.andSubmodules `MaxwellEndpoint]

@[default_target]
lean_lib TempEndpoints
