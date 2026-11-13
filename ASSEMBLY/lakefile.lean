import Lake

open Lake DSL

package nse_gr_assembly where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"

lean_lib GRAdapter where
  srcDir := "../GR_adapter"
  globs := #[.andSubmodules `GRAdapter]

lean_lib NSEGRForward where
  srcDir := "../GR_adapter"

lean_lib NSEGRReverse where
  srcDir := "../GR_adapter"

lean_lib ML001 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML001]

lean_lib ML002 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML002]

lean_lib ML003 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML003]

lean_lib ML004 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML004]

lean_lib ML005 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML005]

lean_lib ML006 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML006]

lean_lib ML007 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML007]

lean_lib ML008 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML008]

lean_lib ML009 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML009]

lean_lib ML010 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML010]

lean_lib ML011 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML011]

lean_lib ML012 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML012]

lean_lib ML013 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML013]

lean_lib ML014 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML014]

lean_lib ML015 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML015]

lean_lib ML016 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML016]

lean_lib ML017 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML017]

lean_lib ML018 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML018]

lean_lib ML019 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML019]

lean_lib ML020 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML020]

lean_lib ML021 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML021]

lean_lib ML022 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML022]

lean_lib ML023 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML023]

lean_lib ML024 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML024]

lean_lib ML025 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML025]

lean_lib ML026 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML026]

lean_lib ML027 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML027]

lean_lib ML028 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML028]

lean_lib ML029 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML029]

lean_lib ML030 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML030]

lean_lib ML031 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML031]

lean_lib ML032 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML032]

lean_lib ML033 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML033]

lean_lib ML034 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML034]

lean_lib ML035 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML035]

lean_lib ML036 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML036]

lean_lib ML037 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML037]

lean_lib ML038 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML038]

lean_lib ML039 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML039]

lean_lib ML040 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML040]

lean_lib ML041 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML041]

lean_lib ML042 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML042]

lean_lib ML043 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML043]

lean_lib ML044 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML044]

lean_lib ML045 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML045]

lean_lib ML046 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML046]

lean_lib ML047 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML047]

lean_lib ML048 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML048]

lean_lib ML049 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML049]

lean_lib ML050 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML050]

lean_lib ML051 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML051]

lean_lib ML052 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML052]

lean_lib ML053 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML053]

lean_lib ML054 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML054]

lean_lib ML055 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML055]

lean_lib ML056 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML056]

lean_lib ML057 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML057]

lean_lib ML058 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML058]

lean_lib ML059 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML059]

lean_lib ML060 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML060]

lean_lib ML061 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML061]

lean_lib ML062 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML062]

lean_lib ML063 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML063]

lean_lib ML064 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML064]

lean_lib ML065 where
  srcDir := "../TEMP"
  globs := #[.submodules `ML065]

lean_lib ME01 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME01]

lean_lib ME02 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME02]

lean_lib ME03 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME03]

lean_lib ME04 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME04]

lean_lib ME05 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME05]

lean_lib ME06 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME06]

lean_lib ME07 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME07]

lean_lib ME08 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME08]

lean_lib ME09 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME09]

lean_lib ME10 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME10]

lean_lib ME11 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME11]

lean_lib ME12 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME12]

lean_lib ME13 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME13]

lean_lib ME14 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME14]

lean_lib ME15 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME15]

lean_lib ME16 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME16]

lean_lib ME17 where
  srcDir := "../TEMP"
  globs := #[.submodules `ME17]

lean_lib FourierHodgeLaws where
  srcDir := "../TEMP"
  globs := #[.submodules `FourierHodgeLaws]

lean_lib SingularClosure where
  srcDir := "../TEMP"
  globs := #[.submodules `SingularClosure]

lean_lib NSEMaxwell where
  srcDir := "../TEMP"
  globs := #[.submodules `NSEMaxwell]

lean_lib NSEMaxwellForward where
  srcDir := "../TEMP"

lean_lib NSEMaxwellReverse where
  srcDir := "../TEMP"

lean_lib MaxwellEndpoint where
  srcDir := "../TEMP"
  globs := #[.andSubmodules `MaxwellEndpoint]

lean_lib TempEndpoints where
  srcDir := "../TEMP"

@[default_target]
lean_lib GRAssembly where
  globs := #[.andSubmodules `GRAssembly]
