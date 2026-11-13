import ML001.Endpoint
import ML002.Endpoint
import ML003.Endpoint
import ML004.Endpoint
import ML005.Endpoint
import ML006.Endpoint
import ML007.Endpoint
import ML008.Endpoint
import ML009.Endpoint
import ML010.Endpoint
import ML011.Endpoint
import ML012.Endpoint
import ML013.Endpoint
import ML014.Endpoint
import ML015.Endpoint
import ML016.Endpoint
import ML017.Endpoint
import ML018.Endpoint
import ML019.Endpoint
import ML020.Endpoint
import ML021.Endpoint
import ML022.Endpoint
import ML023.Endpoint
import ML024.Endpoint
import ML025.Endpoint
import ML026.Endpoint
import ML027.Endpoint
import ML028.Endpoint
import ML029.Endpoint
import ML030.Endpoint
import ML031.Endpoint
import ML032.Endpoint
import ML033.Endpoint
import ML034.Endpoint
import ML035.Endpoint
import ML036.Endpoint
import ML037.Endpoint
import ML038.Endpoint
import ML039.Endpoint
import ML040.Endpoint
import ML041.Endpoint
import ML042.Endpoint
import ML043.Endpoint
import ML044.Endpoint
import ML045.Endpoint
import ML046.Endpoint
import ML047.Endpoint
import ML048.Endpoint
import ML049.Endpoint
import ML050.Endpoint
import ML051.Endpoint
import ML052.Endpoint
import ML053.Endpoint
import ML054.Endpoint
import ML055.Endpoint
import ML056.Endpoint
import ML057.Endpoint
import ML058.Endpoint
import ML059.Endpoint
import ML060.Endpoint
import ML061.Endpoint
import ML062.Endpoint
import ML063.Endpoint
import ML064.Endpoint
import ML065.Endpoint
import ME01.Endpoint
import ME02.Endpoint
import ME03.Endpoint
import ME04.Endpoint
import ME05.Endpoint
import ME06.Endpoint
import ME07.Endpoint
import ME08.Endpoint
import ME09.Endpoint
import ME10.Endpoint
import ME11.Endpoint
import ME12.Endpoint
import ME13.Endpoint
import ME14.Endpoint
import ME15.Endpoint
import ME16.E01.Endpoint
import ME16.E02.Endpoint
import ME16.E03.Endpoint
import ME17.E01.Endpoint
import ME17.E02.Endpoint
set_option pp.universes false
open Lean Meta Elab Command
#check @mem_nhds_prod_iff'
#check @GRTemp.ML001.endpoint
#print axioms GRTemp.ML001.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML001.endpoint
  let sourceInfo ← Lean.getConstInfo `mem_nhds_prod_iff'
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML001.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML001.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `mem_nhds_prod_iff'
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML001.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML001.endpoint"
#check @exists_compact_subset
#check @GRTemp.ML002.endpoint
#print axioms GRTemp.ML002.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML002.endpoint
  let sourceInfo ← Lean.getConstInfo `exists_compact_subset
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML002.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML002.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `exists_compact_subset
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML002.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML002.endpoint"
#check @IsCompact.elim_finite_subcover
#check @GRTemp.ML003.endpoint
#print axioms GRTemp.ML003.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML003.endpoint
  let sourceInfo ← Lean.getConstInfo `IsCompact.elim_finite_subcover
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML003.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML003.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `IsCompact.elim_finite_subcover
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML003.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML003.endpoint"
#check @IsCompact.eventually_forall_of_forall_eventually
#check @GRTemp.ML004.endpoint
#print axioms GRTemp.ML004.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML004.endpoint
  let sourceInfo ← Lean.getConstInfo `IsCompact.eventually_forall_of_forall_eventually
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML004.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML004.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `IsCompact.eventually_forall_of_forall_eventually
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML004.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML004.endpoint"
#check @IsCompact.mem_prod_nhdsSet_of_forall
#check @GRTemp.ML005.endpoint
#print axioms GRTemp.ML005.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML005.endpoint
  let sourceInfo ← Lean.getConstInfo `IsCompact.mem_prod_nhdsSet_of_forall
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML005.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML005.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `IsCompact.mem_prod_nhdsSet_of_forall
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML005.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML005.endpoint"
#check @Set.iUnionLift
#check @GRTemp.ML006.endpoint
#print axioms GRTemp.ML006.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML006.endpoint
  let sourceInfo ← Lean.getConstInfo `Set.iUnionLift
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML006.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML006.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Set.iUnionLift
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML006.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML006.endpoint"
#check @Set.iUnionLift_of_mem
#check @GRTemp.ML007.endpoint
#print axioms GRTemp.ML007.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML007.endpoint
  let sourceInfo ← Lean.getConstInfo `Set.iUnionLift_of_mem
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML007.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML007.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Set.iUnionLift_of_mem
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML007.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML007.endpoint"
#check @Set.liftCover
#check @GRTemp.ML008.endpoint
#print axioms GRTemp.ML008.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML008.endpoint
  let sourceInfo ← Lean.getConstInfo `Set.liftCover
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML008.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML008.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Set.liftCover
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML008.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML008.endpoint"
#check @Set.liftCover_of_mem
#check @GRTemp.ML009.endpoint
#print axioms GRTemp.ML009.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML009.endpoint
  let sourceInfo ← Lean.getConstInfo `Set.liftCover_of_mem
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML009.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML009.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Set.liftCover_of_mem
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML009.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML009.endpoint"
#check @AnalyticAt.congr
#check @GRTemp.ML010.endpoint
#print axioms GRTemp.ML010.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML010.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticAt.congr
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML010.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML010.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticAt.congr
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML010.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML010.endpoint"
#check @AnalyticOnNhd.congr
#check @GRTemp.ML011.endpoint
#print axioms GRTemp.ML011.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML011.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticOnNhd.congr
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML011.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML011.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticOnNhd.congr
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML011.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML011.endpoint"
#check @Filter.EventuallyEq.fderiv_eq
#check @GRTemp.ML012.endpoint
#print axioms GRTemp.ML012.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML012.endpoint
  let sourceInfo ← Lean.getConstInfo `Filter.EventuallyEq.fderiv_eq
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML012.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML012.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Filter.EventuallyEq.fderiv_eq
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML012.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML012.endpoint"
#check @Filter.EventuallyEq.fderiv
#check @GRTemp.ML013.endpoint
#print axioms GRTemp.ML013.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML013.endpoint
  let sourceInfo ← Lean.getConstInfo `Filter.EventuallyEq.fderiv
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML013.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML013.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Filter.EventuallyEq.fderiv
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML013.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML013.endpoint"
#check @Set.piecewise_eqOn
#check @GRTemp.ML014.endpoint
#print axioms GRTemp.ML014.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML014.endpoint
  let sourceInfo ← Lean.getConstInfo `Set.piecewise_eqOn
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML014.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML014.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Set.piecewise_eqOn
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML014.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML014.endpoint"
#check @Function.Periodic.zsmul
#check @GRTemp.ML015.endpoint
#print axioms GRTemp.ML015.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML015.endpoint
  let sourceInfo ← Lean.getConstInfo `Function.Periodic.zsmul
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML015.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML015.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Function.Periodic.zsmul
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML015.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML015.endpoint"
#check @Function.Periodic.add_period
#check @GRTemp.ML016.endpoint
#print axioms GRTemp.ML016.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML016.endpoint
  let sourceInfo ← Lean.getConstInfo `Function.Periodic.add_period
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML016.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML016.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Function.Periodic.add_period
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML016.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML016.endpoint"
#check @AnalyticAt.eventually_analyticAt
#check @GRTemp.ML017.endpoint
#print axioms GRTemp.ML017.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML017.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticAt.eventually_analyticAt
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML017.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML017.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticAt.eventually_analyticAt
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML017.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML017.endpoint"
#check @mem_nhds_iff_exists_Ioo_subset
#check @GRTemp.ML018.endpoint
#print axioms GRTemp.ML018.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML018.endpoint
  let sourceInfo ← Lean.getConstInfo `mem_nhds_iff_exists_Ioo_subset
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML018.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML018.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `mem_nhds_iff_exists_Ioo_subset
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML018.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML018.endpoint"
#check @ContDiffBump.contDiff
#check @GRTemp.ML019.endpoint
#print axioms GRTemp.ML019.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML019.endpoint
  let sourceInfo ← Lean.getConstInfo `ContDiffBump.contDiff
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML019.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML019.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `ContDiffBump.contDiff
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML019.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML019.endpoint"
#check @ContDiffBump.one_of_mem_closedBall
#check @GRTemp.ML020.endpoint
#print axioms GRTemp.ML020.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML020.endpoint
  let sourceInfo ← Lean.getConstInfo `ContDiffBump.one_of_mem_closedBall
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML020.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML020.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `ContDiffBump.one_of_mem_closedBall
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML020.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML020.endpoint"
#check @ContDiffBump.tsupport_eq
#check @GRTemp.ML021.endpoint
#print axioms GRTemp.ML021.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML021.endpoint
  let sourceInfo ← Lean.getConstInfo `ContDiffBump.tsupport_eq
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML021.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML021.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `ContDiffBump.tsupport_eq
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML021.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML021.endpoint"
#check @derivWithin_of_mem_nhds
#check @GRTemp.ML022.endpoint
#print axioms GRTemp.ML022.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML022.endpoint
  let sourceInfo ← Lean.getConstInfo `derivWithin_of_mem_nhds
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML022.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML022.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `derivWithin_of_mem_nhds
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML022.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML022.endpoint"
#check @FormalMultilinearSeries.summable_norm_mul_pow
#check @GRTemp.ML023.endpoint
#print axioms GRTemp.ML023.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML023.endpoint
  let sourceInfo ← Lean.getConstInfo `FormalMultilinearSeries.summable_norm_mul_pow
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML023.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML023.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `FormalMultilinearSeries.summable_norm_mul_pow
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML023.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML023.endpoint"
#check @FormalMultilinearSeries.le_radius_of_summable
#check @GRTemp.ML024.endpoint
#print axioms GRTemp.ML024.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML024.endpoint
  let sourceInfo ← Lean.getConstInfo `FormalMultilinearSeries.le_radius_of_summable
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML024.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML024.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `FormalMultilinearSeries.le_radius_of_summable
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML024.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML024.endpoint"
#check @FormalMultilinearSeries.hasFPowerSeriesOnBall
#check @GRTemp.ML025.endpoint
#print axioms GRTemp.ML025.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML025.endpoint
  let sourceInfo ← Lean.getConstInfo `FormalMultilinearSeries.hasFPowerSeriesOnBall
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML025.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML025.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `FormalMultilinearSeries.hasFPowerSeriesOnBall
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML025.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML025.endpoint"
#check @HasFPowerSeriesOnBall.analyticAt
#check @GRTemp.ML026.endpoint
#print axioms GRTemp.ML026.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML026.endpoint
  let sourceInfo ← Lean.getConstInfo `HasFPowerSeriesOnBall.analyticAt
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML026.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML026.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `HasFPowerSeriesOnBall.analyticAt
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML026.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML026.endpoint"
#check @tendstoUniformlyOn_tsum
#check @GRTemp.ML027.endpoint
#print axioms GRTemp.ML027.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML027.endpoint
  let sourceInfo ← Lean.getConstInfo `tendstoUniformlyOn_tsum
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML027.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML027.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `tendstoUniformlyOn_tsum
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML027.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML027.endpoint"
#check @continuousOn_tsum
#check @GRTemp.ML028.endpoint
#print axioms GRTemp.ML028.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML028.endpoint
  let sourceInfo ← Lean.getConstInfo `continuousOn_tsum
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML028.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML028.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `continuousOn_tsum
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML028.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML028.endpoint"
#check @hasFDerivAt_tsum_of_isPreconnected
#check @GRTemp.ML029.endpoint
#print axioms GRTemp.ML029.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML029.endpoint
  let sourceInfo ← Lean.getConstInfo `hasFDerivAt_tsum_of_isPreconnected
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML029.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML029.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `hasFDerivAt_tsum_of_isPreconnected
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML029.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML029.endpoint"
#check @hasDerivAt_tsum_of_isPreconnected
#check @GRTemp.ML030.endpoint
#print axioms GRTemp.ML030.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML030.endpoint
  let sourceInfo ← Lean.getConstInfo `hasDerivAt_tsum_of_isPreconnected
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML030.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML030.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `hasDerivAt_tsum_of_isPreconnected
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML030.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML030.endpoint"
#check @hasFDerivAt_integral_of_dominated_of_fderiv_le
#check @GRTemp.ML031.endpoint
#print axioms GRTemp.ML031.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML031.endpoint
  let sourceInfo ← Lean.getConstInfo `hasFDerivAt_integral_of_dominated_of_fderiv_le
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML031.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML031.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `hasFDerivAt_integral_of_dominated_of_fderiv_le
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML031.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML031.endpoint"
#check @Complex.integral_boundary_rect_eq_zero_of_differentiableOn
#check @GRTemp.ML032.endpoint
#print axioms GRTemp.ML032.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML032.endpoint
  let sourceInfo ← Lean.getConstInfo `Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML032.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML032.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Complex.integral_boundary_rect_eq_zero_of_differentiableOn
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML032.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML032.endpoint"
#check @Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
#check @GRTemp.ML033.endpoint
#print axioms GRTemp.ML033.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML033.endpoint
  let sourceInfo ← Lean.getConstInfo `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML033.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML033.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML033.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML033.endpoint"
#check @SummableLocallyUniformlyOn.differentiableOn
#check @GRTemp.ML034.endpoint
#print axioms GRTemp.ML034.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML034.endpoint
  let sourceInfo ← Lean.getConstInfo `SummableLocallyUniformlyOn.differentiableOn
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML034.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML034.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `SummableLocallyUniformlyOn.differentiableOn
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML034.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML034.endpoint"
#check @DifferentiableOn.analyticAt
#check @GRTemp.ML035.endpoint
#print axioms GRTemp.ML035.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML035.endpoint
  let sourceInfo ← Lean.getConstInfo `DifferentiableOn.analyticAt
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML035.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML035.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `DifferentiableOn.analyticAt
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML035.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML035.endpoint"
#check @AnalyticAt.restrictScalars
#check @GRTemp.ML036.endpoint
#print axioms GRTemp.ML036.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML036.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticAt.restrictScalars
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML036.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML036.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticAt.restrictScalars
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML036.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML036.endpoint"
#check @AnalyticAt.re_ofReal
#check @GRTemp.ML037.endpoint
#print axioms GRTemp.ML037.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML037.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticAt.re_ofReal
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML037.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML037.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticAt.re_ofReal
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML037.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML037.endpoint"
#check @DifferentiableOn.isExactOn_ball
#check @GRTemp.ML038.endpoint
#print axioms GRTemp.ML038.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML038.endpoint
  let sourceInfo ← Lean.getConstInfo `DifferentiableOn.isExactOn_ball
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML038.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML038.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `DifferentiableOn.isExactOn_ball
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML038.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML038.endpoint"
#check @Complex.IsExactOn.with_val_at
#check @GRTemp.ML039.endpoint
#print axioms GRTemp.ML039.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML039.endpoint
  let sourceInfo ← Lean.getConstInfo `Complex.IsExactOn.with_val_at
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML039.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML039.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Complex.IsExactOn.with_val_at
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML039.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML039.endpoint"
#check @intervalIntegral.integral_hasDerivAt_right
#check @GRTemp.ML040.endpoint
#print axioms GRTemp.ML040.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML040.endpoint
  let sourceInfo ← Lean.getConstInfo `intervalIntegral.integral_hasDerivAt_right
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML040.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML040.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `intervalIntegral.integral_hasDerivAt_right
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML040.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML040.endpoint"
#check @intervalIntegral.integral_deriv_eq_sub
#check @GRTemp.ML041.endpoint
#print axioms GRTemp.ML041.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML041.endpoint
  let sourceInfo ← Lean.getConstInfo `intervalIntegral.integral_deriv_eq_sub
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML041.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML041.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `intervalIntegral.integral_deriv_eq_sub
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML041.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML041.endpoint"
#check @MeasureTheory.integral_tsum_of_summable_integral_norm
#check @GRTemp.ML042.endpoint
#print axioms GRTemp.ML042.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML042.endpoint
  let sourceInfo ← Lean.getConstInfo `MeasureTheory.integral_tsum_of_summable_integral_norm
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML042.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML042.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `MeasureTheory.integral_tsum_of_summable_integral_norm
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML042.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML042.endpoint"
#check @AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check @GRTemp.ML043.endpoint
#print axioms GRTemp.ML043.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML043.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML043.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML043.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML043.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML043.endpoint"
#check @AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
#check @GRTemp.ML044.endpoint
#print axioms GRTemp.ML044.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML044.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML044.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML044.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML044.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML044.endpoint"
#check @Real.summable_exp_nat_mul_iff
#check @GRTemp.ML045.endpoint
#print axioms GRTemp.ML045.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML045.endpoint
  let sourceInfo ← Lean.getConstInfo `Real.summable_exp_nat_mul_iff
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML045.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML045.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Real.summable_exp_nat_mul_iff
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML045.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML045.endpoint"
#check @Real.summable_pow_mul_exp_neg_nat_mul
#check @GRTemp.ML046.endpoint
#print axioms GRTemp.ML046.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML046.endpoint
  let sourceInfo ← Lean.getConstInfo `Real.summable_pow_mul_exp_neg_nat_mul
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML046.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML046.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Real.summable_pow_mul_exp_neg_nat_mul
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML046.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML046.endpoint"
#check @summable_int_iff_summable_nat_and_neg
#check @GRTemp.ML047.endpoint
#print axioms GRTemp.ML047.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML047.endpoint
  let sourceInfo ← Lean.getConstInfo `summable_int_iff_summable_nat_and_neg
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML047.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML047.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `summable_int_iff_summable_nat_and_neg
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML047.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML047.endpoint"
#check @Summable.mul_of_nonneg
#check @GRTemp.ML048.endpoint
#print axioms GRTemp.ML048.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML048.endpoint
  let sourceInfo ← Lean.getConstInfo `Summable.mul_of_nonneg
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML048.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML048.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Summable.mul_of_nonneg
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML048.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML048.endpoint"
#check @tsum_neg
#check @GRTemp.ML049.endpoint
#print axioms GRTemp.ML049.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML049.endpoint
  let sourceInfo ← Lean.getConstInfo `tsum_neg
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML049.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML049.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `tsum_neg
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML049.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML049.endpoint"
#check @Filter.EventuallyEq.deriv
#check @GRTemp.ML050.endpoint
#print axioms GRTemp.ML050.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML050.endpoint
  let sourceInfo ← Lean.getConstInfo `Filter.EventuallyEq.deriv
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML050.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML050.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Filter.EventuallyEq.deriv
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML050.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML050.endpoint"
#check @AnalyticAt.fderiv
#check @GRTemp.ML051.endpoint
#print axioms GRTemp.ML051.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML051.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticAt.fderiv
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML051.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML051.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticAt.fderiv
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML051.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML051.endpoint"
#check @AnalyticAt.contDiffAt
#check @GRTemp.ML052.endpoint
#print axioms GRTemp.ML052.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML052.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticAt.contDiffAt
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML052.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML052.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticAt.contDiffAt
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML052.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML052.endpoint"
#check @ContDiffAt.isSymmSndFDerivAt_of_omega
#check @GRTemp.ML053.endpoint
#print axioms GRTemp.ML053.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML053.endpoint
  let sourceInfo ← Lean.getConstInfo `ContDiffAt.isSymmSndFDerivAt_of_omega
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML053.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML053.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `ContDiffAt.isSymmSndFDerivAt_of_omega
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML053.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML053.endpoint"
#check @AnalyticAt.curry_left
#check @GRTemp.ML054.endpoint
#print axioms GRTemp.ML054.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML054.endpoint
  let sourceInfo ← Lean.getConstInfo `AnalyticAt.curry_left
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML054.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML054.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `AnalyticAt.curry_left
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML054.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML054.endpoint"
#check @Matrix.PosDef.of_dotProduct_mulVec_pos
#check @GRTemp.ML055.endpoint
#print axioms GRTemp.ML055.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML055.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.PosDef.of_dotProduct_mulVec_pos
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML055.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML055.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.PosDef.of_dotProduct_mulVec_pos
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML055.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML055.endpoint"
#check @Matrix.PosDef.add_posSemidef
#check @GRTemp.ML056.endpoint
#print axioms GRTemp.ML056.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML056.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.PosDef.add_posSemidef
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML056.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML056.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.PosDef.add_posSemidef
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML056.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML056.endpoint"
#check @Matrix.PosDef.isUnit
#check @GRTemp.ML057.endpoint
#print axioms GRTemp.ML057.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML057.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.PosDef.isUnit
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML057.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML057.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.PosDef.isUnit
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML057.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML057.endpoint"
#check @Matrix.nonneg_iff_posSemidef
#check @GRTemp.ML058.endpoint
#print axioms GRTemp.ML058.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML058.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.nonneg_iff_posSemidef
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML058.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML058.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.nonneg_iff_posSemidef
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML058.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML058.endpoint"
#check @CFC.sqrt_nonneg
#check @GRTemp.ML059.endpoint
#print axioms GRTemp.ML059.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML059.endpoint
  let sourceInfo ← Lean.getConstInfo `CFC.sqrt_nonneg
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML059.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML059.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `CFC.sqrt_nonneg
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML059.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML059.endpoint"
#check @CFC.sqrt_mul_sqrt_self
#check @GRTemp.ML060.endpoint
#print axioms GRTemp.ML060.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML060.endpoint
  let sourceInfo ← Lean.getConstInfo `CFC.sqrt_mul_sqrt_self
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML060.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML060.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `CFC.sqrt_mul_sqrt_self
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML060.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML060.endpoint"
#check @CFC.isUnit_sqrt_iff
#check @GRTemp.ML061.endpoint
#print axioms GRTemp.ML061.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML061.endpoint
  let sourceInfo ← Lean.getConstInfo `CFC.isUnit_sqrt_iff
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML061.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML061.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `CFC.isUnit_sqrt_iff
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML061.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML061.endpoint"
#check @Matrix.det_fromBlocks_zero₂₁
#check @GRTemp.ML062.endpoint
#print axioms GRTemp.ML062.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML062.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.det_fromBlocks_zero₂₁
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML062.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML062.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.det_fromBlocks_zero₂₁
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML062.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML062.endpoint"
#check @Matrix.isUnit_iff_isUnit_det
#check @GRTemp.ML063.endpoint
#print axioms GRTemp.ML063.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML063.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.isUnit_iff_isUnit_det
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML063.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML063.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.isUnit_iff_isUnit_det
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML063.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML063.endpoint"
#check @Matrix.IsHermitian.instContinuousFunctionalCalculus
#check @GRTemp.ML064.endpoint
#print axioms GRTemp.ML064.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML064.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.IsHermitian.instContinuousFunctionalCalculus
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML064.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML064.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.IsHermitian.instContinuousFunctionalCalculus
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML064.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML064.endpoint"
#check @Matrix.instCStarRing
#check @GRTemp.ML065.endpoint
#print axioms GRTemp.ML065.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ML065.endpoint
  let sourceInfo ← Lean.getConstInfo `Matrix.instCStarRing
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ML065.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ML065.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `Matrix.instCStarRing
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ML065.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ML065.endpoint"
#check @NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries
#check @GRTemp.ME01.endpoint
#print axioms GRTemp.ME01.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME01.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME01.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME01.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME01.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME01.endpoint"
#check @NSEMaxwell.HodgeProof.scalarL_smooth
#check @GRTemp.ME02.endpoint
#print axioms GRTemp.ME02.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME02.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarL_smooth
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME02.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME02.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarL_smooth
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME02.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME02.endpoint"
#check @NSEMaxwell.HodgeProof.vectorL_smooth
#check @GRTemp.ME03.endpoint
#print axioms GRTemp.ME03.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME03.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.vectorL_smooth
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME03.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME03.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.vectorL_smooth
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME03.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME03.endpoint"
#check @NSEMaxwell.HodgeProof.vectorL_component
#check @GRTemp.ME04.endpoint
#print axioms GRTemp.ME04.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME04.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.vectorL_component
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME04.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME04.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.vectorL_component
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME04.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME04.endpoint"
#check @NSEMaxwell.HodgeProof.coordinateDerivative_vectorL_commute
#check @GRTemp.ME05.endpoint
#print axioms GRTemp.ME05.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME05.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.coordinateDerivative_vectorL_commute
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME05.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME05.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.coordinateDerivative_vectorL_commute
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME05.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME05.endpoint"
#check @NSEMaxwell.HodgeProof.divergence_vectorL_commute
#check @GRTemp.ME06.endpoint
#print axioms GRTemp.ME06.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME06.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.divergence_vectorL_commute
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME06.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME06.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.divergence_vectorL_commute
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME06.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME06.endpoint"
#check @NSEMaxwell.HodgeProof.neg_laplacian_vectorL
#check @GRTemp.ME07.endpoint
#print axioms GRTemp.ME07.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME07.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.neg_laplacian_vectorL
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME07.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME07.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.neg_laplacian_vectorL
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME07.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME07.endpoint"
#check @NSEMaxwell.HodgeProof.spatialInverseLaplacianLaws
#check @GRTemp.ME08.endpoint
#print axioms GRTemp.ME08.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME08.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.spatialInverseLaplacianLaws
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME08.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME08.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.spatialInverseLaplacianLaws
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME08.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME08.endpoint"
#check @NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_curl
#check @GRTemp.ME09.endpoint
#print axioms GRTemp.ME09.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME09.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_curl
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME09.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME09.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_curl
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME09.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME09.endpoint"
#check @NSEMaxwell.HodgeProof.scalarL_trajectory_smooth
#check @GRTemp.ME10.endpoint
#print axioms GRTemp.ME10.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME10.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarL_trajectory_smooth
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME10.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME10.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarL_trajectory_smooth
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME10.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME10.endpoint"
#check @NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivAt_pos
#check @GRTemp.ME11.endpoint
#print axioms GRTemp.ME11.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME11.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivAt_pos
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME11.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME11.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivAt_pos
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME11.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME11.endpoint"
#check @NSEMaxwell.HodgeProof.cubeIntegral_hasDerivWithinAt
#check @GRTemp.ME12.endpoint
#print axioms GRTemp.ME12.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME12.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.cubeIntegral_hasDerivWithinAt
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME12.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME12.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.cubeIntegral_hasDerivWithinAt
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME12.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME12.endpoint"
#check @NSEMaxwell.HodgeProof.scalarCoeff_hasDerivAt_pos
#check @GRTemp.ME13.endpoint
#print axioms GRTemp.ME13.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME13.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarCoeff_hasDerivAt_pos
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME13.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME13.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarCoeff_hasDerivAt_pos
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME13.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME13.endpoint"
#check @NSEMaxwell.HodgeProof.uniform_inverseScalarCoeff_moment_bound
#check @GRTemp.ME14.endpoint
#print axioms GRTemp.ME14.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME14.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.uniform_inverseScalarCoeff_moment_bound
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME14.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME14.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.uniform_inverseScalarCoeff_moment_bound
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME14.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME14.endpoint"
#check @NSEMaxwell.HodgeProof.scalarMean_contDiffOn
#check @GRTemp.ME15.endpoint
#print axioms GRTemp.ME15.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME15.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarMean_contDiffOn
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME15.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME15.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarMean_contDiffOn
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME15.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME15.endpoint"
#check @NSEMaxwell.HodgeProof.scalarLift_component
#check @GRTemp.ME16.E01.endpoint
#print axioms GRTemp.ME16.E01.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME16.E01.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarLift_component
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME16.E01.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME16.E01.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarLift_component
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME16.E01.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME16.E01.endpoint"
#check @NSEMaxwell.HodgeProof.scalarLift_contDiff
#check @GRTemp.ME16.E02.endpoint
#print axioms GRTemp.ME16.E02.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME16.E02.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarLift_contDiff
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME16.E02.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME16.E02.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarLift_contDiff
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME16.E02.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME16.E02.endpoint"
#check @NSEMaxwell.HodgeProof.scalarLift_periodic
#check @GRTemp.ME16.E03.endpoint
#print axioms GRTemp.ME16.E03.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME16.E03.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarLift_periodic
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME16.E03.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME16.E03.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarLift_periodic
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME16.E03.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME16.E03.endpoint"
#check @NSEMaxwell.HodgeProof.scalarTimeDerivative_smooth
#check @GRTemp.ME17.E01.endpoint
#print axioms GRTemp.ME17.E01.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME17.E01.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarTimeDerivative_smooth
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME17.E01.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME17.E01.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarTimeDerivative_smooth
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME17.E01.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME17.E01.endpoint"
#check @NSEMaxwell.HodgeProof.scalarTimeDerivative_periodic
#check @GRTemp.ME17.E02.endpoint
#print axioms GRTemp.ME17.E02.endpoint
run_cmd Lean.Elab.Command.liftTermElabM do
  let cutInfo ← Lean.getConstInfo `GRTemp.ME17.E02.endpoint
  let sourceInfo ← Lean.getConstInfo `NSEMaxwell.HodgeProof.scalarTimeDerivative_periodic
  unless cutInfo.levelParams.length == sourceInfo.levelParams.length do
    throwError "Universe parameter mismatch: GRTemp.ME17.E02.endpoint"
  let cut ← Lean.Meta.mkConstWithFreshMVarLevels `GRTemp.ME17.E02.endpoint
  let original ← Lean.Meta.mkConstWithFreshMVarLevels `NSEMaxwell.HodgeProof.scalarTimeDerivative_periodic
  unless ← Lean.Meta.isDefEq (← Lean.Meta.inferType cut) (← Lean.Meta.inferType original) do
    throwError "Source type mismatch: GRTemp.ME17.E02.endpoint"
  Lean.logInfo "TYPE_MATCH GRTemp.ME17.E02.endpoint"
