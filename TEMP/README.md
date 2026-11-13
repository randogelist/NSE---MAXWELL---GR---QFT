# TEMP — isolated endpoint bodies

```text
ENTRY_FOLDERS = 82
SINGLE_ENDPOINT_MODULES = 85
MATHLIB_ENTRIES = 65
METHLIB_ENTRIES = 17 / 20 declarations
COPIED_NON_MATHLIB_DEPENDENCIES = 72
CURRENT_ENDPOINT_STATUS = A_TIER; 85/85 external source-type and axiom checks PASS
LOCAL_LEAN_EXECUTIONS = 0
```

Each leaf contains `Endpoint.lean` and exact source metadata in `source.json`.
ML047 and ML049 explicitly adapt generated `to_additive` proofs. ML006/ML008
retain their definition-valued outputs; ML064/ML065 export structure-valued
definitions without registering new global instances.

The target proof bodies are isolated. Owning upstream modules remain explicit
imports for definitions, notation, instances and helper results. Mathlib stays
pinned; the 72-module non-Mathlib source closure is copied byte-for-byte.
This does not supply the unimplemented GR adapters or the GR root.

[Endpoint/chain index](INDEX.json) · [Dependency provenance](dependency-sources.json) ·
[Compiler status](TEMP_ENDPOINT_EXTRACTION_A_TIER.txt) · [Exact external certificate](EXTERNAL_CERTIFICATE.json)

External cached execution: `run.cmd` on native Windows, or `bash run.sh` on Linux.
Each export is compared with its original type and receives a named axiom audit.

| Entry | Endpoint modules | Original declarations | GC nodes |
|---|---|---|---|
| ME01 | [`ME01.Endpoint`](ME01/Endpoint.lean) | `NSEMaxwell.HodgeProof.scalarL_eq_realFourierSeries` | GC01, GC03 |
| ME02 | [`ME02.Endpoint`](ME02/Endpoint.lean) | `NSEMaxwell.HodgeProof.scalarL_smooth` | GC02 |
| ME03 | [`ME03.Endpoint`](ME03/Endpoint.lean) | `NSEMaxwell.HodgeProof.vectorL_smooth` | GC02 |
| ME04 | [`ME04.Endpoint`](ME04/Endpoint.lean) | `NSEMaxwell.HodgeProof.vectorL_component` | GC02 |
| ME05 | [`ME05.Endpoint`](ME05/Endpoint.lean) | `NSEMaxwell.HodgeProof.coordinateDerivative_vectorL_commute` | GC02 |
| ME06 | [`ME06.Endpoint`](ME06/Endpoint.lean) | `NSEMaxwell.HodgeProof.divergence_vectorL_commute` | GC02 |
| ME07 | [`ME07.Endpoint`](ME07/Endpoint.lean) | `NSEMaxwell.HodgeProof.neg_laplacian_vectorL` | GC02 |
| ME08 | [`ME08.Endpoint`](ME08/Endpoint.lean) | `NSEMaxwell.HodgeProof.spatialInverseLaplacianLaws` | GC02, GC04 |
| ME09 | [`ME09.Endpoint`](ME09/Endpoint.lean) | `NSEMaxwell.HodgeProof.SpatialInverseLaplacianLaws.K_curl` | GC02 |
| ME10 | [`ME10.Endpoint`](ME10/Endpoint.lean) | `NSEMaxwell.HodgeProof.scalarL_trajectory_smooth` | GC02, GC04 |
| ME11 | [`ME11.Endpoint`](ME11/Endpoint.lean) | `NSEMaxwell.HodgeProof.inverseScalarSeries_hasFDerivAt_pos` | GC02, GC04, GC17 |
| ME12 | [`ME12.Endpoint`](ME12/Endpoint.lean) | `NSEMaxwell.HodgeProof.cubeIntegral_hasDerivWithinAt` | GC02, GC04, GC17 |
| ME13 | [`ME13.Endpoint`](ME13/Endpoint.lean) | `NSEMaxwell.HodgeProof.scalarCoeff_hasDerivAt_pos` | GC02 |
| ME14 | [`ME14.Endpoint`](ME14/Endpoint.lean) | `NSEMaxwell.HodgeProof.uniform_inverseScalarCoeff_moment_bound` | GC02, GC03 |
| ME15 | [`ME15.Endpoint`](ME15/Endpoint.lean) | `NSEMaxwell.HodgeProof.scalarMean_contDiffOn` | GC02, GC04, GC17 |
| ME16 | [`ME16.E01.Endpoint`](ME16/E01/Endpoint.lean)<br>[`ME16.E02.Endpoint`](ME16/E02/Endpoint.lean)<br>[`ME16.E03.Endpoint`](ME16/E03/Endpoint.lean) | `NSEMaxwell.HodgeProof.scalarLift_component`<br>`NSEMaxwell.HodgeProof.scalarLift_contDiff`<br>`NSEMaxwell.HodgeProof.scalarLift_periodic` | GC02 |
| ME17 | [`ME17.E01.Endpoint`](ME17/E01/Endpoint.lean)<br>[`ME17.E02.Endpoint`](ME17/E02/Endpoint.lean) | `NSEMaxwell.HodgeProof.scalarTimeDerivative_smooth`<br>`NSEMaxwell.HodgeProof.scalarTimeDerivative_periodic` | GC02, GC04 |
| ML001 | [`ML001.Endpoint`](ML001/Endpoint.lean) | `mem_nhds_prod_iff'` | GC07, GC08, GC13, GC14 |
| ML002 | [`ML002.Endpoint`](ML002/Endpoint.lean) | `exists_compact_subset` | GC07 |
| ML003 | [`ML003.Endpoint`](ML003/Endpoint.lean) | `IsCompact.elim_finite_subcover` | GC03, GC07, GC14 |
| ML004 | [`ML004.Endpoint`](ML004/Endpoint.lean) | `IsCompact.eventually_forall_of_forall_eventually` | GC08, GC10, GC14, GC15, GC20, GC21, GC22 |
| ML005 | [`ML005.Endpoint`](ML005/Endpoint.lean) | `IsCompact.mem_prod_nhdsSet_of_forall` | GC08 |
| ML006 | [`ML006.Endpoint`](ML006/Endpoint.lean) | `Set.iUnionLift` | GC03, GC09 |
| ML007 | [`ML007.Endpoint`](ML007/Endpoint.lean) | `Set.iUnionLift_of_mem` | GC03, GC09 |
| ML008 | [`ML008.Endpoint`](ML008/Endpoint.lean) | `Set.liftCover` | GC09 |
| ML009 | [`ML009.Endpoint`](ML009/Endpoint.lean) | `Set.liftCover_of_mem` | GC09 |
| ML010 | [`ML010.Endpoint`](ML010/Endpoint.lean) | `AnalyticAt.congr` | GC09, GC15 |
| ML011 | [`ML011.Endpoint`](ML011/Endpoint.lean) | `AnalyticOnNhd.congr` | GC09 |
| ML012 | [`ML012.Endpoint`](ML012/Endpoint.lean) | `Filter.EventuallyEq.fderiv_eq` | GC02, GC06, GC08, GC09, GC15, GC16, GC20, GC22 |
| ML013 | [`ML013.Endpoint`](ML013/Endpoint.lean) | `Filter.EventuallyEq.fderiv` | GC02, GC06, GC08, GC09, GC15, GC16, GC20, GC22 |
| ML014 | [`ML014.Endpoint`](ML014/Endpoint.lean) | `Set.piecewise_eqOn` | GC09, GC15 |
| ML015 | [`ML015.Endpoint`](ML015/Endpoint.lean) | `Function.Periodic.zsmul` | GC08, GC09 |
| ML016 | [`ML016.Endpoint`](ML016/Endpoint.lean) | `Function.Periodic.add_period` | GC08, GC09 |
| ML017 | [`ML017.Endpoint`](ML017/Endpoint.lean) | `AnalyticAt.eventually_analyticAt` | GC07, GC13 |
| ML018 | [`ML018.Endpoint`](ML018/Endpoint.lean) | `mem_nhds_iff_exists_Ioo_subset` | GC08, GC10, GC14 |
| ML019 | [`ML019.Endpoint`](ML019/Endpoint.lean) | `ContDiffBump.contDiff` | GC02 |
| ML020 | [`ML020.Endpoint`](ML020/Endpoint.lean) | `ContDiffBump.one_of_mem_closedBall` | GC02 |
| ML021 | [`ML021.Endpoint`](ML021/Endpoint.lean) | `ContDiffBump.tsupport_eq` | GC02 |
| ML022 | [`ML022.Endpoint`](ML022/Endpoint.lean) | `derivWithin_of_mem_nhds` | GC02 |
| ML023 | [`ML023.Endpoint`](ML023/Endpoint.lean) | `FormalMultilinearSeries.summable_norm_mul_pow` | GC03 |
| ML024 | [`ML024.Endpoint`](ML024/Endpoint.lean) | `FormalMultilinearSeries.le_radius_of_summable` | GC03 |
| ML025 | [`ML025.Endpoint`](ML025/Endpoint.lean) | `FormalMultilinearSeries.hasFPowerSeriesOnBall` | GC03 |
| ML026 | [`ML026.Endpoint`](ML026/Endpoint.lean) | `HasFPowerSeriesOnBall.analyticAt` | GC03 |
| ML027 | [`ML027.Endpoint`](ML027/Endpoint.lean) | `tendstoUniformlyOn_tsum` | GC03 |
| ML028 | [`ML028.Endpoint`](ML028/Endpoint.lean) | `continuousOn_tsum` | GC03 |
| ML029 | [`ML029.Endpoint`](ML029/Endpoint.lean) | `hasFDerivAt_tsum_of_isPreconnected` | GC02, GC03, GC04 |
| ML030 | [`ML030.Endpoint`](ML030/Endpoint.lean) | `hasDerivAt_tsum_of_isPreconnected` | GC02, GC03, GC04 |
| ML031 | [`ML031.Endpoint`](ML031/Endpoint.lean) | `hasFDerivAt_integral_of_dominated_of_fderiv_le` | GC02, GC03, GC04, GC12, GC17 |
| ML032 | [`ML032.Endpoint`](ML032/Endpoint.lean) | `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` | GC03 |
| ML033 | [`ML033.Endpoint`](ML033/Endpoint.lean) | `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` | GC03 |
| ML034 | [`ML034.Endpoint`](ML034/Endpoint.lean) | `SummableLocallyUniformlyOn.differentiableOn` | GC03 |
| ML035 | [`ML035.Endpoint`](ML035/Endpoint.lean) | `DifferentiableOn.analyticAt` | GC03, GC21 |
| ML036 | [`ML036.Endpoint`](ML036/Endpoint.lean) | `AnalyticAt.restrictScalars` | GC03 |
| ML037 | [`ML037.Endpoint`](ML037/Endpoint.lean) | `AnalyticAt.re_ofReal` | GC21 |
| ML038 | [`ML038.Endpoint`](ML038/Endpoint.lean) | `DifferentiableOn.isExactOn_ball` | GC21 |
| ML039 | [`ML039.Endpoint`](ML039/Endpoint.lean) | `Complex.IsExactOn.with_val_at` | GC21 |
| ML040 | [`ML040.Endpoint`](ML040/Endpoint.lean) | `intervalIntegral.integral_hasDerivAt_right` | GC21 |
| ML041 | [`ML041.Endpoint`](ML041/Endpoint.lean) | `intervalIntegral.integral_deriv_eq_sub` | GC21 |
| ML042 | [`ML042.Endpoint`](ML042/Endpoint.lean) | `MeasureTheory.integral_tsum_of_summable_integral_norm` | GC02, GC04, GC12, GC17 |
| ML043 | [`ML043.Endpoint`](ML043/Endpoint.lean) | `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` | GC03 |
| ML044 | [`ML044.Endpoint`](ML044/Endpoint.lean) | `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` | GC03 |
| ML045 | [`ML045.Endpoint`](ML045/Endpoint.lean) | `Real.summable_exp_nat_mul_iff` | GC03 |
| ML046 | [`ML046.Endpoint`](ML046/Endpoint.lean) | `Real.summable_pow_mul_exp_neg_nat_mul` | GC03 |
| ML047 | [`ML047.Endpoint`](ML047/Endpoint.lean) | `summable_int_iff_summable_nat_and_neg` | GC03 |
| ML048 | [`ML048.Endpoint`](ML048/Endpoint.lean) | `Summable.mul_of_nonneg` | GC03 |
| ML049 | [`ML049.Endpoint`](ML049/Endpoint.lean) | `tsum_neg` | GC01 |
| ML050 | [`ML050.Endpoint`](ML050/Endpoint.lean) | `Filter.EventuallyEq.deriv` | GC02, GC06, GC21 |
| ML051 | [`ML051.Endpoint`](ML051/Endpoint.lean) | `AnalyticAt.fderiv` | GC04, GC05, GC06, GC10, GC11, GC12, GC16, GC17, GC18, GC19, GC21 |
| ML052 | [`ML052.Endpoint`](ML052/Endpoint.lean) | `AnalyticAt.contDiffAt` | GC05, GC11, GC16, GC18 |
| ML053 | [`ML053.Endpoint`](ML053/Endpoint.lean) | `ContDiffAt.isSymmSndFDerivAt_of_omega` | GC06, GC11, GC16, GC17, GC18, GC19, GC21 |
| ML054 | [`ML054.Endpoint`](ML054/Endpoint.lean) | `AnalyticAt.curry_left` | GC04, GC17 |
| ML055 | [`ML055.Endpoint`](ML055/Endpoint.lean) | `Matrix.PosDef.of_dotProduct_mulVec_pos` | GC15 |
| ML056 | [`ML056.Endpoint`](ML056/Endpoint.lean) | `Matrix.PosDef.add_posSemidef` | GC15 |
| ML057 | [`ML057.Endpoint`](ML057/Endpoint.lean) | `Matrix.PosDef.isUnit` | GC15 |
| ML058 | [`ML058.Endpoint`](ML058/Endpoint.lean) | `Matrix.nonneg_iff_posSemidef` | GC15 |
| ML059 | [`ML059.Endpoint`](ML059/Endpoint.lean) | `CFC.sqrt_nonneg` | GC15 |
| ML060 | [`ML060.Endpoint`](ML060/Endpoint.lean) | `CFC.sqrt_mul_sqrt_self` | GC15 |
| ML061 | [`ML061.Endpoint`](ML061/Endpoint.lean) | `CFC.isUnit_sqrt_iff` | GC15 |
| ML062 | [`ML062.Endpoint`](ML062/Endpoint.lean) | `Matrix.det_fromBlocks_zero₂₁` | GC15 |
| ML063 | [`ML063.Endpoint`](ML063/Endpoint.lean) | `Matrix.isUnit_iff_isUnit_det` | GC15 |
| ML064 | [`ML064.Endpoint`](ML064/Endpoint.lean) | `Matrix.IsHermitian.instContinuousFunctionalCalculus` | GC15 |
| ML065 | [`ML065.Endpoint`](ML065/Endpoint.lean) | `Matrix.instCStarRing` | GC15 |

Cached native Linux [run 43383376659](https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43383376659) passed at `ceed85075fde80dfea7f3e54568e634f6f38ab12`: 85/85 compiled endpoints, exact source-type matches and standard-only named audits; 253 source-file hashes verified. Immutable source comments and catalog metadata retain their preparation labels; the certificate overlay records current promotion. GR adapters and root remain open.
