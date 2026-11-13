`ROOT_STATUS = A_TIER / CONDITIONAL_FORMAL_CLOSURE`.
`U1 = !=!; U2 = !=!; U3 = !=!`.

Exact endpoint: [NSE_GR_THREE_OBLIGATION_CLOSURE.lean](GRAssembly/NSE_GR_THREE_OBLIGATION_CLOSURE.lean).
Scope: [NSE_GR_THREE_OBLIGATION_CLOSURE_A_TIER.txt](NSE_GR_THREE_OBLIGATION_CLOSURE_A_TIER.txt).
Retained premises: `nu > 0`, `rho != 0`, `LiteratureInputs` (LI01 CK, LI02 Gaussian jets, LI03 smooth Fourier).
Native records `c,r,h,q`: internally constructed; no additional native-law premise.

Target: local jointly analytic period-one 3D NSE germs modulo time-pressure
gauge, equivalent to the independent marked 5D normalized Gaussian vacuum
zero-stress sector germs. Global NSE regularity and arbitrary 4D GR are outside this endpoint.

External compiler and named axiom audits: `898/898 PASS_STANDARD_ONLY`.
Verified source files: `337`.
Audited source: `2efaf74109eb30b6ca3c3bc426b4c7da5811f7b2`.
External run: https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43471012374

[Certificate](../Auxillary/GR/Closure/EXTERNAL_CERTIFICATE.json).
[Exact derivation crosswalk](../Auxillary/GR/Closure/endpoint-crosswalk.json).
[Retained compiler/audit evidence](../Auxillary/GR/Closure/EXTERNAL_EVIDENCE.zip).

External Windows: `run.cmd --dag-build --individual-modules --keep-going`.
External Linux: `bash run.sh --dag-build --individual-modules --keep-going`.
One Lake process schedules the dependency graph; theorem-level audits remain ordered.
Compiler, pinned shared dependency and incremental project caches are preserved.
`LOCAL_LEAN_EXECUTIONS = 0`.

Historical baseline certificate: `../Auxillary/GR/Assembly/EXTERNAL_CERTIFICATE.json`.
Its source `8c72af4b7e0bdfafd305746a8a7b4b94a6801649` had 657 named audits and open native records;
the Closure certificate above records the current exact root promotion.
