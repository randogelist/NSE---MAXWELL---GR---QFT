`GRAssembly.lean` imports the 85 isolated TEMP endpoints and native GR assembly modules.

`GR_ASSEMBLY_A_TIER.txt` specifies exact scope and remaining root obligations.
`../Auxillary/GR/Assembly/endpoint-index.json` maps declarations to GC nodes and source lines.

External Windows: `run.cmd`.
External Linux: `bash run.sh`.
Both preserve compatible caches and acquire official cached Mathlib objects.
No local Lean execution is part of source preparation.

Status: `A_TIER_CANDIDATE`. Root from LI01--LI03: `OPEN`.
