`GRAssembly.lean` imports the 85 isolated TEMP endpoints and native GR assembly modules.

`GR_ASSEMBLY_A_TIER.txt` specifies exact scope and remaining root obligations.
`../Auxillary/GR/Assembly/endpoint-index.json` maps declarations to GC nodes and source lines.

External Windows: `run.cmd`.
External Linux: `bash run.sh`.
Both preserve compatible caches and acquire official cached Mathlib objects.
No local Lean execution is part of source preparation.

Status: `A_TIER`: 150 new theorems, 21 definitions; 657 named standard-only audits.
308 source input hashes verified. Root from LI01--LI03: `OPEN` (`c,r,h,q`).

Certificate: `../Auxillary/GR/Assembly/EXTERNAL_CERTIFICATE.json`.
Audited source: `8c72af4b7e0bdfafd305746a8a7b4b94a6801649`.
External run: https://github.com/randogelist/NSE---MAXWELL---GR---QFT/actions/runs/43389123717
