# Verification record

Verified locally on 2026-10-07 using Rocq 9.1.0, OCaml 4.14.2, and the standard
library bundled with Rocq Platform 2026.07.0 on Windows x86_64.

Command:

```powershell
python scripts/check.py --coqc '<Rocq Platform directory>\bin\coqc.exe'
```

Result:

```text
The Rocq Prover, version 9.1.0
compiled with OCaml 4.14.2
Compiling theories/Prelude.v
Compiling theories/Model.v
Compiling theories/Safety.v
Compiling theories/Examples.v
Compiling theories/Audit.v
[21 occurrences of: Closed under the global context]
Independently checking compiled proof objects...
PASS: 5 modules compiled; 21 assumption audits closed; kernel check passed.
```

The source-text scan found no unfinished proofs or axiom declarations in the
compiled modules. The positive traces and unsafe-action rejection examples are
theorems checked with the rest of the project. Generated proof objects are
ignored by Git and can be reproduced with the same check script.

The GitHub Actions workflow pins `rocq-core` 9.1.0 and `rocq-stdlib` 9.1.0. Its
remote execution is separate from this local verification record; this document
does not assert a successful hosted CI run.
