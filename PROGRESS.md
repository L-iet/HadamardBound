# Palomar preparation checkpoint (2 November 2026)

The standalone Git repository is rooted in this Lean directory. Joshua Mark is
the author and responsible maintainer; ORCID 0009-0003-5905-2382. Project files
are staged for review. No commit, remote, publication or registration was created.
The seven-milestone proof completion below remains historical pre-port evidence.

Fresh validation of the module-system port:
- Full Challenge/Solution build passed: 5,811 jobs.
- Axiom audit passed: 156 principal declarations, only propext, Classical.choice
  and Quot.sound. The modern import example also compiled.
- Full native Linux Comparator passed, exit 0: all six independently stated
  claims accepted by con-ron, NanoDa and Lean default kernels. Both source builds
  ran inside bubblewrap (Challenge 2,155 jobs; Solution 5,809 jobs). con-ron
  verified 113,566 declarations. This was not an export-only check.
- Negative control rejected Challenge as its own Solution: illegal sorryAx.
- Reconstructed dependency manifest verified: 1,001 modules from the pinned
  archive with recorded compatibility and module-system changes.
- Metadata v0.4 schema, source preflight and three lexer regression tests passed.
- Repository-local aligned paper compiled with Tectonic 0.17.0; the outer
  manuscript and PDF were not changed.

Exact evidence is in submission/verification.json; logs are ignored under .lake/.
The successful Comparator log is .lake/palomar-comparator.log. No build or
Comparator process remains active. Native Lean 4.35.0 is available under
.proof-tools/lean-4.35.0-linux, outside the sandbox-writable .lake directory.
Its release archive SHA-256 is
7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d.

Publication remains blocked by redistribution permission for original additions
in the logarithm supplement and a final public immutable repository snapshot.
The vendor tree is Git-ignored; the root Apache licence does not relicense it.
submission/permission-request.txt is a draft only, not sent. A deployable Palomar
snapshot needs cleared source in Git or an appropriately licensed pinned Git
dependency; network downloads during sandboxed proof builds are not a solution.
No Lax compatibility check or registry acceptance is claimed.

---

# Formalization checkpoint

All seven milestones in README.md are complete. The mathematical proofs,
ordinary default Lake build, combined axiom audit and documented import example
passed final verification on 28 October 2026.

## Verified mathematical results

The core proves Golay seeds 1/2/10/26, Turyn multiplication and the full Golay
family; the complete Craigen matrix construction and exact transfer dimension;
multiplicative independence; binary representability; all greedy, logarithmic,
rotation and finite-case deductions; covering counts and inversion; asymptotic
Hadamard and gap deductions; flat orthogonal matrices; variance-sensitive
rounding concentration; and the optimal sign-matrix condition-number bound.

The sparse input has now been discharged. The verified external theorem
QuadraticPi.rationalLogRatio_finite_good, from the arXiv:2610.28079v1 Lean
supplement, gives finite sets of reduced rational approximants to log(a)/log(b)
for every exponent >3 and independent positive rational bases. Its actual
GoodRationalApproximations and NoPowerRelation definitions and exact theorem
type were inspected. Independence follows from the core's irrationality proof
in the 10/2 case and the general IndependentBases theorem for arbitrary bases.

The external theorem closure is 1,000 modules. Our adapter additionally uses
QuadraticPi.ExponentConverse, giving 1,001 external modules in the full build.
All 1,001 modules, all five integration adapters and all nine final endpoints
have compiled under Lean 4.35.0. Their actual axiom audits passed, using only
propext, Classical.choice and Quot.sound. Evidence:

* .lake/logarithms-audit/report.json: integrationPassed = true.
* .lake/logarithms-audit/logs/external-endpoint-audit.log.
* .lake/logarithms-audit/logs/hadamard-adapter-audit.log.
* .lake/logarithms-audit/logs/complete-results-audit.log.

The unconditional theorem is HadamardMultibase.sparseRepresentationBound.
All closed final endpoints are in namespace HadamardMultibase.Complete:
main_bound, tau_bound, quantitative_gap_bound, subpolynomial_gap_bound,
covering_bounds, golay_covering_bounds, flat_orthogonal_bound,
approximateHadamard_condition_bound, optimalConditionNumber_bound.
There are no sparse or Diophantine hypotheses in these endpoint types.

## Final acceptance

* `lake --rehash build`: exit 0, 5,809 jobs. Both default targets,
  HadamardMultibase and HadamardMultibaseComplete, compiled successfully.
  Final run used LEAN_NUM_THREADS=4, with two threads per supplement module.
* `lake env lean Audit.lean`: exit 0; 156 declarations (140 core and 16
  external/adapters/final) audited. The axiom union is exactly propext,
  Classical.choice and Quot.sound.
* The README client importing HadamardMultibaseComplete compiled in the normal
  Lake environment, checking the sparse, main, covering and optimal-condition
  endpoints.
* Source scans of 86 project Lean files and 1,001 external dependency files
  found no sorry, admit, custom axiom or native_decide tokens outside comments
  and strings. The external files match the pinned archive plus all 34 recorded
  compatibility patches, with no mismatches.
* Public definitions and theorem types were reviewed against all seven
  milestones and the manuscript, including the corrected flatness range below.

Local evidence (ignored build outputs): .lake/final-default-build.log,
.lake/final-combined-audit.log, .lake/final-readme-client.log,
.lake/final-acceptance.json, .lake/verification-source-scan.json, and
.lake/logarithms-audit/source-integrity.json. Final acceptance was recorded at
2026-10-28T07:37:44Z. The isolated proof verification also passed independently.

## Reproducible dependency setup

Archive: https://arxiv.org/src/2610.28079v1
SHA256: 2b37bfa6f04a1316eead45f1b6ba2ad660eef6a02f00b31476d603a7e55de69e
python scripts/audit_logarithms.py --prepare-only verifies/extracts/patches
source. lake env python scripts/audit_logarithms.py --jobs 8 --threads 2
reproduces isolated compiler and axiom verification.

Sources are cached under ignored sources/logarithms-2610.28079v1; archive and
notices are preserved. SOURCE-NOTICE.txt makes no new blanket software license
election for the author's additions; source is downloaded, not vendored.
OAI upstream notices remain in force. Own compatibility changes are recorded
in integration/logarithms-4.35-patches.json: bundled ordered-homomorphism API
for AddValuation.map, explicit multiline singleton notation, and full
unfolding for affected rewrite/simpa comparisons. No mathematical assumption
or axiom is added. An explicit previousNew field supports upgrading a patch.

The supplement uses supported legacy imports. Own integration files and
HadamardMultibaseComplete use that format to import the modern core.
A legacy-mode client starts with import HadamardMultibaseComplete.

## Environment

Workspace: D:/Papers/Hadamard/lean. Lean/mathlib 4.35.0; mathlib commit
56a005855ea17e0b0958f73ec801ae140b0a1679. Its tracked source was checked clean.
Shell tools use require_escalated because the normal shell sandbox cannot
launch PowerShell here. Authorized reads, edits and builds have been approved.
There is no Git repository at the project root. Source caches/build outputs
are ignored. No subagents were spawned; current instructions prohibit that.

The meaningful flat-matrix statement has 0<epsilon<1/2. The manuscript's
reciprocal is nonpositive for epsilon>=1/2. Formal covering proofs handle
finite initial cases; gap statements use natural orders. The manuscript itself
has not been edited.
