# Candidate verification policy

Status: verified locally and by fresh independent review.
Verified date: 2026-10-18.
Revision: Dafnyutils `5da26fd4776bc8187bec769fb663e2c44048d991` plus this task's changes.
Originating [plan](../../plan/2026-10-18-align-codex-topdown-verification.md).

Public checks and final candidate scoring reuse `src/verification.py`; there is no
provider-dependent branch. Each native proof target gets one
`measure-complexity --mutations 3 --random-seed 0` process, isolated assertions,
a 30-second limit per verification condition per mutation, and its own 100-second
outer process deadline. The three mutations occur inside that one command.
`runtime.process.run_process_capture_bytes` captures output and stops the process
group on timeout. Build and entry-contract phases keep their existing behavior.

The native `definition-analysis --include-verification-facts` opt-in exposes
`sourceFacts.verificationTargets`, containing exact `ICanVerify` names, source paths
and authored attributes. `src/analysis/client.py` requires the field when requested;
`src/entry_contract.py` intersects those targets with the existing reachable,
editable verification sources. No Python declaration-name guessing is needed.
This preserves constrained type/witness obligations, function-by-method obligations,
and datatype constructor default-value checks, including native `#` names.
Legacy consumers do not request the extra field and keep their existing wire.

`validated_entry_contract` rejects declaration-level `timeLimit`,
`timeLimitMultiplier`, their modern forms and the internal equivalent spelling
in editable utility sources. It checks both authored definition attributes and
native target attributes, including constructor attributes. Baseline manifest
creation does not run that candidate restriction; unchanged protected support
remains governed by immutable fingerprints. Source trust checks and fingerprint
rules remain unchanged. Generated task profiles publish the policy through the
existing `public_rules` contract.

A successful process alone is insufficient: native warnings, nonzero exit,
outer timeout, failed TRX outcomes, missing/malformed reports, and changed source
identity all prevent success. Bodyless candidate callables still fail. Individual
known targets may have no proof obligations, but final aggregate evidence retains
its existing positive-total requirement for outcome-wire compatibility.

Evidence: focused tests in `tests/core/test_verification_policy.py` and
`tests/core/test_verification_limits.py` use in-memory process/report/storage
boundaries; they never create temporary directories or launch native processes.
Scoped Ruff and changed-source Pyright checks pass. Base configured Pyright has
an interpreter-discovery limitation; with installed dependency paths supplied,
full-source checking exposes an unrelated pre-existing return-type error in
`src/evaluation/agent/runtime.py:835`. Full historical suites contain prohibited
temporary-directory workloads and were not executed. Local unit checks establish
policy wiring and failure handling, not all-task proofs, provider performance,
runtime-oracle scores or statistical conclusions.

Fresh independent review passed 25 policy/limit units, seven native analyzer
cases, driver/test builds, scoped lint/source typing and generic native proof and
attribute controls. Parent's final evaluator smoke passed six targets/18 mutation
receipts and rejected both a bad constructor default and helper timeout override.
Evidence and baseline native-style limitations are recorded in the originating
plan. No full historical suite, benchmark suite or provider experiment was run.
