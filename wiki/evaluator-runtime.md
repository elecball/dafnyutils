# Evaluator runtime dependencies

Status: current
Verified: 2026-10-22, working tree based on `16f2778`
Originating plan: [restore touch evaluator runtime](../plan/2026-10-22-touch-evaluator-runtime.md)

The touch benchmark needs the trusted native `touch_time_parser` beside its
compiled evaluator DLL. Ordinary `benchmarks.make_tasks._build` builds that
dependency, while generated public `eval_support/build.sh` only compiles Dafny.
This separation is intentional: candidate containers receive public inputs and
tools, not the trusted repository or GNU source/build trees.

`evaluation.submission.api._evaluate_captured` prepares the runtime on the trusted
host before checks when no operator/capture block exists. It selects the canonical
`task.configuration.name`, so a public task alias does not suppress preparation.
`evaluation.submission.workspace.prepare_evaluator_runtime` uses the existing
touch Makefile's `build-time-parser` target. `BUILD_DIR` stays in the trusted
repository; `TOUCH_TIME_PARSER` points to that evaluation's exact
`_build/bench/touch_time_parser` output. Absolute output paths preserve standalone
relative-directory use when Make changes directories.

Each evaluation uses its own linker output. The existing GNU build lock protects
GNU preparation, but does not cover the helper link after that preparation. Do
not replace isolated outputs with an unchecked shared helper/copy cache. Make
checks dependency freshness on every preparation. After Make succeeds, the
preparer rejects missing, symbolic-link, nonregular and nonexecutable outputs.

Expected process or filesystem preparation failures become an explicit evaluator
runtime infrastructure block and result note. Existing required checks and score
aggregation remain unchanged; candidate capture metadata is not relabeled as a
submission error. The shared hook applies to standalone and multi-task archive
evaluation with either new or caller-managed evaluator sandboxes.

IOExtern's trusted-repository fallback can hide a missing adjacent helper during
implementation tests. Fuzzer staging already explicitly requires the helper as a
DLL sibling and copies it into the isolated DUT runtime. Providing an environment
override alone does not repair that deployment requirement.

Sources: `src/benchmarks/make_tasks.py::_build`,
`bench/utils/touch/Makefile::build-time-parser`,
`src/evaluation/task/scripts/build.sh`,
`src/evaluation/submission/workspace.py::prepare_evaluator_runtime`,
`src/evaluation/submission/api.py::_evaluate_captured`,
`bench/core/IOExtern.cs::TrustedTimeParserPath`,
`tools/coreutils_fuzzer/src/utils/capabilities.rs` and
`tools/coreutils_fuzzer/src/fuzz/container.rs::runtime_files`.

Evidence: `tests/evaluation/test_evaluator_runtime.py` exercises fake process,
metadata, executable-access, runner and persistence boundaries. It denies real
filesystem mutation, copying and native subprocesses. Serial fake cases verify
distinct output selection, not actual concurrent compilation. No native build,
Docker run, candidate replay, benchmark oracle, Dafny proof or provider call was
performed for this repair; successful fake checks do not establish live efficacy.

Local acceptance covers 130 owner unit cases, 16 final integrations, repository
Ruff and the root protocol roundtrip. The integration cases use bounded native
analysis/fingerprinting and subprocess lifecycles, not helper compilation or
benchmark proofs. Fresh independent review accepts the 17 focused fake controls
and changed-source typing. Full-source typing retains one unchanged baseline
return-type error at `evaluation/agent/runtime.py:834`; no diagnostic is suppressed.
The originating plan records exact commands, hashes, versions and limits.


## Private-control metadata cleanup — 2026-10-26

Status: source independently accepted with owner unit/final-integration gates.
Sixth cohort weekly-20261026T000458Z-48fb3c6ce74f independently observed normal
shared-cat-r02 exit0, successful cleanup/regular archive production, and final
success with all four evaluation sets passed (5/5 commands) at01:14Z. This is one
live case; the user subsequently stopped the incomplete eighty-trial cohort.
Origin: [private control cleanup plan](../plan/2026-10-26-private-control-cleanup.md).
Sources: evaluation/agent/runtime.py::_ownership_handoff_targets,
handoff_agent_sandbox_ownership, cleanup_sandbox_control_files,
run_candidate_lifecycle; evaluation/agent/ownership.py.

Trusted controllers can create root-owned runtime directories under private
/run/agent_home. Excluding that home from output metadata handoff while later
chmodding every private control directory makes host cleanup fail with EPERM.
The lifecycle then returns before packaging, so even an agent exit0 can produce
only blocked evaluations with zero commands. Run statusfailed alone does not
establish that a candidate was evaluated. Operational blocked_reason must be
checked separately without exposing evaluator outputs or private contents.

The private home now participates in the existing bounded, metadata-only
post-termination ownership handoff. Read-only mounts and trusted run/tools
remain protected; source validation, no-follow/alias/hardlink checks and helper
limits remain. The helper preserves modes, reads no contents, uses no network
or forwarded credential environment, and runs only after confirmed shutdown.
Private-home mounts and model restrictions are unchanged; home is not packaged.
Strict cleanup failure and submission/archive/evaluation rules remain unchanged.

The pre-fix fake reproduction reaches the exact EPERM before packaging. Owner
156units/21integrations and Ruff88files pass; independent13focused cases and
additional pure security/lifecycle probes accept the settled source. Default
typing remains limited by host dependency discovery, recorded with exact hashes
and commands in the plan. These checks prove no actual archive production,
benchmark/proof success, paid performance or complete live result. Interrupted
run results are preserved; a fresh native run is separately authorized.

Native evidence is metadata-only: current source runtime.py SHA256
f41a67d25a299594b2ac02d19e21492346900d1c467ca5cece983d60dea65d87,
agent image df8c884cb5e22a8019afd62a729d56b1901b1b5d41befe33a242a274818468fd;
regular result.tar.gz15169bytes, normal agent exit0/no timeout, no blocked
evaluations and exact final status success. Archive contents, private home,
candidate source and evaluator inputs/outputs were not read. These native
observations separately establish this repaired lifecycle on one completed
trial; they do not establish absence of defects in remaining trials.

The user subsequently stopped the sixth cohort at01:38Z. The single complete
live success remains valid evidence; no full-cohort completion or further
repair/rerun is authorized. See the originating plan for preserved results,
explicit interruptions and unreviewed stop-boundary observations.
