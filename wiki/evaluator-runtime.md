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
