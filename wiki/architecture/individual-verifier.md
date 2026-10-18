# Individual public verification feedback

Status: verified locally and accepted by fresh independent review.
Verification date: 2026-10-19.
Revision: Dafnyutils `63d5f7e` plus originating plan changes.
Originating [owner plan](../../plan/2026-10-19-codex-individual-verifier.md);
related [root plan](../../../plan/2026-10-19-codex-individual-verifier.md).

Newly generated task workspaces include a protected `eval_support/verify-target.sh`
helper; namespaced releases place the same helper under their task support
directory. `release._public_profile` generates its optional guidance using that
actual directory, so displayed commands match delivered helpers. Run from the workspace root:

```sh
./eval_support/verify-target.sh --list
./eval_support/verify-target.sh --source bench/utils/example/Proof.dfy --symbol 'Proof.Check'
```

The first command validates the entry contract and lists workspace-relative
`source::native-symbol` pairs. Use the exact displayed source and symbol in the
second command. Native constructor names can begin with `#`; quote all symbols.
The wrapper accepts only the documented list form or source-then-symbol form;
it binds the actual task manifest, utility, tool and workspace itself.

`src/verification.py` reuses `EntryContractCheckSession.validate`,
`verification_options` and `_verify_target`. There is no .NET compilation/build
phase for individual feedback. Full Dafny resolution and candidate integrity
validation still run; malformed unrelated reachable source may prevent feedback.
Only reachable editable sources from the validated contract are selectable.
Unknown/prefix/duplicate/protected/outside-workspace selectors fail closed.
Dafny native symbol and source filters use suffix matching. The scoped verifier
rejects same-source suffix-colliding symbols (for example `A.Check` with
`Other.A.Check`), passes an absolute resolved source filter, and rejects remaining
absolute path suffix collisions across known analysis/utility sources. A unique
longer symbol remains selectable; the full gate retains its existing filters.
Candidate verification-limit overrides remain forbidden across editable sources.

A selected declaration receives the established three mutations, seed 0,
isolated assertions, 30-second per-condition limit and 100-second process cap.
Warnings, nonzero exit, timeout, failed mutation results, missing/malformed TRX
and source changes prevent success. A valid target with no proof obligations
returns nonzero with `DAFNY_TARGET_VERIFICATION_OUTCOME=no_obligations` and an
explanation. This is scoped feedback, not evidence of complete verification.

Successful individual feedback emits
`DAFNY_TARGET_VERIFICATION_OUTCOME=verified`, never the complete-gate success
wire `DAFNY_VERIFICATION_OUTCOME=verified`. Scoped selectors cannot be combined
with `--full` or build arguments. Generated `public_rules` advertise the helper
as optional guidance; the mandatory public check stays `./eval_support/verify.sh`.
Final proof scope, scoring and existing release snapshots are unchanged.

Evidence: 58 focused individual/policy/limit unit cases pass locally and in fresh
independent review with storage, filesystem, subprocess, analysis and TRX
boundaries faked (only fixed, small script templates read for generation).
Changed-source Ruff/format checks pass. Expanded source Pyright passes using the
explicit installed dependency path in `/workspace/tmp/codex-individual-verifier/pyright-individual.json`;
the default interpreter discovery misses the pre-existing `pydantic` import in
`release.py`. The root agent reports owner `make test-unit`: 101 passed, 15
deselected, and root `make test`: 123 passed, 19 deselected. These commands prove
unit behavior, not benchmark-wide proofs or provider performance. Root native smoke after corrections passed all eight controls; logs are under
`/workspace/tmp/codex-individual-verifier/native-probe.log` and
`native/summary.json`. This bounded synthetic smoke establishes native helper
behavior, not benchmark-wide proof completion. Final integration evidence is
recorded separately in the originating plan.
No image rollout or paid experiment was performed.
