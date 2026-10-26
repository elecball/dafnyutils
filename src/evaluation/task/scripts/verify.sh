#!/usr/bin/env bash
set -euo pipefail
mode=full
if [[ $# -eq 1 && "$1" == --describe-proof-scope ]]; then
  mode=describe
elif [[ $# -eq 1 && "$1" == --compile-only ]]; then
  mode=compile
elif [[ $# -ne 0 ]]; then
  printf '%s\n' 'Usage: verify.sh [--describe-proof-scope | --compile-only]' >&2
  exit 1
fi
infrastructure_failure() {
  if [[ "$mode" == describe ]]; then
    printf 'Cannot describe proof scope: %s\n' "$1" >&2
  elif [[ "$mode" == compile ]]; then
    printf 'DAFNY_COMPILE_OUTCOME=infrastructure_failure phase=%s\n' "$1"
  else
    printf 'DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=%s\n' "$1"
  fi
  exit 1
}
script_path="${BASH_SOURCE[0]}"
case "$script_path" in
  */*) script_dir="${script_path%/*}" ;;
  *) script_dir="." ;;
esac
script_dir="$(cd "$script_dir" && pwd)" ||
  infrastructure_failure build
if [[ -n "${EVAL_WORKSPACE_DIR:-}" ]]; then
  workspace_root="$EVAL_WORKSPACE_DIR"
else
  workspace_root="$(cd "$script_dir/@{SCRIPT_PARENT}" && pwd)" ||
    infrastructure_failure build
fi
cd "$workspace_root" || infrastructure_failure build
@{BUILD_ENVIRONMENT}
cleanup_dotnet_build_servers() {
  dotnet build-server shutdown >/dev/null 2>&1 || true
}
command -v python3 >/dev/null 2>&1 ||
  infrastructure_failure evidence
python3 -c 'import verification' ||
  infrastructure_failure evidence
common_args=(
  --workspace-root "$workspace_root"
  --utility-root @{UTILITY_ROOT}
  --manifest "$script_dir/entry_contract.json"
  --dafny "${DAFNY_BENCHMARK:-dafny-benchmark}"
)
if [[ "$mode" == describe ]]; then
  python3 -m verification "${common_args[@@]}" --describe-proof-scope
  exit $?
fi
trap cleanup_dotnet_build_servers EXIT
mkdir -p _build/bench || infrastructure_failure build
if [[ "$mode" == compile ]]; then
  python3 -m verification \
    "${common_args[@@]}" \
    --compile-only \
    --build-arg="${DAFNY_BENCHMARK:-dafny-benchmark}" \
    @{COMPILE_BUILD_ARGS}
  exit $?
fi
python3 -m verification \
  "${common_args[@@]}" \
  --full \
  --build-arg="${DAFNY_BENCHMARK:-dafny-benchmark}" \
  @{FULL_BUILD_ARGS}
