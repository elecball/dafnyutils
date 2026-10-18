#!/usr/bin/env bash
set -euo pipefail
individual_failure() {
  printf '%s\n' "$1" >&2
  printf 'DAFNY_TARGET_VERIFICATION_OUTCOME=infrastructure_failure phase=selection\n'
  exit 1
}
if [[ $# -eq 1 && "$1" == --list ]]; then
  :
elif [[ $# -eq 4 && "$1" == --source && "$3" == --symbol ]]; then
  :
else
  individual_failure 'Usage: verify-target.sh --list | --source PATH --symbol FULL_NAME'
fi
script_path="${BASH_SOURCE[0]}"
case "$script_path" in
  */*) script_dir="${script_path%/*}" ;;
  *) script_dir="." ;;
esac
script_dir="$(cd "$script_dir" && pwd)" || individual_failure 'Cannot locate support directory'
workspace_root="${EVAL_WORKSPACE_DIR:-$(cd "$script_dir/@{SCRIPT_PARENT}" && pwd)}"
cd "$workspace_root" || individual_failure 'Cannot locate workspace'
@{BUILD_ENVIRONMENT}
command -v python3 >/dev/null 2>&1 || individual_failure 'Python runtime is unavailable'
python3 -m verification \
  --workspace-root "$workspace_root" \
  --utility-root @{UTILITY_ROOT} \
  --manifest "$script_dir/entry_contract.json" \
  --dafny "${DAFNY_BENCHMARK:-dafny-benchmark}" \
  --individual "$@@"
