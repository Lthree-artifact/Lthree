#!/usr/bin/env bash
set -u

# Run `lake env lean` for every .lean file under SSA/oracle.
# Usage:
#   ./run_oracle_lake_env_lean.sh
#   ./run_oracle_lake_env_lean.sh /path/to/oracle

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$SCRIPT_DIR"
ORACLE_DIR="${1:-$REPO_ROOT/SSA/oracle}"

if [[ ! -d "$ORACLE_DIR" ]]; then
  echo "Error: directory not found: $ORACLE_DIR" >&2
  exit 2
fi

cd "$REPO_ROOT" || exit 2

fail_count=0
total_count=0

while IFS= read -r file; do
  total_count=$((total_count + 1))
  echo "[$total_count] lake env lean $file"
  if ! lake env lean "$file"; then
    echo "FAILED: $file" >&2
    fail_count=$((fail_count + 1))
  fi
done < <(find "$ORACLE_DIR" -type f -name '*.lean' | sort)

echo
echo "Done. total=$total_count failed=$fail_count"

if [[ "$fail_count" -ne 0 ]]; then
  exit 1
fi

