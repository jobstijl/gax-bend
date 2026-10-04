# Source me (after tools/env.sh): the upstream hip branch's bend (2.0.24, Bun)
# with ROCm 7.2.4 unpacked in .vendor/rocm; `bend-hip` replaces `bend`.
root=$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)
export ROCM_PATH="$root/.vendor/rocm/opt/rocm"
export LD_LIBRARY_PATH="$ROCM_PATH/lib:$root/.vendor/rocm/usr/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
bend-hip() { "$root/.vendor/bun/bun-linux-x64/bun" "$root/.vendor/bend-hip/bend2/main.ts" "$@"; }
