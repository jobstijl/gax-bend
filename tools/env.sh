# Source me: puts bend and the project's clang on PATH, no telemetry.
root=$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)
export PATH="$HOME/.bend/bin:$root/.vendor/bin:$PATH"
export CC="$root/.vendor/bin/clang"
export BEND_NO_TELEMETRY=1
