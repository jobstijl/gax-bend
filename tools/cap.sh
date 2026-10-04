#!/bin/sh
# Run a heavy job under the machine's agreed limits: 16G, no swap.
exec systemd-run --user --scope -q -p MemoryMax=16G -p MemorySwapMax=0 -- "$@"
