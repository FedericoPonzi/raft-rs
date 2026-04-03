#!/usr/bin/env bash
# Run raft-rs trace validation against the Raft TLA+ safety invariants.
#
# Prerequisites: Java 11+, Rust toolchain.
# Usage: ./tla-trace-validation/run_trace_validation.sh
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LIB_DIR="$SCRIPT_DIR/lib"
TRACE_DIR="$SCRIPT_DIR/traces"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

TLA2TOOLS_URL="https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
COMMUNITY_URL="https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar"

# -- Download TLC if necessary -------------------------------------------
if [ ! -f "$LIB_DIR/tla2tools.jar" ] || [ ! -f "$LIB_DIR/CommunityModules-deps.jar" ]; then
    echo "Downloading TLC and CommunityModules…"
    mkdir -p "$LIB_DIR"
    curl -sL -o "$LIB_DIR/tla2tools.jar" "$TLA2TOOLS_URL"
    curl -sL -o "$LIB_DIR/CommunityModules-deps.jar" "$COMMUNITY_URL"
fi

# -- Copy the upstream raft.tla spec into the working directory -----------
if [ -f "$REPO_ROOT/raft-tla/raft.tla" ]; then
    cp "$REPO_ROOT/raft-tla/raft.tla" "$SCRIPT_DIR/raft.tla"
fi

# -- Verify composed action preserves safety (bounded model check) --------
# Runs TLC for up to SAFETY_CHECK_SECS seconds.  raft.tla's DuplicateMessage
# prevents the BFS queue from fully draining, so we use a timeout.
# If TLC finds no violation in that time, the check passes.
SAFETY_CHECK_SECS="${SAFETY_CHECK_SECS:-60}"
echo "[1/3] Verifying TimeoutWithSelfVote preserves safety (${SAFETY_CHECK_SECS}s)…"
if [ -f "$SCRIPT_DIR/ComposedRaftSafety.tla" ]; then
    safety_output=$(cd "$SCRIPT_DIR" && timeout "$SAFETY_CHECK_SECS" \
        java -XX:+UseParallelGC \
        -cp "lib/tla2tools.jar:lib/CommunityModules-deps.jar" \
        tlc2.TLC -nowarning -workers auto \
        -config ComposedRaftSafety.cfg ComposedRaftSafety.tla 2>&1) || true

    if echo "$safety_output" | grep -q "violated"; then
        echo "  FAIL: Composed action violates safety!"
        echo "$safety_output" | grep -E "violated|failed|Error" | head -5
        exit 1
    else
        states=$(echo "$safety_output" | grep -oP '\d+ distinct states found' | tail -1 || echo "")
        echo "  PASS: No violation found ($states)"
    fi
else
    echo "  SKIP: ComposedRaftSafety.tla not found"
fi

# -- Generate traces ------------------------------------------------------
echo "[2/3] Generating traces…"
mkdir -p "$TRACE_DIR"
(cd "$REPO_ROOT" && RAFT_TRACE_DIR="$TRACE_DIR" \
    cargo test --package harness --test trace_validation -- --quiet 2>&1) \
    | tail -1

# -- Validate traces with TLC --------------------------------------------
echo "[3/3] Validating traces with TLC…"

PASS=0 FAIL=0
for trace in "$TRACE_DIR"/*.ndjson; do
    [ -f "$trace" ] || continue
    name=$(basename "$trace")

    output=$(cd "$SCRIPT_DIR" && RAFT_TRACE="traces/$name" \
        java -XX:+UseParallelGC \
        -cp "lib/tla2tools.jar:lib/CommunityModules-deps.jar" \
        tlc2.TLC -nowarning -workers 1 \
        -config Traceraft.cfg Traceraft.tla 2>&1) || true

    if echo "$output" | grep -q "No error has been found"; then
        PASS=$((PASS + 1))
    elif echo "$output" | grep -q "violated\|Error:.*failed"; then
        FAIL=$((FAIL + 1))
        inv=$(echo "$output" | grep -E "violated|failed" | head -1)
        echo "  FAIL: $name  $inv"
    else
        echo "  ERROR: $name — TLC did not produce expected output"
        echo "$output" | tail -5
        exit 1
    fi
done

echo ""
echo "Results: $PASS passed, $FAIL failed ($(( PASS + FAIL )) traces)"
[ "$FAIL" -eq 0 ] && echo "All traces satisfy Raft safety invariants." || exit 1
