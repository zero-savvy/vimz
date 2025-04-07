#!/usr/bin/env bash

set -euo pipefail

cleanup() {
    if [ -n "${ANVIL_PID-}" ] && kill -0 "$ANVIL_PID" 2>/dev/null; then
        echo "Stopping Anvil node (PID $ANVIL_PID)..."
        kill "$ANVIL_PID"
    fi
}
trap cleanup EXIT

source_env_file() {
    if [ -f ".local.env" ]; then
        echo "Sourcing .local.env file..."
        set -a
        source .local.env
        set +a
    else
        echo "Warning: .local.env file not found!"
    fi
}

start_anvil() {
    echo "Starting Anvil node in the background..."
    anvil > anvil.log 2>&1 &
    ANVIL_PID=$!
    echo "Anvil node started with PID $ANVIL_PID"
}

run_scenario_script() {
    local script="$1"
    if [ ! -f "$script" ]; then
        echo "Error: Scenario script '$script' not found."
        exit 1
    fi
    echo "Running scenario: $script..."
    local script_dir
    script_dir=$(dirname "$script")
    local script_file
    script_file=$(basename "$script")
    # Change directory to the scenario's folder and ensure PYTHONPATH includes the parent directory
    pushd "$script_dir" > /dev/null
    PYTHONPATH=.. python3 "$script_file"
    popd > /dev/null
}

run_all_scenarios() {
    local found=0
    for script in scenarios/*.py; do
        if [ -f "$script" ]; then
            run_scenario_script "$script"
            found=1
        fi
    done
    if [ "$found" -eq 0 ]; then
        echo "No scenario scripts found."
    fi
}

main() {
    source_env_file
    start_anvil

    if [ $# -gt 0 ]; then
        run_scenario_script "$1"
    else
        echo "No scenario specified. Running all scenario scripts matching 'scenarios/*.py'..."
        run_all_scenarios
    fi

    echo "All scenarios completed successfully."
}

main "$@"
