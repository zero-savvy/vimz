#!/usr/bin/env bash

set -euo pipefail

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BOLD='\033[1m'
NC='\033[0m'  # No Color

cleanup() {
    if [ -n "${ANVIL_PID-}" ] && kill -0 "$ANVIL_PID" 2>/dev/null; then
        echo "Stopping Anvil node (PID $ANVIL_PID)..."
        kill "$ANVIL_PID"
    fi
}
trap cleanup EXIT

source_env_file() {
    if [ -f ".local.env" ]; then
        echo "Sourcing .local.env file and exporting variables..."
        set -a
        source .local.env
        set +a
    else
        echo -e "${YELLOW}Warning: .local.env file not found!${NC}"
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
        echo -e "${RED}Error: Scenario script '$script' not found.${NC}"
        exit 1
    fi
    local scenario_name
    scenario_name=$(basename "$script" .py)
    echo -e "${BOLD}Running scenario: ${scenario_name}...${NC}"

    pushd "$(dirname "$script")" > /dev/null
    PYTHONPATH=.. SCENARIO_NAME="${scenario_name}" python3 "$(basename "$script")"
    popd > /dev/null
}

run_all_scenarios() {
    local found=0
    for script in scenarios/*.py; do
        if [ "$(basename "$script")" = "__init__.py" ]; then
            continue
        fi
        if [ -f "$script" ]; then
            run_scenario_script "$script"
            echo -e "\n\n\n"
            found=1
        fi
    done
    if [ "$found" -eq 0 ]; then
        echo -e "${RED}No scenario scripts found.${NC}"
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

    echo -e "${GREEN}${BOLD}All scenarios completed successfully.${NC}${NC}"
}

main "$@"
