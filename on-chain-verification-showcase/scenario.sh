#!/usr/bin/env bash

set -eou pipefail

########################################################################################################################
#### VARIABLES #########################################################################################################
########################################################################################################################
RPC_URL="http://localhost:8545"                                                     # Default Anvil RPC URL

DEPLOYER_KEY="0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"   # Anvil's endowed account 1
CHALLENGER_KEY="0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d" # Anvil's endowed account 2
SUBMITTER_KEY="0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a"  # Anvil's endowed account 3

REWARD=1000000000000000000                                                          # 1 ETH for solving challenge
BLUR_CHALLENGE_ID=0                                                                 # Blur variant ID

########################################################################################################################
#### LOGGING ###########################################################################################################
########################################################################################################################
get_timestamp() {
  date +'%Y-%m-%d %H:%M:%S'
}

log_progress() {
  bold=$(tput bold)
  normal=$(tput sgr0)
  echo "[$(get_timestamp)] ${bold}${1}${normal}"
}

########################################################################################################################
##### ENVIRONMENT ######################################################################################################
########################################################################################################################
prepare_env() {
  ./check-env.sh > /dev/null
  npm install &>> /dev/null
  log_progress "✅ Checked requirements and installing dependencies"
}

########################################################################################################################
##### ANVIL NODE #######################################################################################################
########################################################################################################################
stop_node() {
  anvil_pid=$(pgrep -f 'anvil' || true)
  if [ -n "$anvil_pid" ]; then
    kill "${anvil_pid}"
    log_progress "✅ Stopped running anvil node"
  fi
}

start_node() {
  stop_node
  anvil &>> /dev/null &
  sleep 0.5 # Wait for the node to start, sometimes other commands connect too fast.
  log_progress "✅ Anvil node started"
}

####################################################################################################
#### CONTRACTS #####################################################################################
####################################################################################################
deploy_contracts() {
  forge script Deploy.s.sol --private-key "$DEPLOYER_KEY" --rpc-url "$RPC_URL" --broadcast &>> /dev/null
  CONTRACT_ADDRESS=$(cat broadcast/Deploy.s.sol/31337/run-latest.json | jq -r '.transactions[2].contractAddress')
  export CONTRACT_ADDRESS
  log_progress "✅ Contracts deployed"
}

########################################################################################################################
##### CLEANUP ##########################################################################################################
########################################################################################################################
remove_artifacts() {
  rm -f "challenge.png" "blur.json"
}

cleanup() {
  if [[ "$?" -ne 0 ]]; then
    echo "❌ SCENARIO FAILED!"
  else
    log_progress "✅ Scenario successfully run"
  fi

  remove_artifacts
  stop_node
}

trap cleanup EXIT SIGINT SIGTERM

########################################################################################################################
##### CHALLENGER #######################################################################################################
########################################################################################################################
upload_challenge() {
  CHALLENGE_ID=$(ipfs add "../source_image/HD.png" 2> /dev/null | awk '{print $2}')
  export CHALLENGE_ID
  log_progress "  ✅ Challenge uploaded to IPFS with ID: $CHALLENGE_ID"
}

create_challenge_on_chain() {
  cast send \
    --private-key "$CHALLENGER_KEY" \
    --rpc-url "$RPC_URL" \
    --value "$REWARD" \
    "$CONTRACT_ADDRESS" \
    "createChallenge(string memory, uint8)" "$CHALLENGE_ID" "$BLUR_CHALLENGE_ID" \
    &>> /dev/null
  log_progress "  ✅ Challenge created"
}

create_challenge() {
  log_progress "🚀 Creating challenge"
  upload_challenge
  create_challenge_on_chain
}

########################################################################################################################
##### SUBMITTER ########################################################################################################
########################################################################################################################
read_challenge_id() {
  FOUND_CHALLENGE_ID=$(cast call \
    --rpc-url "$RPC_URL" \
    "$CONTRACT_ADDRESS" "imageId(uint256)(string)" "0" \
    2> /dev/null | tr -d '"')
  export FOUND_CHALLENGE_ID
  log_progress "  ✅ Found challenge ID: $FOUND_CHALLENGE_ID"
}

fetch_challenge() {
  ipfs cat "$FOUND_CHALLENGE_ID" > "challenge.png"
  log_progress "  ✅ Challenge fetched from IPFS"
}

process_image() {
  if [ ! -f "./blur.json" ]; then
    image-editor --image-path challenge.png --output-dir ./ blur &>> /dev/null
    log_progress "  ✅ Image processed"
  else
    log_progress "  ❕ Found processed image - have you cleared artifacts from previous runs?"
  fi
}

upload_solution() {
  SOLUTION_ID=$(ipfs add "blur.json" 2> /dev/null | awk '{print $2}')
  export SOLUTION_ID
  log_progress "  ✅ Solution uploaded to IPFS with ID: $SOLUTION_ID"
}

compute_proof() {
  echo -e "\n\n"
  pushd ../vimz/ &>> /dev/null

  cargo run --release --features light-test --bin vimz -- \
    -f blur -w ../circuits/sonobe/blur_step_js/blur_step.wasm \
    -i ../on-chain-verification-showcase/blur.json \
    -c ../circuits/sonobe/blur_step.r1cs \
    -r HD -b sonobe --demo \
    -o ../calldata/proof

  echo -e "\n\n"
  popd &>> /dev/null

  log_progress "  ✅ Proof computed"
}

send_solution() {
  SELECTOR="cf2c8294"
  PROOF=$(xxd -p -c 10000 < "../calldata/proof" | cut -c 9-)
  SUFFIX=$(cast abi-encode "f(uint256,string memory)" "0" "$SOLUTION_ID" | cut -c 3-)

  cast send \
    "$CONTRACT_ADDRESS" \
    0x"${SELECTOR}${PROOF}${SUFFIX}" \
    --private-key "$SUBMITTER_KEY" \
    --rpc-url "$RPC_URL" \
    &>> /dev/null
  log_progress "  ✅ Solution submitted"
}

solve_challenge() {
  log_progress "🚀 Solving challenge"
  read_challenge_id
  fetch_challenge
  process_image
  upload_solution
  compute_proof
  send_solution
}

########################################################################################################################
##### SCENARIO #########################################################################################################
########################################################################################################################
run() {
  prepare_env

  start_node
  deploy_contracts

  create_challenge
  solve_challenge
}

run
