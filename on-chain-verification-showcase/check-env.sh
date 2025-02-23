#!/usr/bin/env bash

# List of required tools and installation hints
declare -A requirements=(
    ["image-editor"]="Install it using 'make build-aux-tools' from the repo root or 'pip install pyvimz'"
    ["image-hasher"]="Install it using 'make build-aux-tools' from the repo root or 'pip install pyvimz'"
    ["jq"]="Install it using: sudo apt install jq, sudo yum install jq, or brew install jq"
    ["xxd"]="Install it using: sudo apt install xxd, sudo yum install vim-common, or brew install vim"
    ["cut"]="This is part of coreutils, install it using: sudo apt install coreutils, sudo yum install coreutils, or brew install coreutils"
    ["python3"]="Install it using: sudo apt install python3, sudo yum install python3, or brew install python3"
    ["pip"]="Ensure Python is installed, then install pip using: sudo apt install python3-pip, sudo yum install python3-pip, or brew install python3-pip"
    ["anvil"]="Install it using instructions from https://book.getfoundry.sh/getting-started/installation"
    ["forge"]="Install it using instructions from https://book.getfoundry.sh/getting-started/installation"
    ["cast"]="Install it using instructions from https://book.getfoundry.sh/getting-started/installation"
    ["solc"]="Install it using instructions from https://docs.soliditylang.org/en/latest/installing-solidity.html"
    ["ipfs"]="Install it using instructions from https://docs.ipfs.tech/install/command-line/#install-official-binary-distributions"
    ["cargo"]="Install it using instructions from https://www.rust-lang.org/tools/install"
    ["npm"]="Install it using instructions from https://docs.npmjs.com/downloading-and-installing-node-js-and-npm"
)

missing_tools=()

echo "Checking required tools..."
for tool in "${!requirements[@]}"; do
    if ! command -v "$tool" &>/dev/null; then
        missing_tools+=("$tool")
    fi
done

if [ ${#missing_tools[@]} -eq 0 ]; then
    echo "✅ All required tools are installed!"
else
    echo "⚠️ The following tools are missing:"
    for tool in "${missing_tools[@]}"; do
        echo "  ❌ $tool - ${requirements[$tool]}"
    done
    exit 1
fi
