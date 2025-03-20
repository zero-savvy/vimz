BUILD_DIR = out
CONTRACTS_SRC_DIR = contracts

.PHONY: help
help: # Show help for each of the Makefile recipes.
	@grep -E '^[a-zA-Z0-9 -]+:.*#'  Makefile | sort | while read -r l; do printf "\033[1;32m$$(echo $$l | cut -f 1 -d':')\033[00m:$$(echo $$l | cut -f 2- -d'#')\n"; done

####################################################################################################
################################# CONTRACTS ########################################################
####################################################################################################

.PHONY: compile-contracts
compile-contracts: # Compile all contracts using Foundry
	@forge build

.PHONY: serve-contract-docs
serve-contract-docs: # Serve documentation locally using MkDocs
	@forge doc --serve

.PHONY: format-contracts
format-contracts: # Format Solidity code
	@forge fmt

