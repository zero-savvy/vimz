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
	@forge doc --serve --open -i

.PHONY: format-contracts
format-contracts: # Format Solidity code
	@forge fmt

####################################################################################################
################################# PYTHON ###########################################################
####################################################################################################

.PHONY: lint-python
lint-python: # Format and lint Python code
	@black scenarios/ vimz_marketplace_sdk/
	@isort scenarios/ vimz_marketplace_sdk/
