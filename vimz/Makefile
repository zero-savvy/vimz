ifeq ($(LIGHT_TEST),yes)
    FEATURES += --features light-test
else
    FEATURES +=
endif

ifeq ($(BACKEND),nova-snark)
    SUBDIR = nova_snark
else
    SUBDIR = sonobe
endif

ifeq ($(DEMO),yes)
	DEMO_FLAG := --demo
else
	DEMO_FLAG :=
endif

FRONTEND ?=
FRONTEND_ARG := $(if $(FRONTEND),--frontend $(FRONTEND),)

.PHONY: help
help: # Show help for each of the Makefile recipes.
	@grep -E '^[a-zA-Z0-9 -]+:.*#'  Makefile | sort | while read -r l; do printf "\033[1;32m$$(echo $$l | cut -f 1 -d':')\033[00m:$$(echo $$l | cut -f 2- -d'#')\n"; done

.PHONY: lint
lint: # Run the linter.
	@cargo +nightly fmt --all
	@cargo clippy --release

.PHONY: run-transformation
run-transformation: # Run a given transformation
run-transformation:
	@cargo run --release $(FEATURES) --bin vimz -- \
 		-f $(TRANSFORMATION) -w ../circuits/$(SUBDIR)/$(TRANSFORMATION)_step_js/$(TRANSFORMATION)_step.wasm \
		-i ../input_data/$(TRANSFORMATION).json \
		-c ../circuits/$(SUBDIR)/$(TRANSFORMATION)_step.r1cs -r HD \
		-b $(BACKEND) $(FRONTEND_ARG) $(DEMO_FLAG) -o ../calldata/$(TRANSFORMATION).bytes \
		--source-image ../source_image/HD.png --target-image ../input_data/$(TRANSFORMATION).png \

.PHONY: blur
blur: # Run the blur transformation.
blur: TRANSFORMATION=blur
blur: run-transformation

.PHONY: brightness
brightness: # Run the brightness transformation.
brightness: TRANSFORMATION=brightness
brightness: run-transformation

.PHONY: contrast
contrast: # Run the contrast transformation.
contrast: TRANSFORMATION=contrast
contrast: run-transformation

.PHONY: crop
crop: # Run the crop transformation.
crop: TRANSFORMATION=crop
crop: run-transformation

.PHONY: grayscale
grayscale: # Run the grayscale transformation.
grayscale: TRANSFORMATION=grayscale
grayscale: run-transformation

.PHONY: hash
hash: # Run the hash transformation.
hash: TRANSFORMATION=hash
hash: run-transformation

.PHONY: redact
redact: # Run the redact transformation.
redact: TRANSFORMATION=redact
redact: run-transformation

.PHONY: resize
resize: # Run the resize transformation.
resize: TRANSFORMATION=resize
resize: run-transformation

.PHONY: sharpness
sharpness: # Run the sharpness transformation.
sharpness: TRANSFORMATION=sharpness
sharpness: run-transformation

.PHONY: all-transformations
all-transformations: # Run all transformations.
all-transformations:
	@$(MAKE) blur
	@$(MAKE) brightness
	@$(MAKE) contrast
	@$(MAKE) crop
	@$(MAKE) grayscale
	@$(MAKE) hash
	@$(MAKE) redact
	@$(MAKE) resize
	@$(MAKE) sharpness


.PHONY: generate-contract
generate-contract: # Generate verifier contract
generate-contract:
	@cargo run --release $(FEATURES) --bin generate-verifier-contract -- \
 		-f $(TRANSFORMATION) -w ../circuits/sonobe/$(TRANSFORMATION)_step_js/$(TRANSFORMATION)_step.wasm \
		-i ../input_data/$(TRANSFORMATION).json -o ../contracts/ \
		-c ../circuits/sonobe/$(TRANSFORMATION)_step.r1cs -r HD \
		-b sonobe --demo

.PHONY: generate-verifier-contracts
generate-verifier-contracts: # Generate all verifier contracts
generate-verifier-contracts:
	@$(MAKE) generate-contract TRANSFORMATION=blur
	@$(MAKE) generate-contract TRANSFORMATION=brightness
	@$(MAKE) generate-contract TRANSFORMATION=contrast
	@$(MAKE) generate-contract TRANSFORMATION=crop
	@$(MAKE) generate-contract TRANSFORMATION=grayscale
	@$(MAKE) generate-contract TRANSFORMATION=hash
	@$(MAKE) generate-contract TRANSFORMATION=redact
	@$(MAKE) generate-contract TRANSFORMATION=resize
	@$(MAKE) generate-contract TRANSFORMATION=sharpness
