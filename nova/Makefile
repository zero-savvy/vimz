ifeq ($(LIGHT_TEST),yes)
    FEATURES += --features light-test
else
    FEATURES +=
endif

ifeq ($(backend),nova-snark)
    SUBDIR = nova_snark
else
    SUBDIR = sonobe
endif

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
	@cargo run --release $(FEATURES) -- \
 		-f $(TRANSFORMATION) -w ../circuits/$(SUBDIR)/$(TRANSFORMATION)_step_js/$(TRANSFORMATION)_step.wasm \
		-o ../$(TRANSFORMATION)_hd.json \
		-i ../samples/JSON/HD/transformation_$(TRANSFORMATION).json \
		-c ../circuits/$(SUBDIR)/$(TRANSFORMATION)_step.r1cs -r HD \
		-b $(backend)

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

.PHONY: grayscale
grayscale: # Run the grayscale transformation.
grayscale: TRANSFORMATION=grayscale
grayscale: run-transformation

.PHONY: hash
hash: # Run the hash transformation.
hash: TRANSFORMATION=hash
hash: run-transformation

.PHONY: sharpness
sharpness: # Run the sharpness transformation.
sharpness: TRANSFORMATION=sharpness
sharpness: run-transformation

.PHONY: all-transformations
all-transformations: # Run all transformations.
all-transformations: blur brightness contrast grayscale sharpness
