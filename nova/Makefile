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

.PHONY: blur
blur: # Run VIMz with the blur transformation.
	@cargo run --release $(FEATURES) -- \
		-f blur -w ../circuits/$(SUBDIR)/$(SUBDIR)_blur_step_js/$(SUBDIR)_blur_step.wasm \
		-o ../blur_hd.json \
		-i ../samples/JSON/HD/transformation_blur.json \
		-c ../circuits/$(SUBDIR)/$(SUBDIR)_blur_step.r1cs -r HD \
		-b $(backend)

.PHONY: brightness
brightness: # Run VIMz with the brightness transformation.
	@cargo run --release $(FEATURES) -- \
		-f brightness -w ../circuits/$(SUBDIR)/$(SUBDIR)_brightness_step_js/$(SUBDIR)_brightness_step.wasm \
		-o ../brightness_hd.json \
		-i ../samples/JSON/HD/transformation_brightness.json \
		-c ../circuits/$(SUBDIR)/$(SUBDIR)_brightness_step.r1cs -r HD \
		-b $(backend)

.PHONY: grayscale
grayscale: # Run VIMz with the grayscale transformation.
	@cargo run --release $(FEATURES) -- \
		-f grayscale -w ../circuits/$(SUBDIR)/$(SUBDIR)_grayscale_step_js/$(SUBDIR)_grayscale_step.wasm \
		-o ../grayscale_hd.json \
		-i ../samples/JSON/HD/transformation_grayscale.json \
		-c ../circuits/$(SUBDIR)/$(SUBDIR)_grayscale_step.r1cs -r HD \
		-b $(backend)
