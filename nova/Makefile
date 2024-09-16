ifeq ($(LIGHT_TEST),yes)
    FEATURES += --features light-test
else
    FEATURES +=
endif

.PHONY: help
help: # Show help for each of the Makefile recipes.
	@grep -E '^[a-zA-Z0-9 -]+:.*#'  Makefile | sort | while read -r l; do printf "\033[1;32m$$(echo $$l | cut -f 1 -d':')\033[00m:$$(echo $$l | cut -f 2- -d'#')\n"; done

.PHONY: blur
blur: # Run VIMz with the blur transformation.
	@cargo run --release $(FEATURES) -- \
		-f blur -w ../circuits/blur_step_js/blur_step.wasm \
		-o /home/piomiko/Desktop/vimz/blur_hd.json \
		-i ../samples/JSON/HD/transformation_blur.json \
		-c ../circuits/blur_step.r1cs -r HD

.PHONY: brightness
brightness: # Run VIMz with the brightness transformation.
	@cargo run --release $(FEATURES) -- \
		-f brightness -w ../circuits/brightness_step_js/brightness_step.wasm \
		-o /home/piomiko/Desktop/vimz/brightness_hd.json \
		-i ../samples/JSON/HD/transformation_brightness.json \
		-c ../circuits/brightness_step.r1cs -r HD

.PHONY: grayscale
grayscale: # Run VIMz with the grayscale transformation.
	@cargo run --release $(FEATURES) -- \
		-f grayscale -w ../circuits/grayscale_step_js/grayscale_step.wasm \
		-o /home/piomiko/Desktop/vimz/grayscale_hd.json \
		-i ../samples/JSON/HD/transformation_grayscale.json \
		-c ../circuits/grayscale_step.r1cs -r HD
