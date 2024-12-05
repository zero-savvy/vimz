.PHONY: help
help: # Show help for each of the Makefile recipes.
	@grep -E '^[a-zA-Z0-9 -]+:.*#'  Makefile | sort | while read -r l; do printf "\033[1;32m$$(echo $$l | cut -f 1 -d':')\033[00m:$$(echo $$l | cut -f 2- -d'#')\n"; done

TRANSFORMATIONS = blur brightness contrast crop grayscale hash resize sharpness

########################################################################################################################
########################### INPUT DATA GENERATION ######################################################################
########################################################################################################################

INPUT_SOURCE = --image-path ./source_image/HD.png
INPUT_TARGET_DIR = ./input_data/
INPUT_TARGET = --output-dir $(INPUT_TARGET_DIR)

EXTRA_ARGS_brightness = --factor 1.4
EXTRA_ARGS_contrast = --factor 1.4
EXTRA_ARGS_crop = --x 200 --y 100 --crop-size HD
EXTRA_ARGS_resize = --resize-option "HD to SD"

.PHONY: generate-input-data
generate-input-data: # Prepare input data for every supported transformation.
generate-input-data: $(patsubst %, $(INPUT_TARGET_DIR)%.json, $(TRANSFORMATIONS))

$(INPUT_TARGET_DIR)%.json:
	@mkdir -p $(INPUT_TARGET_DIR)
	@python3 image_editor/main.py $* $(INPUT_SOURCE) $(INPUT_TARGET) $(EXTRA_ARGS_$*)

########################################################################################################################
########################### CIRCUIT COMPILATION ########################################################################
########################################################################################################################

BACKEND = sonobe nova_snark

COMPILATION_ARTIFACTS := $(foreach backend,$(BACKEND),$(foreach trans,$(TRANSFORMATIONS), \
    circuits/$(backend)/$(trans)_step.r1cs \
    circuits/$(backend)/$(trans)_step_js/$(trans)_step.wasm \
    circuits/$(backend)/$(trans)_step.compile_log))

.PHONY: build-circuits
build-circuits: $(COMPILATION_ARTIFACTS)

circuits/%_step.r1cs circuits/%_step_js/%_step.wasm circuits/%_step.compile_log: circuits/%_step.circom
	@backend=$(word 1,$(subst /, ,$*)); \
	transformation=$(word 2,$(subst /, ,$*)); \
	transformation_file=$$transformation\_step.circom; \
	./circuits/build_circuits.sh circuits/$$backend $$transformation_file

.PHONY: report-circuit-parameters
report-circuit-parameters: build-circuits
	@python3 analysis_utils/analyze_circuits.py sonobe > /dev/null
	@python3 analysis_utils/analyze_circuits.py nova_snark > /dev/null

.PHONY: clean-circuits
clean-circuits:
	@cd circuits && ./clear_builds.sh sonobe && ./clear_builds.sh nova_snark

########################################################################################################################
########################### BENCHMARKING ###############################################################################
########################################################################################################################

RUN_ARTIFACTS := $(foreach trans,$(TRANSFORMATIONS), runs/nova_snark/$(trans).out)

.PHONY: run-nova-snark-benchmarks
run-nova-snark-benchmarks: generate-input-data build-circuits $(RUN_ARTIFACTS)

runs/nova_snark/%.out:
	@mkdir -p runs/nova_snark
	@cd vimz/ && $(MAKE) $* BACKEND=nova-snark DEMO=yes > ../$@
