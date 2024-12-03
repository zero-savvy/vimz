.PHONY: help
help: # Show help for each of the Makefile recipes.
	@grep -E '^[a-zA-Z0-9 -]+:.*#'  Makefile | sort | while read -r l; do printf "\033[1;32m$$(echo $$l | cut -f 1 -d':')\033[00m:$$(echo $$l | cut -f 2- -d'#')\n"; done

########################################################################################################################
########################### INPUT DATA GENERATION ######################################################################
########################################################################################################################

INPUT_SOURCE = --image-path ./source_image/HD.png
INPUT_TARGET_DIR = ./input_data/
INPUT_TARGET = --output-dir $(INPUT_TARGET_DIR)

TRANSFORMATIONS = blur brightness contrast crop grayscale hash resize sharpness

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
