.PHONY: help
help: # Show help for each of the Makefile recipes.
	@grep -E '^[a-zA-Z0-9 -]+:.*#'  Makefile | sort | while read -r l; do printf "\033[1;32m$$(echo $$l | cut -f 1 -d':')\033[00m:$$(echo $$l | cut -f 2- -d'#')\n"; done

INPUT_SOURCE = --image-path ./samples/HD.png
INPUT_TARGET = --output-dir ./samples/JSON/HD/

.PHONY: generate-input-data
generate-input-data: # Prepare input data for every supported transformation.
	@python3 image_editor/main.py blur       $(INPUT_SOURCE) $(INPUT_TARGET)
	@python3 image_editor/main.py brightness $(INPUT_SOURCE) $(INPUT_TARGET) --factor 1.4
	@python3 image_editor/main.py contrast   $(INPUT_SOURCE) $(INPUT_TARGET) --factor 1.4
	@python3 image_editor/main.py crop       $(INPUT_SOURCE) $(INPUT_TARGET) --x 200 --y 100 --crop-size HD
	@python3 image_editor/main.py grayscale  $(INPUT_SOURCE) $(INPUT_TARGET)
	@python3 image_editor/main.py resize     $(INPUT_SOURCE) $(INPUT_TARGET) --resize-option "HD to SD"
	@python3 image_editor/main.py sharpness  $(INPUT_SOURCE) $(INPUT_TARGET)
