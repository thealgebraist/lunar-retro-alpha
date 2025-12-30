# Makefile for Lunar Retro-Alpha

ZIG_VERSION := 0.13.0
ZIG_URL := https://ziglang.org/download/$(ZIG_VERSION)/zig-linux-x86_64-$(ZIG_VERSION).tar.xz
ZIG_DIR := zig-linux-x86_64-$(ZIG_VERSION)

FFMPEG_URL := https://johnvansickle.com/ffmpeg/releases/ffmpeg-release-amd64-static.tar.xz
FFMPEG_DIR := ffmpeg-static

# Detect tools in path or local directories
ZIG := $(shell which zig 2>/dev/null || echo ./$(ZIG_DIR)/zig)
FFMPEG := $(shell which ffmpeg 2>/dev/null || echo ./$(FFMPEG_DIR)/ffmpeg)
PYTHON := python3
VENV_DIR := .venv
VENV_PYTHON := $(VENV_DIR)/bin/python3

ASSET_DIR := moon_base_assets
WASM_TARGET := game.wasm
WASM_B64 := game.wasm.base64

.PHONY: all build clean gensamples genimages genvideo genhistory setup_tools setup_zig setup_ffmpeg setup_python

all: build

setup_tools: setup_zig setup_ffmpeg setup_python
	@if ! which $(PYTHON) >/dev/null 2>&1; then echo "Error: python3 not found."; exit 1; fi

setup_python:
	@if [ ! -d "$(VENV_DIR)" ]; then \
		echo "Creating virtual environment..."; \
		$(PYTHON) -m venv $(VENV_DIR); \
	fi
	@echo "Installing/Checking Python dependencies in $(VENV_DIR)..."
	@$(VENV_PYTHON) -m pip install --upgrade pip
	@$(VENV_PYTHON) -m pip install \
		"torch" \
		"torchvision" \
		"torchaudio" \
		"diffusers>=0.32.0" \
		"transformers>=4.44.0" \
		"accelerate>=0.34.2" \
		"huggingface-hub<1.0" \
		"tokenizers>=0.22.0,<=0.23.0" \
		"scipy>=1.16.0" \
		"numpy<2.3.0" \
		"pydub" \
		"soundfile" \
		"opencv-python" \
		"moviepy" \
		"tangoflux" \
		"datasets" \
		"google-genai" \
		"runwayml"

setup_zig:
	@if [ ! -x "$(ZIG)" ]; then \
		echo "Zig not found. Downloading $(ZIG_VERSION)..."; \
		curl -L $(ZIG_URL) | tar -xJ; \
	fi

setup_ffmpeg:
	@if [ ! -x "$(FFMPEG)" ]; then \
		echo "FFmpeg not found. Downloading static build..."; \
		mkdir -p $(FFMPEG_DIR); \
		curl -L $(FFMPEG_URL) | tar -xJ -C $(FFMPEG_DIR) --strip-components=1; \
	fi

build: setup_tools $(WASM_TARGET) $(WASM_B64) backstory_frames.json
	$(VENV_PYTHON) embed_wasm.py

$(WASM_TARGET): game.zig
	$(ZIG) build-exe game.zig -target wasm32-freestanding -rdynamic -O ReleaseSmall --name game -fno-entry

$(WASM_B64): $(WASM_TARGET)
	base64 < $(WASM_TARGET) > $(WASM_B64)

backstory_frames.json: gen_frames.py
	$(VENV_PYTHON) gen_frames.py > backstory_frames.json

gensamples: setup_tools
	$(VENV_PYTHON) generate_all.py

genimages: setup_tools
	$(VENV_PYTHON) generate_images.py

genvideo: setup_tools
	$(VENV_PYTHON) genvideo.py

genhistory: setup_tools
	$(VENV_PYTHON) generate_history_tapes.py

clean:
	rm -f $(WASM_TARGET) $(WASM_B64) game.wasm.o backstory_frames.json
	rm -rf $(ZIG_DIR) $(FFMPEG_DIR) $(VENV_DIR)
	find $(ASSET_DIR) -name "*.wav" -delete
	find $(ASSET_DIR) -name "*.ogg" -delete
