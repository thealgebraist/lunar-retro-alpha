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

ASSET_DIR := moon_base_assets
WASM_TARGET := game.wasm
WASM_B64 := game.wasm.base64

.PHONY: all build clean gensamples setup_tools setup_zig setup_ffmpeg

all: build

setup_tools: setup_zig setup_ffmpeg
	@if ! which $(PYTHON) >/dev/null 2>&1; then echo "Error: python3 not found."; exit 1; fi

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
	$(PYTHON) embed_wasm.py

$(WASM_TARGET): game.zig
	$(ZIG) build-exe game.zig -target wasm32-freestanding -rdynamic -O ReleaseSmall --name game -fno-entry

$(WASM_B64): $(WASM_TARGET)
	base64 < $(WASM_TARGET) > $(WASM_B64)

backstory_frames.json: gen_frames.py
	$(PYTHON) gen_frames.py > backstory_frames.json

gensamples: setup_tools
	$(PYTHON) generate_moon_base_sounds.py
	$(PYTHON) generate_intro_synth.py
	$(PYTHON) generate_backstory_audio.py
	$(PYTHON) generate_ending_synth.py
	$(PYTHON) generate_escape_pod_large.py
	$(PYTHON) generate_more_triggers.py
	$(PYTHON) generate_stable_audio.py
	$(PYTHON) normalize_samples.py
	$(PYTHON) convert_to_ogg.py

clean:
	rm -f $(WASM_TARGET) $(WASM_B64) game.wasm.o backstory_frames.json
	rm -rf $(ZIG_DIR) $(FFMPEG_DIR)
	find $(ASSET_DIR) -name "*.wav" -delete
	find $(ASSET_DIR) -name "*.ogg" -delete
