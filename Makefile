# Makefile for Lunar Retro-Alpha

ZIG_VERSION := 0.13.0
ZIG_URL := https://ziglang.org/download/$(ZIG_VERSION)/zig-linux-x86_64-$(ZIG_VERSION).tar.xz

# Detect if zig is in the path, otherwise use a local one
ZIG := $(shell which zig 2>/dev/null || echo ./zig-linux-x86_64-$(ZIG_VERSION)/zig)

PYTHON := python3
FFMPEG := ffmpeg

ASSET_DIR := moon_base_assets
WASM_TARGET := game.wasm
WASM_B64 := game.wasm.base64

.PHONY: all build clean gensamples setup_zig

all: build

setup_zig:
	@if [ ! -x "$(ZIG)" ]; then \
		echo "Zig not found. Downloading $(ZIG_VERSION)..."; \
		curl -L $(ZIG_URL) | tar -xJ; \
	fi

build: setup_zig $(WASM_TARGET) $(WASM_B64) backstory_frames.json
	$(PYTHON) embed_wasm.py

$(WASM_TARGET): game.zig
	$(ZIG) build-exe game.zig -target wasm32-freestanding -rdynamic -O ReleaseSmall --name game -fno-entry

$(WASM_B64): $(WASM_TARGET)
	base64 < $(WASM_TARGET) > $(WASM_B64)

backstory_frames.json: gen_frames.py
	$(PYTHON) gen_frames.py > backstory_frames.json

gensamples:
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
	rm -rf zig-linux-x86_64-$(ZIG_VERSION)
	find $(ASSET_DIR) -name "*.wav" -delete
	find $(ASSET_DIR) -name "*.ogg" -delete
