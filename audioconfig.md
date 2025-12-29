# Audio Generation Configuration

This document saves the working configuration used to generate AI audio assets for the Lunar Retro-Alpha project.

## Environment

- **Python Version**: 3.11 (via `/opt/homebrew/bin/python3.11`)
- **Library Location**: `./local_libs` (local installation to avoid system conflicts)

## Libraries

The following specific versions were required to ensure compatibility between `AudioLDM2` and `Bark` in this environment:

- **diffusers**: `0.25.0`
- **transformers**: `4.35.2`
- **accelerate**: `0.25.0`
- **huggingface_hub**: `0.19.4`
- **numpy**: `1.26.4` (< 2.0)
- **scipy**: `1.16.3`
- **safetensors**: `0.7.0`
- **torch**: `2.9.1` (Apple Silicon / MPS compatible build)

## Models

### 1. Suno/Bark (Voices)
- **Model ID**: `suno/bark-small`
- **Task**: Generating character dialogue, tape logs, and reactions.
- **Cache Location**: `~/.cache/huggingface/hub/models--suno--bark-small`

### 2. CVSSP/AudioLDM2 (Sound Effects)
- **Model ID**: `cvssp/audioldm2-large`
- **Task**: Generating soundscapes, ambient noise, machinery (crusher, elevator), and rumble effects.
- **Cache Location**: `~/.cache/huggingface/hub/models--cvssp--audioldm2-large`

## Usage

To regenerate assets using this config, run:

```bash
/opt/homebrew/bin/python3.11 regenerate_all_assets.py
```

Ensure `regenerate_all_assets.py` inserts `local_libs` at the beginning of `sys.path`:

```python
import sys
import os
sys.path.insert(0, os.path.abspath("local_libs"))
```
