import torch
import os
import sys
try:
    from diffusers import HunyuanVideoPipeline
except ImportError:
    print("HunyuanVideoPipeline not found in diffusers. Please upgrade diffusers to latest version.")
    sys.exit(1)

from diffusers.utils import export_to_video
from typing import Final, List
import numpy as np

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Constants
DEVICE: Final[str] = "cuda" if torch.cuda.is_available() else "cpu"
# Using HunyuanVideo 1.5 720p model - perfect for H100
MODEL_ID: Final[str] = "hunyuanvideo-community/HunyuanVideo-1.5-Diffusers-720p_t2v"
PROMPT: Final[str] = (
    "A cinematic, high-detail wide shot of a derelict 1950s-style moon base. "
    "The base consists of rusted chrome domes and retro-futuristic antennas. "
    "The camera flies past slowly from a distance. Through the thick glass portholes, "
    "tiny silhouettes of people are visible moving inside. "
    "Lunar dust kicks up in the foreground. High contrast, 35mm film grain, sci-fi noir."
)

def build_pipeline(model_id: str) -> HunyuanVideoPipeline:
    """
    Initializes the HunyuanVideo pipeline.
    """
    print(f"Loading {model_id} onto {DEVICE}...")
    # H100 excels at bfloat16
    dtype = torch.bfloat16 if DEVICE == "cuda" else torch.float32
    
    pipe = HunyuanVideoPipeline.from_pretrained(
        model_id,
        torch_dtype=dtype
    )

    pipe.to(DEVICE)
    # pipe.vae.enable_tiling() # Can be enabled for even higher res if needed
        
    return pipe

def generate_video(
    pipe: HunyuanVideoPipeline,
    prompt: str,
    output_path: str,
    seed: int = 42
) -> str:
    """
    Generates a high-quality video using HunyuanVideo 1.5.
    """
    generator = torch.Generator(device=DEVICE).manual_seed(seed)

    print(f"Starting generation for prompt: {prompt}")
    
    # HunyuanVideo 1.5 settings
    # Typical num_frames: 31, 61, etc.
    # width/height for 720p: 1280x720 or similar
    output = pipe(
        prompt=prompt,
        num_frames=61, # ~5 seconds at 10fps or ~2.5s at 24fps
        width=1280,
        height=720,
        num_inference_steps=50,
        guidance_scale=6.0,
        generator=generator,
    ).frames[0]

    print(f"Exporting video to {output_path}...")
    export_to_video(output, output_path, fps=24)
    
    # Save a binary backup
    backup_path = output_path.replace(".mp4", ".bin")
    torch.save(output, backup_path)
    print(f"Binary backup saved to: {backup_path}")

    return output_path

def main() -> None:
    output_filename = "moon_base_cinematic_hq.mp4"

    if DEVICE != "cuda":
        print("Warning: CUDA not detected. This model is extremely heavy and requires a GPU (ideally H100).")

    try:
        pipeline = build_pipeline(MODEL_ID)
        print("Starting generation. This will take full advantage of the GPU...")
        result_path = generate_video(pipeline, PROMPT, output_filename)
        print(f"Process complete. Video: {result_path}")
    except Exception as e:
        print(f"Error during video generation: {e}")

if __name__ == "__main__":
    main()
