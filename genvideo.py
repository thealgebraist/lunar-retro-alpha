import torch
import os
import sys
try:
    from diffusers import WanPipeline
except ImportError:
    print("WanPipeline not found in diffusers. Please upgrade diffusers to latest version.")
    sys.exit(1)

from diffusers.utils import export_to_video
from typing import Final, List
import numpy as np

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Constants
DEVICE: Final[str] = "cuda" if torch.cuda.is_available() else "cpu"
MODEL_ID: Final[str] = "Wan-AI/Wan2.1-T2V-1.3B-Diffusers"
PROMPT: Final[str] = (
    "A cinematic, high-detail wide shot of a derelict 1950s-style moon base. "
    "The base consists of rusted chrome domes and retro-futuristic antennas. "
    "The camera flies past slowly from a distance. Through the thick glass portholes, "
    "tiny silhouettes of people are visible moving inside. "
    "Lunar dust kicks up in the foreground. High contrast, 35mm film grain, sci-fi noir."
)

def build_pipeline(model_id: str) -> WanPipeline:
    """
    Initializes the Wan2.1 pipeline.
    """
    print(f"Loading {model_id} onto {DEVICE}...")
    # Wan2.1 works best with bfloat16
    dtype = torch.bfloat16 if DEVICE == "cuda" else torch.float32
    
    pipe = WanPipeline.from_pretrained(
        model_id,
        torch_dtype=dtype
    )

    if DEVICE == "cuda":
        pipe.enable_model_cpu_offload()
    else:
        pipe.to(DEVICE)
        
    return pipe

def generate_video(
    pipe: WanPipeline,
    prompt: str,
    output_path: str,
    seed: int = 42
) -> str:
    """
    Generates a high-quality video using Wan2.1 1.3B.
    """
    generator = torch.Generator(device=DEVICE).manual_seed(seed)

    print(f"Starting generation for prompt: {prompt}")
    
    # Wan2.1 1.3B settings
    # 480P is recommended for this model (832x480)
    output = pipe(
        prompt=prompt,
        negative_prompt="low quality, worst quality, deformed, distorted, grainy, noise, blurry",
        num_frames=81, # 81 frames for ~5 seconds at 16fps
        width=832,
        height=480,
        num_inference_steps=50,
        guidance_scale=5.0,
        generator=generator,
    ).frames[0]

    print(f"Exporting video to {output_path}...")
    export_to_video(output, output_path, fps=16)
    
    # Save a binary backup
    backup_path = output_path.replace(".mp4", ".bin")
    torch.save(output, backup_path)
    print(f"Binary backup saved to: {backup_path}")

    return output_path

def main() -> None:
    output_filename = "moon_base_cinematic_wan.mp4"

    if DEVICE != "cuda":
        print("Warning: CUDA not detected. This model requires a GPU.")

    try:
        pipeline = build_pipeline(MODEL_ID)
        print("Starting generation...")
        result_path = generate_video(pipeline, PROMPT, output_filename)
        print(f"Process complete. Video: {result_path}")
    except Exception as e:
        print(f"Error during video generation: {e}")

if __name__ == "__main__":
    main()