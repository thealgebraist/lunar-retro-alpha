import torch
import os
import sys
try:
    from diffusers import LTXVideoPipeline
except ImportError:
    print("LTXVideoPipeline not found in diffusers. Please upgrade diffusers to >= 0.32.0")
    print("Trying to fallback to CogVideoXPipeline or exit...")
    from diffusers import CogVideoXPipeline as LTXVideoPipeline # Fallback just to avoid NameError if possible

from diffusers.utils import export_to_video
from typing import Final, List
import numpy as np

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Constants
DEVICE: Final[str] = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
MODEL_ID: Final[str] = "Lightricks/LTX-Video"
PROMPT: Final[str] = (
    "A cinematic, high-detail wide shot of a derelict 1950s-style moon base. "
    "The base consists of rusted chrome domes and retro-futuristic antennas. "
    "The camera flies past slowly from a distance. Through the thick glass portholes, "
    "tiny silhouettes of people are visible moving inside. "
    "Lunar dust kicks up in the foreground. High contrast, 35mm film grain, sci-fi noir."
)

def build_pipeline(model_id: str) -> LTXVideoPipeline:
    """
    Initializes the LTX-Video pipeline with optimizations.
    """
    print(f"Loading {model_id} onto {DEVICE}...")
    dtype = torch.bfloat16 if DEVICE == "cuda" else torch.float32
    
    pipe = LTXVideoPipeline.from_pretrained(
        model_id,
        torch_dtype=dtype
    )

    if DEVICE == "cuda":
        pipe.enable_model_cpu_offload()
    else:
        pipe.to(DEVICE)
        
    return pipe

def generate_ltx_video(
    pipe: LTXVideoPipeline,
    prompt: str,
    output_path: str,
    seed: int = 42
) -> str:
    """
    Generates a video using LTX-Video.
    """
    generator = torch.Generator(device=DEVICE).manual_seed(seed)

    print(f"Starting generation for prompt: {prompt}")
    
    output = pipe(
        prompt=prompt,
        negative_prompt="low quality, worst quality, deformed, distorted, grainy, noise, blurry",
        num_frames=161,
        width=768,
        height=512,
        num_inference_steps=50,
        guidance_scale=3.0,
        mu=7.5, # Required when use_dynamic_shifting is True (default for LTX-Video)
        generator=generator,
    ).frames[0]

    print(f"Exporting video to {output_path}...")
    export_to_video(output, output_path, fps=24)
    
    backup_path = output_path.replace(".mp4", ".bin")
    torch.save(output, backup_path)
    print(f"Binary backup saved to: {backup_path}")

    return output_path

def main() -> None:
    output_filename = "moon_base_cinematic.mp4"
    pipeline = build_pipeline(MODEL_ID)

    print("Starting generation. This may take several minutes...")
    try:
        result_path = generate_ltx_video(pipeline, PROMPT, output_filename)
        print(f"Process complete. Video: {result_path}")
    except Exception as e:
        print(f"Error during LTX-Video generation: {e}")

if __name__ == "__main__":
    main()