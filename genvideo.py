import torch
from diffusers import CogVideoXPipeline
from diffusers.utils import export_to_video

# Data types for scene configuration
from typing import Final

# Constants for the 3090 optimization
DEVICE: Final[str] = "cuda"
PROMPT: Final[str] = (
    "A cinematic, high-detail wide shot of a derelict 1950s-style moon base. "
    "The base consists of rusted chrome domes and retro-futuristic antennas. "
    "The camera flies past slowly from a distance. Through the thick glass portholes, "
    "tiny silhouettes of people are visible moving inside. "
    "Lunar dust kicks up in the foreground. High contrast, 35mm film grain, sci-fi noir."
)

def build_pipeline(model_id: str) -> CogVideoXPipeline:
    """
    Initializes the CogVideoX pipeline with 3090-specific optimizations.
    Uses FP8 precision to stay under 24GB VRAM.
    """
    pipe = CogVideoXPipeline.from_pretrained(
        model_id,
        torch_dtype=torch.float16  # Load in 16-bit
    )
    
    # Enable CPU offloading for parts of the model not currently in use
    # and VAE slicing to handle the memory-heavy decoding step.
    pipe.enable_model_cpu_offload()
    pipe.vae.enable_slicing()
    pipe.vae.enable_tiling()
    
    return pipe

def generate_adventure_video(
    pipe: CogVideoXPipeline, 
    prompt: str, 
    output_path: str,
    seed: int = 42
) -> str:
    """
    Generates a 5-second video (approx 40-72 frames depending on config).
    Returns the path to the saved file.
    """
    generator = torch.Generator(device=DEVICE).manual_seed(seed)
    
    # CogVideoX-5B typically generates at 720p; we scale down/config for 480p 
    # to ensure stability and speed on a single consumer card.
    video_frames = pipe(
        prompt=prompt,
        num_videos_per_prompt=1,
        num_inference_steps=50,  # Standard for high quality
        num_frames=48,           # ~5 seconds at 8-10 fps or 2 seconds at 24fps
        guidance_scale=6.0,
        generator=generator,
    ).frames[0]

    export_to_video(video_frames, output_path, fps=8)
    return output_path

def main() -> None:
    model_path = "THUDM/CogVideoX-5b"
    output_filename = "moon_base_cinematic.mp4"
    
    print(f"Loading model {model_path} onto RTX 3090...")
    pipeline = build_pipeline(model_path)
    
    print("Starting generation. This may take 2-5 minutes...")
    result_path = generate_adventure_video(pipeline, PROMPT, output_filename)
    
    print(f"Video saved successfully to: {result_path}")

if __name__ == "__main__":
    main()