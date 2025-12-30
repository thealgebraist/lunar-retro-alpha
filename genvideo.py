import torch
import os
from diffusers import CogVideoXPipeline
from typing import Final, List
from moviepy.editor import ImageSequenceClip
import numpy as np

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
    Uses FP16 and memory offloading to stay under 24GB VRAM.
    """
    pipe = CogVideoXPipeline.from_pretrained(
        model_id,
        torch_dtype=torch.float16
    )

    # Enable CPU offloading and VAE optimizations for memory efficiency
    pipe.enable_model_cpu_offload()

    return pipe

def save_binary_backup(frames: List[np.ndarray], backup_path: str) -> None:
    """
    Saves the raw numpy frames to a binary file using torch.save.
    This acts as a pre-encoding backup.
    """
    # Convert list of frames to a single numpy array for storage
    frames_array = np.stack(frames)
    torch.save(frames_array, backup_path)
    print(f"Binary backup saved to: {backup_path}")

def export_video_moviepy(frames: List[np.ndarray], output_path: str, fps: int = 8) -> None:
    """
    Exports the video using MoviePy instead of OpenCV.
    """
    try:
        # CogVideoX returns a list of PIL images or numpy arrays.
        # MoviePy ImageSequenceClip works well with numpy arrays (RGB).
        clip = ImageSequenceClip(frames, fps=fps)
        clip.write_videofile(output_path, codec="libx264", audio=False)
    except Exception as e:
        print(f"Error during video export: {e}")
        print("Note: The binary backup was already saved successfully.")

def generate_adventure_video(
    pipe: CogVideoXPipeline,
    prompt: str,
    output_path: str,
    seed: int = 42
) -> str:
    """
    Generates frames, saves a binary backup, then encodes to MP4 using MoviePy.
    """
    generator = torch.Generator(device=DEVICE).manual_seed(seed)

    # Generate video frames
    # result.frames[0] is typically a list of PIL images
    output = pipe(
        prompt=prompt,
        num_videos_per_prompt=1,
        num_inference_steps=50,
        num_frames=8,
        guidance_scale=6.0,
        generator=generator,
    )

    # Convert PIL images to numpy arrays for processing/backup
    video_frames_np = [np.array(frame) for frame in output.frames[0]]

    # 1. Save binary backup first
    backup_filename = output_path.replace(".mp4", ".bin")
    save_binary_backup(video_frames_np, backup_filename)

    # 2. Export to video using MoviePy
    export_video_moviepy(video_frames_np, output_path, fps=8)

    return output_path

def main() -> None:
    model_path = "THUDM/CogVideoX-5b"
    output_filename = "moon_base_cinematic.mp4"

    print(f"Loading model {model_path} onto RTX 3090...")
    pipeline = build_pipeline(model_path)

    print("Starting generation. This may take 2-5 minutes...")
    result_path = generate_adventure_video(pipeline, PROMPT, output_filename)

    print(f"Process complete. Video: {result_path}")

if __name__ == "__main__":
    main()