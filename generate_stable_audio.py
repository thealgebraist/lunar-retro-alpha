import torch
import soundfile as sf
from diffusers import StableAudioPipeline
import os

def generate_audio(prompt, negative_prompt="Low quality, static, noise, distorted", duration_seconds=10, output_file="output_stable_audio.wav"):
    print(f"Loading Stable Audio Open 1.0...")
    
    # Use MPS if on Apple Silicon, otherwise CPU (Stable Audio Open usually requires float32 on MPS)
    device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
    torch_dtype = torch.float32 # MPS often prefers float32 for these specific pipelines
    
    pipe = StableAudioPipeline.from_pretrained(
        "stabilityai/stable-audio-open-1.0", 
        torch_dtype=torch_dtype
    )
    pipe = pipe.to(device)

    print(f"Generating: {prompt}")
    
    # Calculate steps based on duration if needed, or use default
    # The model is trained for 47s, so we use audio_end_in_s to clip/guide duration
    generator = torch.Generator(device=device).manual_seed(42)
    
    output = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=100,
        audio_end_in_s=duration_seconds,
        num_waveforms_per_prompt=1,
        generator=generator
    )

    audio = output.audios[0]
    
    # Save the file
    # audio is typically [channels, samples]
    # soundfile expects [samples, channels]
    audio_to_save = audio.T.float().cpu().numpy()
    
    sf.write(output_file, audio_to_save, pipe.config.sampling_rate)
    print(f"Saved to {output_file}")

if __name__ == "__main__":
    prompt = "A cinematic orchestral piece with rising tension and deep brass hits"
    generate_audio(prompt)
