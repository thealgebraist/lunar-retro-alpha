import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess

# Ensure local libs are found
sys.path.insert(0, os.path.abspath("local_libs"))

from diffusers import AudioLDM2Pipeline
from transformers import GPT2Model

def main():
    model_id = "cvssp/audioldm2-large"
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    # Workaround for GPT2Model vs GPT2LMHeadModel issue
    lang_model = GPT2Model.from_pretrained(model_id, subfolder="language_model", torch_dtype=torch.float16 if device == "mps" else torch.float32)
    
    pipe = AudioLDM2Pipeline.from_pretrained(
        model_id, 
        language_model=lang_model,
        torch_dtype=torch.float16 if device == "mps" else torch.float32
    ).to(device)
    
    os.makedirs("moon_base_assets_hq", exist_ok=True)
    os.makedirs("moon_base_assets", exist_ok=True)
    
    prompt = "steady low frequency electronic hum of a 1950s control room, rhythmic computer processing sounds, fan cooling, ambient drone, sci-fi computer room"
    name = "launch_control"
    
    print(f"Generating: {name}...")
    
    duration = 15.0 # Longer for better looping
    
    audio = pipe(
        prompt,
        negative_prompt="low quality, noise, speech, music, beep, alarm, frantic",
        num_inference_steps=30,
        audio_length_in_s=duration
    ).audios[0]

    # Normalize
    rms = np.sqrt(np.mean(audio**2))
    target_rms = 10**(-18.0 / 20)
    if rms > 0:
        audio = audio * (target_rms / rms)
    peak = np.max(np.abs(audio))
    if peak > 0.95: 
        audio = audio * (0.95 / peak)

    # Loop logic (crossfade)
    sample_rate = 16000
    fade_duration = 3.0
    fade_samples = int(fade_duration * sample_rate)
    
    start_fade = audio[:fade_samples]
    end_fade = audio[-fade_samples:]
    middle = audio[fade_samples:-fade_samples]
    
    alpha = np.linspace(0, 1, fade_samples)
    # Blend end into start to create the seam
    blended = end_fade * (1 - alpha) + start_fade * alpha
    
    # Result is blended + middle part. This makes the total length = duration - fade_duration
    # Actually, standard loop: take fade_samples from end, mix with start.
    # final = (start + end) ...
    # Simple way: cut fade_samples from end, mix it with start.
    # audio = [A (fade), B (body), C (fade)]
    # Loop = [A+C, B]
    
    final_audio = np.concatenate([blended, middle])

    output_wav = f"moon_base_assets_hq/{name}.wav"
    output_ogg = f"moon_base_assets/{name}.ogg"

    # Save WAV
    scipy.io.wavfile.write(output_wav, 16000, (final_audio * 32767).astype(np.int16))
    
    # Convert to OGG
    print(f"Converting to {output_ogg}...")
    subprocess.run(['ffmpeg', '-y', '-i', output_wav, '-c:a', 'libvorbis', '-q:a', '6', output_ogg], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    print("Launch control sound regenerated.")

if __name__ == "__main__":
    main()
