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
    
    prompt = "growling combination of goat horse elephant car lion robot all mixed together with a loud trumpet sound"
    name = "alien_death"
    
    print(f"Generating: {name}...")
    audio = pipe(
        prompt,
        negative_prompt="low quality, noise, speech, music, cheerful",
        num_inference_steps=30,
        audio_length_in_s=5.0
    ).audios[0]

    # Normalize
    rms = np.sqrt(np.mean(audio**2))
    target_rms = 10**(-10.0 / 20) # Louder than usual
    if rms > 0:
        audio = audio * (target_rms / rms)
    peak = np.max(np.abs(audio))
    if peak > 0.95: 
        audio = audio * (0.95 / peak)

    output_wav = f"moon_base_assets_hq/{name}.wav"
    output_ogg = f"moon_base_assets/{name}.ogg"

    # Save WAV
    scipy.io.wavfile.write(output_wav, 16000, (audio * 32767).astype(np.int16))
    
    # Convert to OGG
    print(f"Converting to {output_ogg}...")
    subprocess.run(['ffmpeg', '-y', '-i', output_wav, '-c:a', 'libvorbis', '-q:a', '6', output_ogg], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    print("Alien monster sound generated.")

if __name__ == "__main__":
    main()
