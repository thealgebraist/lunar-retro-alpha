import os
import sys

# Ensure local libs are found
sys.path.insert(0, os.path.abspath("local_libs"))

import torch
from diffusers import AudioLDM2Pipeline
import scipy.io.wavfile
import numpy as np
import subprocess

def main():
    model_id = "cvssp/audioldm2-large"
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    from transformers import GPT2Model
    
    # Workaround for GPT2Model vs GPT2LMHeadModel issue
    lang_model = GPT2Model.from_pretrained(model_id, subfolder="language_model", torch_dtype=torch.float16 if device == "mps" else torch.float32)
    
    pipe = AudioLDM2Pipeline.from_pretrained(
        model_id, 
        language_model=lang_model,
        torch_dtype=torch.float16 if device == "mps" else torch.float32
    ).to(device)
    
    os.makedirs("moon_base_assets_hq", exist_ok=True)
    os.makedirs("moon_base_assets", exist_ok=True)
    
    sounds = {
        "airlock_hiss": "Sudden burst of high-pressure air, heavy mechanical seal locking",
        "airlock_death": "Decompression explosive hiss, sudden rush of air, metallic katchong clunk followed by eerie silence"
    }

    negative_prompt = "low quality, noise, speech, drums, distorted"

    for name, prompt in sounds.items():
        output_wav = f"moon_base_assets_hq/{name}.wav"
        output_ogg = f"moon_base_assets/{name}.ogg"
        
        print(f"Generating: {name}...")
        
        duration = 5.0
        
        audio = pipe(
            prompt,
            negative_prompt=negative_prompt,
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

        # Save WAV
        scipy.io.wavfile.write(output_wav, 16000, (audio * 32767).astype(np.int16))
        
        # Convert to OGG
        print(f"Converting to {output_ogg}...")
        subprocess.run(['ffmpeg', '-y', '-i', output_wav, '-c:a', 'libvorbis', '-q:a', '6', output_ogg], 
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    print("Airlock sounds regenerated.")

if __name__ == "__main__":
    main()
