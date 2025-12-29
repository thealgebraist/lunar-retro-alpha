import torch
from diffusers import AudioLDM2Pipeline
import scipy.io.wavfile
import numpy as np
import os
import subprocess

def main():
    model_id = "cvssp/audioldm2-large"
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    from transformers import GPT2LMHeadModel
    lang_model = GPT2LMHeadModel.from_pretrained(model_id, subfolder="language_model", torch_dtype=torch.float16 if device == "mps" else torch.float32)
    pipe = AudioLDM2Pipeline.from_pretrained(model_id, language_model=lang_model, torch_dtype=torch.float16 if device == "mps" else torch.float32).to(device)
    
    os.makedirs("moon_base_assets_hq", exist_ok=True)
    
    new_sounds = {
        "terminal_tick": "Single sharp mechanical typewriter tick, electronic high-frequency click, Alien movie computer style, short and crisp",
        "airlock_death": "Decompression explosive hiss, sudden rush of air, metallic katchong clunk followed by eerie silence",
        "elevator_button": "Heavy 1950s industrial push button click, mechanical snap",
        "elevator_approach": "Distant low-frequency industrial drone slowly getting louder, mechanical vibration, hum of a large machine",
        "elevator_klonk": "Heavy metallic klonk, rusty screeching door opening, pneumatic air release",
        "elevator_moving": "Heavy industrial lift moving, rattling chains, grinding gears, low frequency thrum, rhythmic vibration",
        "elevator_death": "Sorrowful cinematic 1950s strings, low dark cello, peaceful but lonely ending theme"
    }

    for name, prompt in new_sounds.items():
        output_wav = f"moon_base_assets_hq/{name}.wav"
        output_ogg = f"moon_base_assets/{name}.ogg"
        print(f"Generating: {name}...")
        
        duration = 5.0
        if name == "elevator_approach": duration = 10.0 # We will loop this
        if name == "elevator_moving": duration = 10.0 # We will loop this
        if name == "elevator_death": duration = 10.0
        if name == "terminal_tick": duration = 1.0

        audio = pipe(prompt, num_inference_steps=30, audio_length_in_s=duration).audios[0]
        
        # Normalize
        rms = np.sqrt(np.mean(audio**2))
        target_rms = 10**(-18.0 / 20)
        audio = audio * (target_rms / (rms + 1e-9))
        peak = np.max(np.abs(audio))
        if peak > 0.95: audio = audio * (0.95 / peak)

        scipy.io.wavfile.write(output_wav, 16000, (audio * 32767).astype(np.int16))
        subprocess.run(['ffmpeg', '-y', '-i', output_wav, '-c:a', 'libvorbis', '-q:a', '6', output_ogg], 
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    print("New interaction sounds generated.")

if __name__ == "__main__":
    main()
