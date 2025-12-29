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
    
    print(f"Loading {model_id} for MUTHUR tick...")
    lang_model = GPT2LMHeadModel.from_pretrained(model_id, subfolder="language_model", torch_dtype=torch.float16 if device == "mps" else torch.float32)
    pipe = AudioLDM2Pipeline.from_pretrained(model_id, language_model=lang_model, torch_dtype=torch.float16 if device == "mps" else torch.float32).to(device)
    
    # MUTHUR style: high pitched, chirpy, electronic but mechanical
    prompt = "Extremely short and sharp high-pitched electronic computer chirp, rhythmic mechanical relay click, 1950s mainframe terminal sound, Alien movie MUTHUR style, single crisp blip"
    negative_prompt = "low quality, noise, hum, voice, long, echo"

    output_wav = "moon_base_assets_hq/terminal_tick.wav"
    output_ogg = "moon_base_assets/terminal_tick.ogg"
    
    print(f"Generating MUTHUR-style tick...")
    # Generate 1 second (we only need the start)
    audio = pipe(prompt, negative_prompt=negative_prompt, num_inference_steps=40, audio_length_in_s=1.0).audios[0]
    
    # We want it to be very short, so let's trim it to first 100ms or so if there is signal
    # Or just use the whole thing if it's mostly silence after the hit.
    
    # Normalize
    rms = np.sqrt(np.mean(audio**2))
    target_rms = 10**(-12.0 / 20) # Louder for ticks
    audio = audio * (target_rms / (rms + 1e-9))
    peak = np.max(np.abs(audio))
    if peak > 0.98: audio = audio * (0.98 / peak)

    scipy.io.wavfile.write(output_wav, 16000, (audio * 32767).astype(np.int16))
    
    # Convert to OGG with high quality
    subprocess.run(['ffmpeg', '-y', '-i', output_wav, '-c:a', 'libvorbis', '-q:a', '8', output_ogg], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    print("MUTHUR terminal tick generated.")

if __name__ == "__main__":
    main()
