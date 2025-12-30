import torch
from diffusers import AudioLDMPipeline
import scipy.io.wavfile
import numpy as np
import os

def main():
    # Using the Large model for better texture
    model_id = "cvssp/audioldm-l-full"
    device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    pipe = AudioLDMPipeline.from_pretrained(model_id, torch_dtype=torch.float16).to(device)
    
    os.makedirs("moon_base_assets", exist_ok=True)
    
    # Prompt with more mid-range "audible" components
    prompt = "Audible steady mechanical whirring of a ventilation fan in a small spaceship cabin, rhythmic low-frequency humming, soft electrical buzzing, 1950s sci-fi equipment noise, cramped padded interior acoustics"
    negative_prompt = "silence, subsonic, dead air, speech, music, high pitch whistle"
    
    output_file = "moon_base_assets/escape_pod.wav"
    print(f"Generating {output_file} with Large model...")
    
    audio = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=50,
        audio_length_in_s=10.0
    ).audios[0]
    
    # Check if we got actual signal and not just flatline/subsonic
    peak_val = np.max(np.abs(audio))
    print(f"Original peak: {peak_val}")
    
    # Normalize to -12dB RMS to make it definitely audible
    target_rms_db = -12.0
    rms = np.sqrt(np.mean(audio**2))
    print(f"Original RMS: {rms}")
    
    if rms > 0:
        target_rms = 10**(target_rms_db / 20)
        gain = target_rms / rms
        normalized = audio * gain
        peak = np.max(np.abs(normalized))
        if peak > 0.99:
            normalized = normalized * (0.99 / peak)
        
        print(f"Final peak after normalization: {np.max(np.abs(normalized))}")
        scipy.io.wavfile.write(output_file, 16000, (normalized * 32767).astype(np.int16))
    else:
        print("ERROR: Generated audio is silent!")

if __name__ == "__main__":
    main()
