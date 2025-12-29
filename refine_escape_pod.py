import torch
from diffusers import AudioLDMPipeline
import scipy.io.wavfile
import numpy as np
import os

def main():
    model_id = "cvssp/audioldm-s-full-v2"
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    pipe = AudioLDMPipeline.from_pretrained(model_id, torch_dtype=torch.float16).to(device)
    
    os.makedirs("moon_base_assets", exist_ok=True)
    
    # Highly specific prompt for the "classic space station" feel
    prompt = "Classic space station humming in a small cramped enclosure, padded soft fabrics and plastic surfaces damping the sound, low resonant mechanical drone, subtle vibration of metal panels, 1950s sci-fi interior, intimate and muffled acoustics"
    negative_prompt = "open space, large hall, reverb, loud noise, high pitch, speech, silence"
    
    output_file = "moon_base_assets/escape_pod.wav"
    print(f"Regenerating {output_file} with intimate cabin acoustics...")
    
    audio = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=60, # Higher steps for more texture
        audio_length_in_s=10.0
    ).audios[0]
    
    # Normalize
    target_rms_db = -18.0
    rms = np.sqrt(np.mean(audio**2))
    if rms > 0:
        target_rms = 10**(target_rms_db / 20)
        gain = target_rms / rms
        normalized = audio * gain
        peak = np.max(np.abs(normalized))
        if peak > 0.99:
            normalized = normalized * (0.99 / peak)
        scipy.io.wavfile.write(output_file, 16000, (normalized * 32767).astype(np.int16))

    print("Successfully updated escape_pod.wav")

if __name__ == "__main__":
    main()
