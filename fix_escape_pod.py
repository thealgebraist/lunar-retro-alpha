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
    
    # Improved prompt for audible texture
    prompt = "Low frequency room tone of a small metal spacecraft cabin, very faint electronic hum, soft air flow, quiet interior ambiance, 1950s sci-fi"
    negative_prompt = "low quality, noise, silence, dead air, high pitch"
    
    output_file = "moon_base_assets/escape_pod.wav"
    print(f"Regenerating {output_file}...")
    
    audio = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=50,
        audio_length_in_s=10.0
    ).audios[0]
    
    scipy.io.wavfile.write(output_file, 16000, (audio * 32767).astype(np.int16))

    # Normalize immediately
    print("Normalizing...")
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

    print("Done.")

if __name__ == "__main__":
    main()
