import torch
from diffusers import AudioLDMPipeline
import scipy.io.wavfile
import numpy as np
import os

def main():
    model_id = "cvssp/audioldm-s-full-v2"
    device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    pipe = AudioLDMPipeline.from_pretrained(model_id, torch_dtype=torch.float16).to(device)
    
    os.makedirs("moon_base_assets", exist_ok=True)
    
    # Heroic but lonely 50s sci-fi ending
    prompt = "Heroic celebratory space synth music, 1950s sci-fi radio drama ending, triumphant analog brass and shimmering pads, fading into peaceful lonely silence, cinematic conclusion"
    negative_prompt = "low quality, noise, speech, drums, chaos"
    
    output_file = "moon_base_assets/ending_synth.wav"
    print(f"Generating ending synth (30 seconds)...")
    
    audio = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=50,
        audio_length_in_s=30.0
    ).audios[0]
    
    # Normalize to -15dB RMS (slightly louder for finale)
    target_rms_db = -15.0
    rms = np.sqrt(np.mean(audio**2))
    if rms > 0:
        target_rms = 10**(target_rms_db / 20)
        gain = target_rms / rms
        normalized = audio * gain
        peak = np.max(np.abs(normalized))
        if peak > 0.99:
            normalized = normalized * (0.99 / peak)
        
        scipy.io.wavfile.write(output_file, 16000, (normalized * 32767).astype(np.int16))
        print(f"Saved ending synth to {output_file}")

if __name__ == "__main__":
    main()
