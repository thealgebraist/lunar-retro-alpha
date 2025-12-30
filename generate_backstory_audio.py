import torch
from diffusers import AudioLDMPipeline
import scipy.io.wavfile
import numpy as np
import os
import subprocess

def main():
    model_id = "cvssp/audioldm-s-full-v2"
    device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    pipe = AudioLDMPipeline.from_pretrained(model_id, torch_dtype=torch.float16).to(device)
    
    os.makedirs("moon_base_assets", exist_ok=True)
    
    # Cinematic 8-second intro/backstory sound
    prompt = "Dramatic sci-fi film intro, low brass hits, rising orchestral tension, shimmering electronics, 1950s cinematic style, 8 seconds long"
    negative_prompt = "low quality, noise, speech, drums, looping"
    
    output_wav = "moon_base_assets/backstory.wav"
    output_ogg = "moon_base_assets/backstory.ogg"
    print(f"Generating backstory soundtrack (8 seconds)...")
    
    audio = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=50,
        audio_length_in_s=8.0
    ).audios[0]
    
    # Normalize to -12dB RMS
    target_rms_db = -12.0
    rms = np.sqrt(np.mean(audio**2))
    if rms > 0:
        target_rms = 10**(target_rms_db / 20)
        gain = target_rms / rms
        normalized = audio * gain
        peak = np.max(np.abs(normalized))
        if peak > 0.99:
            normalized = normalized * (0.99 / peak)
        
        scipy.io.wavfile.write(output_wav, 16000, (normalized * 32767).astype(np.int16))
        
        # Convert to OGG
        cmd = ['ffmpeg', '-y', '-i', output_wav, '-c:a', 'libvorbis', '-q:a', '6', output_ogg]
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        print(f"Saved backstory OGG to {output_ogg}")

if __name__ == "__main__":
    main()
