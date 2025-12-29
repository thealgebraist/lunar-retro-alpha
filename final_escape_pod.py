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
    
    # Prompt emphasizing mid-range frequencies for better audibility
    # "Soft fabrics" can sometimes lead to too much damping, so we balance it with "whirring"
    prompt = "Loud steady mechanical whirring, spaceship ventilation fan, audible mid-range drone, small padded cabin, muffled plastic and metal resonance, 1950s sci-fi atmosphere"
    negative_prompt = "silence, subsonic, low frequency only, high pitch screech, speech, music"
    
    output_file = "moon_base_assets/escape_pod.wav"
    print(f"Regenerating {output_file} with louder mid-range texture...")
    
    audio = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=50,
        audio_length_in_s=10.0
    ).audios[0]
    
    # Normalize to -12dB RMS (LOUDER)
    target_rms_db = -12.0
    rms = np.sqrt(np.mean(audio**2))
    
    if rms > 0:
        target_rms = 10**(target_rms_db / 20)
        gain = target_rms / rms
        normalized = audio * gain
        
        # Prevent clipping
        peak = np.max(np.abs(normalized))
        if peak > 0.95:
            normalized = normalized * (0.95 / peak)
            
        print(f"Final Peak: {20*np.log10(np.max(np.abs(normalized))):.2f} dB")
        print(f"Final RMS: {20*np.log10(np.sqrt(np.mean(normalized**2))):.2f} dB")
        
        scipy.io.wavfile.write(output_file, 16000, (normalized * 32767).astype(np.int16))
        print("Successfully updated escape_pod.wav")
    else:
        print("ERROR: Model produced silence.")

if __name__ == "__main__":
    main()
