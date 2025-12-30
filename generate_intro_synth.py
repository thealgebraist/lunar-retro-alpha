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
    
    # Eerie 1950s space synth prompt
    prompt = "Eerie mysterious space synth music, 1950s sci-fi atmosphere, low pulsing drones, high shimmering analog oscillations, echoing electronic textures, cosmic horror, cinematic cinematic"
    negative_prompt = "low quality, noise, speech, drums, fast beat, happy"
    
    output_file = "moon_base_assets/intro_synth.wav"
    print(f"Generating intro synth (30 seconds)...")
    
    audio = pipe(
        prompt,
        negative_prompt=negative_prompt,
        num_inference_steps=50,
        audio_length_in_s=30.0
    ).audios[0]
    
    # Normalize to -18dB RMS
    target_rms_db = -18.0
    rms = np.sqrt(np.mean(audio**2))
    if rms > 0:
        target_rms = 10**(target_rms_db / 20)
        gain = target_rms / rms
        normalized = audio * gain
        peak = np.max(np.abs(normalized))
        if peak > 0.99:
            normalized = normalized * (0.99 / peak)
        
        # Make loopable (apply crossfade)
        sample_rate = 16000
        fade_samples = int(2.0 * sample_rate)
        start_fade = normalized[:fade_samples]
        end_fade = normalized[-fade_samples:]
        middle = normalized[fade_samples:-fade_samples]
        alpha = np.linspace(0, 1, fade_samples)
        blended = end_fade * (1 - alpha) + start_fade * alpha
        loopable = np.concatenate([blended, middle])
        
        scipy.io.wavfile.write(output_file, sample_rate, (loopable * 32767).astype(np.int16))
        print(f"Saved loopable intro synth to {output_file}")

if __name__ == "__main__":
    main()
