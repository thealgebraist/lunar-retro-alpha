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
    
    # Updated/New sounds
    new_sounds = {
        "battery_bank": "Deep industrial humming and oscillating electrical thrum of a large battery storage room, rhythmic low-frequency pulses, 1950s power station ambiance, no high pitch noise",
        "elevator_move": "Deep metallic vibration and the sound of heavy gears turning, ascending or descending in an old elevator shaft, industrial mechanical movement",
        "item_pickup": "A sharp, metallic mechanical click followed by a short electronic hum, picking up a solid metal object, retro sci-fi sound",
        "puzzle_success": "A satisfying mechanical three-note chime from an old intercom speaker, electrical relay clicking into place, 1950s melody",
        "airlock_hiss": "A sudden burst of high-pressure air followed by a heavy mechanical seal locking tight, pneumatic door sound",
        "battery_insert": "A heavy mechanical clunk followed by a rising electrical buzz as power begins to flow into a circuit"
    }
    
    negative_prompt = "low quality, noise, high pitched scream, shrill whistle, speech"
    
    for name, prompt in new_sounds.items():
        output_file = f"moon_base_assets/{name}.wav"
        print(f"Generating/Updating: {name}...")
        
        duration = 10.0 if name == "battery_bank" else 5.0
        
        audio = pipe(
            prompt,
            negative_prompt=negative_prompt,
            num_inference_steps=40, # Slightly more steps for better quality
            audio_length_in_s=duration
        ).audios[0]
        
        scipy.io.wavfile.write(output_file, 16000, (audio * 32767).astype(np.int16))

    print("New triggers and improved battery bank sound generated in 'moon_base_assets/'")

if __name__ == "__main__":
    main()
