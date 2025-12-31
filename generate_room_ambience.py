import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess
from transformers import AutoProcessor, AudioGenForConditionalGeneration

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Constants
HQ_DIR = "moon_base_assets_hq/ambience"
GAME_DIR = "moon_base_assets/ambience"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
MODEL_ID = "facebook/audiogen-medium"

if not os.path.exists(HQ_DIR):
    os.makedirs(HQ_DIR)
if not os.path.exists(GAME_DIR):
    os.makedirs(GAME_DIR)

# Model
processor = None
model = None

def get_audiogen():
    global processor, model
    if model is None:
        print(f"Loading {MODEL_ID} on {DEVICE}...")
        processor = AutoProcessor.from_pretrained(MODEL_ID)
        model = AudioGenForConditionalGeneration.from_pretrained(MODEL_ID).to(DEVICE)
    return processor, model

def gen_ambience(prompt, filename):
    wav_path = os.path.join(HQ_DIR, filename + ".wav")
    if os.path.exists(wav_path):
        print(f"Skipping: {filename} (already exists)")
        return wav_path

    print(f"Generating Ambience: {filename}...")
    proc, net = get_audiogen()
    
    inputs = proc(text=[prompt], return_tensors="pt").to(DEVICE)
    
    with torch.no_grad():
        audio_values = net.generate(**inputs, max_new_tokens=1500)
        audio_array = audio_values[0, 0].cpu().numpy()
    
    # Normalize
    rms = np.sqrt(np.mean(audio_array**2))
    target_rms = 10**(-20.0 / 20)
    if rms > 0:
        audio_array = audio_array * (target_rms / (rms + 1e-9))
    peak = np.max(np.abs(audio_array))
    if peak > 0.95:
        audio_array = audio_array * (0.95 / peak)

    # Loopable processing
    sample_rate = 16000 
    fade_samples = int(4.0 * sample_rate) 
    if len(audio_array) > fade_samples * 2:
        start_fade = audio_array[:fade_samples]
        end_fade = audio_array[-fade_samples:]
        middle = audio_array[fade_samples:-fade_samples]
        alpha = np.linspace(0, 1, fade_samples)
        blended = end_fade * (1 - alpha) + start_fade * alpha
        audio_array = np.concatenate([blended, middle])

    scipy.io.wavfile.write(wav_path, rate=sample_rate, data=(audio_array * 32767).astype(np.int16))
    return wav_path

def convert_to_ogg(wav_path, ogg_name):
    print(f"Converting to {ogg_name}.ogg...")
    ogg_path = os.path.join(GAME_DIR, ogg_name + ".ogg")
    subprocess.run(['ffmpeg', '-y', '-i', wav_path] + ['-c:a', 'libvorbis', '-q:a', '5', ogg_path], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():
    rooms = {
        "observation_dome": "Eerie whistling wind from a micro-leak in a glass dome, faint rhythmic mechanical clock ticking, space station ambiance",
        "comms_array": "Harsh static hiss, electric hum of vacuum tube cabinets, rhythmic clicking of teletype machines",
        "security_hub": "Low frequency electrical hum of a heavy transformer, flickering CRT buzz, distant industrial echoes",
        "elevator_lobby": "Distant metallic groan from an elevator shaft, low industrial drone, cavernous hum",
        "mess_hall": "Quiet empty room acoustics, distant water dripping on metal, ghostly distorted intercom hum",
        "sleeping_pods": "Soft rhythmic wheezing of a ventilation fan, quiet breathing, small metallic room",
        "medical_lab": "High pitched chemical valve drip, sterile electronic hum, glass clattering softly",
        "main_reactor": "Deep bone-shaking sub-bass thrum of a nuclear core, static electricity crackle",
        "fuel_storage": "Hollow echoing footsteps on metal grating, low moan of cold expanding pipes, silence",
        "battery_bank": "Deep industrial humming, oscillating electrical thrum, low frequency pulses",
        "maintenance_tunnels": "Scuttling of metal on metal, hiss of escaping steam, cramped industrial acoustics",
        "cargo_loading": "Howling wind against heavy hangar doors, groaning stressed metal beams",
        "oxygen_scrubbers": "Deep wet gurgling of liquid tanks, rhythmic puffing of large mechanical bellows",
        "launch_control": "Frantic clicking of a geiger counter, steady electronic countdown beep, tense room",
        "escape_pod": "Loud steady mechanical whirring, spaceship ventilation fan, small padded cabin",
        "mine_level": "Rough hewn rock cavern, distant echoes of heavy machinery, dripping water, deep rumbles"
    }

    for room_id, prompt in rooms.items():
        for i in range(2):
            filename = f"{room_id}_ambience_{i}"
            full_prompt = f"{prompt}, looping background sound, high quality, realistic variation {i}"
            wav = gen_ambience(full_prompt, filename)
            convert_to_ogg(wav, filename)

    print("\nRoom ambience generated successfully!")

if __name__ == "__main__":
    main()