import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess
from transformers import AutoProcessor, BarkModel

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Constants
HQ_DIR = "moon_base_assets_hq"
GAME_DIR = "moon_base_assets"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"

if not os.path.exists(HQ_DIR):
    os.makedirs(HQ_DIR)
if not os.path.exists(GAME_DIR):
    os.makedirs(GAME_DIR)

# Model
bark_processor = None
bark_model = None

def get_bark():
    global bark_processor, bark_model
    if bark_model is None:
        print("Loading Bark Large...")
        bark_processor = AutoProcessor.from_pretrained("suno/bark")
        bark_model = BarkModel.from_pretrained("suno/bark").to(DEVICE)
    return bark_processor, bark_model

def gen_history_segment(text, filename, preset="v2/en_speaker_6"):
    wav_path = os.path.join(HQ_DIR, filename + ".wav")
    if os.path.exists(wav_path):
        print(f"Skipping: {filename} (already exists)")
        return wav_path

    print(f"Generating History Segment: {filename}...")
    processor, model = get_bark()
    
    # Text with cues for better emotion/timing
    inputs = processor(text, voice_preset=preset)
    
    with torch.no_grad():
        audio_array = model.generate(**inputs.to(DEVICE))
        audio_array = audio_array.cpu().numpy().squeeze()
    
    scipy.io.wavfile.write(wav_path, rate=model.generation_config.sample_rate, data=audio_array)
    return wav_path

def convert_to_ogg(wav_path, ogg_name):
    print(f"Converting to {ogg_name}.ogg...")
    ogg_path = os.path.join(GAME_DIR, ogg_name + ".ogg")
    # Tape-like quality
    filter_cmd = ["-af", "highpass=f=200,lowpass=f=3500,volume=1.5"]
    subprocess.run(['ffmpeg', '-y', '-i', wav_path] + filter_cmd + ['-c:a', 'libvorbis', '-q:a', '4', ogg_path], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():
    history_segments = [
        {
            "name": "history_1_origins",
            "text": "[clears throat] Log entry one. Nineteen fifty-four. We just finished the primary dome. The view... it is breathtaking. Thousands of stars, and Earth hanging like a blue marble. We're here to stay. Science, progress, and the future of mankind. [pause] It's a new frontier.",
            "preset": "v2/en_speaker_6"
        },
        {
            "name": "history_2_life",
            "text": "Life on the base isn't all science. We have mess hall nights now. [laughs] Dr. Aris brought some old jazz tapes. The coffee is terrible, tastes like recycled plastic, but the camaraderie... that's what keeps us going. We're a family up here, two hundred thousand miles from home.",
            "preset": "v2/en_speaker_6"
        },
        {
            "name": "history_3_golden",
            "text": "The reactor is at full capacity. We've mapped the entire Tycho crater. Success after success. [sigh] They're talking about building a second base in the Mare Serenitatis. Everything was perfect. We were the kings of the moon. [pause] I wish it could have lasted forever.",
            "preset": "v2/en_speaker_6"
        },
        {
            "name": "history_4_downfall",
            "text": "[breathing heavily] Everything happened so fast. The breach in sector seven... it wasn't just a leak. [static] Something is wrong with the air. People are... changing. I've locked myself in the comms array. If anyone finds this... [whispers] don't come looking for us. It's over.",
            "preset": "v2/en_speaker_6"
        }
    ]

    for seg in history_segments:
        wav = gen_history_segment(seg["text"], seg["name"], preset=seg["preset"])
        convert_to_ogg(wav, seg["name"])

    print("\nHistory tapes generated successfully!")

if __name__ == "__main__":
    main()