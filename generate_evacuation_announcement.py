import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from transformers import AutoProcessor, BarkModel
from pydub import AudioSegment, effects
from pydub.generators import WhiteNoise

# Constants
HQ_DIR = "moon_base_assets_hq"
GAME_DIR = "moon_base_assets"
DEVICE = "cpu"

if not os.path.exists(HQ_DIR):
    os.makedirs(HQ_DIR)
if not os.path.exists(GAME_DIR):
    os.makedirs(GAME_DIR)

# Models
bark_processor = None
bark_model = None

def get_bark():
    global bark_processor, bark_model
    if bark_model is None:
        print("Loading Bark...")
        bark_processor = AutoProcessor.from_pretrained("suno/bark-small")
        bark_model = BarkModel.from_pretrained("suno/bark-small").to(DEVICE)
    return bark_processor, bark_model

def gen_bark(text, filename, preset="v2/en_speaker_9"): 
    print(f"Generating Bark: {filename}...")
    processor, model = get_bark()
    # Add robotic prompt for monotone voice
    full_text = f"[monotone robot voice] {text}"
    inputs = processor(full_text, voice_preset=preset)
    with torch.no_grad():
        audio_array = model.generate(**inputs.to(DEVICE))
        audio_array = audio_array.cpu().numpy().squeeze()
    
    wav_path = os.path.join(HQ_DIR, filename + ".wav")
    scipy.io.wavfile.write(wav_path, rate=model.generation_config.sample_rate, data=audio_array)
    return wav_path

def bunker_tail(seg):
    out = seg
    taps = [
        (140, 16),
        (310, 18),
        (620, 20),
        (1050, 22),
        (1650, 24),
    ]
    for d, g in taps:
        out = out.overlay(seg - g, position=d)
    return out

def process_audio_python(wav_path, ogg_name):
    print(f"Processing {wav_path} -> {ogg_name}.ogg with Python Effects...")
    audio = AudioSegment.from_file(wav_path)

    # Mono PA
    audio = audio.set_channels(1)

    # Band-limit (small PA feel)
    audio = audio.high_pass_filter(220)
    audio = audio.low_pass_filter(5200)

    # Gentle saturation / Compression
    audio = audio.apply_gain(+2)
    audio = effects.compress_dynamic_range(audio, threshold=-20, ratio=2.0)

    # Distance cue: soften highs a bit more
    audio = audio.low_pass_filter(4200)

    # Early reflections (very subtle)
    early = (audio - 10)
    audio = audio.overlay(early, position=55)
    audio = audio.overlay(early - 3, position=165)

    # “Underground” tail via layered quiet delays (short + long)
    audio = bunker_tail(audio)

    # Slight ambience bed
    noise = WhiteNoise().to_audio_segment(duration=len(audio)).low_pass_filter(900) - 48
    audio = audio.overlay(noise)

    # Normalize gently
    audio = effects.normalize(audio - 1)

    ogg_path = os.path.join(GAME_DIR, ogg_name + ".ogg")
    audio.export(ogg_path, format="ogg")

def main():
    announcements = [
        ("Evacuate the station. Oxygen level low.", "announcement_0"),
        ("This area is off limits.", "announcement_1"),
        ("Alert! Station integrity compromised.", "announcement_2"),
        ("Station running on backup power, please restart generator to survive.", "announcement_3"),
        ("Keep in mind that the radioactivity is level rising.", "announcement_4"),
        ("The mining area is off limits.", "announcement_5"),
        ("Proceed to the escape pod.", "announcement_6"),
        ("Airlock safety compromised.", "announcement_7"),
        
        # Countdown
        ("station integrity decompensation in 5 minutes", "countdown_5m"),
        ("station integrity decompensation in 4 minutes", "countdown_4m"),
        ("station integrity decompensation in 3 minutes", "countdown_3m"),
        ("station integrity decompensation in 2 minutes", "countdown_2m"),
        ("station integrity decompensation in 1 minutes", "countdown_1m"),
        ("station integrity decompensation in 60 seconds", "countdown_60s"),
        ("50 seconds", "countdown_50s"),
        ("40 seconds", "countdown_40s"),
        ("30 seconds", "countdown_30s"),
        ("20 seconds", "countdown_20s"),
        ("10 seconds", "countdown_10s"),
        ("station integrity decompensation imminent", "countdown_imminent")
    ]
    
    for text, name in announcements:
        wav = os.path.join(HQ_DIR, name + ".wav")
        # Regenerate all to ensure the new "androgynous female robotic" voice
        wav = gen_bark(text, name)
        process_audio_python(wav, name)
    
    print("All announcements generated and processed.")

if __name__ == "__main__":
    main()
