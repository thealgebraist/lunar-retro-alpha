import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess
import requests

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

try:
    from transformers import AutoProcessor, BarkModel
except ImportError:
    print("Transformers not found. Please run 'make setup_python' first.")
    sys.exit(1)

# Constants
HQ_DIR = "moon_base_assets_hq"
GAME_DIR = "moon_base_assets"
WORDS_HQ = os.path.join(HQ_DIR, "words")
WORDS_GAME = os.path.join(GAME_DIR, "words")
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
VOICE_PRESET = "v2/en_speaker_9" # Robotic androgynous female

if not os.path.exists(WORDS_HQ):
    os.makedirs(WORDS_HQ)
if not os.path.exists(WORDS_GAME):
    os.makedirs(WORDS_GAME)

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

def get_1000_words():
    # Fetch common words list
    url = "https://raw.githubusercontent.com/first20hours/google-10000-english/master/google-10000-english-no-swears.txt"
    try:
        response = requests.get(url)
        words = response.text.splitlines()[:1000]
        return words
    except Exception as e:
        print(f"Error fetching words: {e}")
        # Fallback list if offline
        return ["the", "be", "to", "of", "and", "a", "in", "that", "have", "i"]

def gen_word(text, filename):
    wav_path = os.path.join(WORDS_HQ, filename + ".wav")
    if os.path.exists(wav_path):
        return wav_path

    print(f"Generating Word: {text}...")
    processor, model = get_bark()
    
    # We wrap the word in a very short pause to help Bark focus on the single word
    inputs = processor(f"[pause] {text} [pause]", voice_preset=VOICE_PRESET)
    
    with torch.no_grad():
        audio_array = model.generate(**inputs.to(DEVICE))
        audio_array = audio_array.cpu().numpy().squeeze()
    
    # Trim silence? For now just save
    scipy.io.wavfile.write(wav_path, rate=model.generation_config.sample_rate, data=audio_array)
    return wav_path

def convert_to_ogg(wav_path, ogg_name):
    ogg_path = os.path.join(WORDS_GAME, ogg_name + ".ogg")
    if os.path.exists(ogg_path):
        return
    # Robotic PA quality
    filter_cmd = ["-af", "highpass=f=200,lowpass=f=4000,volume=1.5"]
    subprocess.run(['ffmpeg', '-y', '-i', wav_path] + filter_cmd + ['-c:a', 'libvorbis', '-q:a', '4', ogg_path], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():
    words = get_1000_words()
    print(f"Generating {len(words)} common words...")
    
    for word in words:
        # Sanitized filename
        filename = word.strip().lower()
        if not filename: continue
        
        try:
            wav = gen_word(filename, filename)
            convert_to_ogg(wav, filename)
        except Exception as e:
            print(f"Failed to generate '{filename}': {e}")

    print("\nCommon words library generated successfully!")

if __name__ == "__main__":
    main()
