import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess
import requests
import librosa
from transformers import AutoProcessor, BarkModel

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Constants
HQ_DIR = "moon_base_assets_hq"
GAME_DIR = "moon_base_assets"
WORDS_HQ = os.path.join(HQ_DIR, "words")
WORDS_GAME = os.path.join(GAME_DIR, "words")
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
VOICE_PRESET = "v2/en_speaker_9" # Robotic androgynous female
WORDS_PER_BATCH = 64

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
    url = "https://raw.githubusercontent.com/first20hours/google-10000-english/master/google-10000-english-no-swears.txt"
    try:
        response = requests.get(url)
        words = response.text.splitlines()[:1000]
        return words
    except Exception as e:
        print(f"Error fetching words: {e}")
        return ["the", "be", "to", "of", "and", "a", "in", "that", "have", "i"]

def split_audio_into_words(audio_array, sample_rate, word_list):
    intervals = librosa.effects.split(audio_array, top_db=30)
    
    if len(intervals) != len(word_list):
        print(f"Warning: Detected {len(intervals)} intervals but expected {len(word_list)} words.")
    
    for i, (start, end) in enumerate(intervals):
        if i >= len(word_list): break
        
        word = word_list[i].strip().lower()
        word_audio = audio_array[start:end]
        
        wav_path = os.path.join(WORDS_HQ, f"{word}.wav")
        scipy.io.wavfile.write(wav_path, rate=sample_rate, data=word_audio)
        convert_to_ogg(wav_path, word)

def convert_to_ogg(wav_path, ogg_name):
    ogg_path = os.path.join(WORDS_GAME, ogg_name + ".ogg")
    filter_cmd = ["-af", "highpass=f=200,lowpass=f=4000,volume=1.5"]
    subprocess.run(['ffmpeg', '-y', '-i', wav_path] + filter_cmd + ['-c:a', 'libvorbis', '-q:a', '4', ogg_path], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():
    words = get_1000_words()
    print(f"Generating {len(words)} words in batches of {WORDS_PER_BATCH}...")
    
    processor, model = get_bark()
    sample_rate = model.generation_config.sample_rate

    for i in range(0, len(words), WORDS_PER_BATCH):
        batch = words[i:i + WORDS_PER_BATCH]
        if all(os.path.exists(os.path.join(WORDS_GAME, f"{w.strip().lower()}.ogg")) for w in batch):
            continue

        batch_text = ", ".join(batch)
        print(f"Processing Batch {i//WORDS_PER_BATCH + 1}: {batch[0]}...{batch[-1]}")
        
        inputs = processor(batch_text, voice_preset=VOICE_PRESET)
        
        with torch.no_grad():
            try:
                audio_array = model.generate(**inputs.to(DEVICE))
                audio_array = audio_array.cpu().numpy().squeeze()
                split_audio_into_words(audio_array, sample_rate, batch)
            except Exception as e:
                print(f"Error processing batch starting at {i}: {e}")

    print("\nCommon words library generation complete!")

if __name__ == "__main__":
    main()
