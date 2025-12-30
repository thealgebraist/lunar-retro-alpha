import os
import sys
import torch
import scipy.io.wavfile
import numpy as np

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from transformers import pipeline

def transcribe_all():
    print("Loading Whisper Tiny...")
    # Use whisper-tiny for fast validation
    try:
        pipe = pipeline("automatic-speech-recognition", model="openai/whisper-tiny.en", device="cpu")
    except Exception as e:
        print(f"Failed to load pipeline: {e}")
        return

    files = {
        "announcement_0": "Evacuate the station. Oxygen level low.",
        "announcement_1": "This area is off limits.",
        "announcement_2": "Alert! Station integrity compromised.",
        "announcement_3": "Station running on backup power, please restart generator to survive.",
        "announcement_4": "Keep in mind that the radioactivity is level rising.",
        "announcement_5": "The mining area is off limits.",
        "announcement_6": "Proceed to the escape pod.",
        "announcement_7": "Airlock safety compromised.",
        "countdown_5m": "station integrity decompensation will occur in 5 minutes",
        "countdown_4m": "station integrity decompensation will occur in 4 minutes",
        "countdown_3m": "station integrity decompensation will occur in 3 minutes",
        "countdown_2m": "station integrity decompensation will occur in 2 minutes",
        "countdown_1m": "station integrity decompensation will occur in 1 minutes",
        "countdown_60s": "station integrity decompensation will occur in 60 seconds",
        "countdown_50s": "50 seconds",
        "countdown_40s": "40 seconds",
        "countdown_30s": "30 seconds",
        "countdown_20s": "20 seconds",
        "countdown_10s": "10 seconds",
        "countdown_imminent": "station integrity decompensation imminent"
    }

    results = []
    HQ_DIR = "moon_base_assets_hq"

    for name, expected in files.items():
        path = os.path.join(HQ_DIR, name + ".wav")
        if not os.path.exists(path):
            print(f"File not found: {path}")
            continue

        # Whisper pipeline can take raw numpy array
        rate, data = scipy.io.wavfile.read(path)
        # Convert to float32 mono
        if data.dtype == np.int16:
            data = data.astype(np.float32) / 32768.0
        elif data.dtype == np.int32:
            data = data.astype(np.float32) / 2147483648.0
        
        # Audio length might be zero if generation failed
        if len(data) == 0:
            print(f"Empty file: {path}")
            results.append((name, expected, "EMPTY"))
            continue

        # Transcribe
        # input_values = processor(data, sampling_rate=rate, return_tensors="pt").input_features
        # forced_decoder_ids = processor.get_decoder_prompt_ids(language="en", task="transcribe")
        # predicted_ids = model.generate(input_values, forced_decoder_ids=forced_decoder_ids)
        # transcription = processor.batch_decode(predicted_ids, skip_special_tokens=True)[0]
        
        # Simpler with pipeline
        transcription = pipe({"sampling_rate": rate, "raw": data})["text"]
        print(f"File: {name}\nExpected: {expected}\nGot:      {transcription.strip()}\n")
        results.append((name, expected, transcription.strip()))

    return results

if __name__ == "__main__":
    transcribe_all()
