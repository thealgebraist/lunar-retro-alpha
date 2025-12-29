import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from transformers import AutoProcessor, BarkModel
from diffusers import AudioLDM2Pipeline

# Constants
HQ_DIR = "moon_base_assets_hq"
GAME_DIR = "moon_base_assets"
DEVICE = "cpu" # Mac M1/M2/M3 usually prefers "mps", but sticking to cpu for max compatibility if torch isn't built for it here.

if not os.path.exists(HQ_DIR):
    os.makedirs(HQ_DIR)
if not os.path.exists(GAME_DIR):
    os.makedirs(GAME_DIR)

# Models
bark_processor = None
bark_model = None
audioldm_pipe = None

def get_bark():
    global bark_processor, bark_model
    if bark_model is None:
        print("Loading Bark...")
        bark_processor = AutoProcessor.from_pretrained("suno/bark-small")
        bark_model = BarkModel.from_pretrained("suno/bark-small").to(DEVICE)
    return bark_processor, bark_model

def get_audioldm():
    global audioldm_pipe
    if audioldm_pipe is None:
        print("Loading AudioLDM2...")
        # Use the large model as requested
        repo_id = "cvssp/audioldm2-large"
        audioldm_pipe = AudioLDM2Pipeline.from_pretrained(repo_id, torch_dtype=torch.float32)
        audioldm_pipe.to(DEVICE)
    return audioldm_pipe

def gen_bark(text, filename, preset="v2/en_speaker_6"):
    print(f"Generating Bark: {filename}...")
    processor, model = get_bark()
    inputs = processor(text, voice_preset=preset)
    with torch.no_grad():
        audio_array = model.generate(**inputs.to(DEVICE))
        audio_array = audio_array.cpu().numpy().squeeze()
    
    wav_path = os.path.join(HQ_DIR, filename + ".wav")
    scipy.io.wavfile.write(wav_path, rate=model.generation_config.sample_rate, data=audio_array)
    return wav_path

def gen_ldm(prompt, filename, duration=5.0, steps=20):
    print(f"Generating AudioLDM: {filename}...")
    pipe = get_audioldm()
    # negative_prompt = "low quality, average quality, noise, music"
    audio = pipe(prompt, num_inference_steps=steps, audio_length_in_s=duration).audios[0]
    
    wav_path = os.path.join(HQ_DIR, filename + ".wav")
    scipy.io.wavfile.write(wav_path, rate=16000, data=audio)
    return wav_path

def convert_to_ogg(wav_path, ogg_name, lowpass=None):
    print(f"Converting {wav_path} -> {ogg_name}.ogg...")
    ogg_path = os.path.join(GAME_DIR, ogg_name + ".ogg")
    filter_cmd = []
    if lowpass:
        filter_cmd = ["-af", f"lowpass=f={lowpass}"]
    cmd = ["ffmpeg", "-y", "-i", wav_path] + filter_cmd + ["-c:a", "libvorbis", ogg_path]
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def mix_tape_log():
    print("Mixing tape log...")
    # Generate Voice
    voice_path = gen_bark(
        "[sigh] Log entry 4-1-2. We were hit. That meteor shower... it came out of nowhere. [pause] Hull breach in sector 7. Things went downhill fast. Life support is failing. [static] Everyone... disappeared into the tunnels. I'm the only one left.", 
        "tape_voice_raw"
    )
    # Generate BG
    bg_path = gen_ldm("space station background humming, distant heavy explosions, metallic crashing, eerie silence", "tape_bg_raw", duration=20.0)
    
    # Mix
    final_wav = os.path.join(HQ_DIR, "tape_log.wav")
    # Apply filters to voice and mix with bg
    filter_complex = "[0:a]highpass=f=300,lowpass=f=3000,vibrato=f=6:d=0.1,volume=2.0[v];[1:a]volume=0.6[bg];[v][bg]amix=inputs=2:duration=first[out]"
    
    cmd = [
        "ffmpeg", "-y",
        "-i", voice_path,
        "-i", bg_path,
        "-filter_complex", filter_complex,
        "-map", "[out]",
        final_wav
    ]
    subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    convert_to_ogg(final_wav, "tape_log")

def main():
    # 1. Tape Log (Bark + LDM Mix)
    try:
        mix_tape_log()
    except Exception as e:
        print(f"Failed tape log: {e}")

    # 2. Reactions (Bark)
    reactions = [
        "What was that?",
        "What in the...",
        "I wonder what that is.",
        "What in the world just happened?",
        "I hope this place doesn't collapse.",
        "Is that dust coming from the ceiling?!",
        "Wow."
    ]
    for i, txt in enumerate(reactions):
        p = gen_bark(f"[hesitation] {txt}", f"reaction_{i}")
        convert_to_ogg(p, f"reaction_{i}")

    # 3. Lever Reactions (Bark)
    lever_bad = [
        "[hesitation] uh oh.",
        "That wasn't good.",
        "[sigh] ...",
        "What happened to the lights?",
    ]
    for i, txt in enumerate(lever_bad):
        p = gen_bark(txt, f"lever_bad_{i}")
        convert_to_ogg(p, f"lever_bad_{i}")

    lever_good = [
        "That's better.",
        "Alright.",
        "[gasps] much better."
    ]
    for i, txt in enumerate(lever_good):
        p = gen_bark(txt, f"lever_good_{i}")
        convert_to_ogg(p, f"lever_good_{i}")

    # 4. SFX (AudioLDM2)
    # Train Rumble (Earthquake style)
    p = gen_ldm("deep tectonic earthquake rumbling, massive low frequency vibration, heavy sub-bass roar, growing earth tremor, no high frequencies", "train_rumble", duration=15.0)
    convert_to_ogg(p, "train_rumble", lowpass=200)

    # Sleep Sounds
    p = gen_ldm("person sleeping, snoring, heavy breathing, mumbling about the moon", "sleep_sounds", duration=15.0)
    convert_to_ogg(p, "sleep_sounds")

    # Elevator Klonk
    p = gen_ldm("heavy rusty metallic clonk, industrial machinery latching, heavy impact, reverb", "elevator_klonk", duration=2.0)
    convert_to_ogg(p, "elevator_klonk")

    # Crusher
    p = gen_ldm("broken industrial rock crusher engine sputtering, stalling, metallic grinding, mechanical failure", "crusher_broken", duration=5.0)
    convert_to_ogg(p, "crusher_broken")

if __name__ == "__main__":
    main()
