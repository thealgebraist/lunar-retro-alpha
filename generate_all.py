import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

try:
    from transformers import AutoProcessor, BarkModel
    try:
        from diffusers import TangoFluxPipeline
        USE_DIFFUSERS_TANGO = True
    except ImportError:
        from tangoflux import TangoFluxInference
        USE_DIFFUSERS_TANGO = False
except ImportError as e:
    print(f"Warning: Could not import some libraries: {e}")
    print("This script requires 'tangoflux' or 'diffusers>=0.31.0' and 'transformers'.")

# Constants
HQ_DIR = "moon_base_assets_hq"
GAME_DIR = "moon_base_assets"
NUMBERS_HQ = os.path.join(HQ_DIR, "numbers")
NUMBERS_GAME = os.path.join(GAME_DIR, "numbers")

# Mac M1/M2/M3 usually prefers "mps", but TangoFlux might require CUDA or CPU for now
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
# TangoFlux prefers bfloat16 on CUDA, float32 on MPS/CPU
TORCH_DTYPE = torch.bfloat16 if DEVICE == "cuda" else torch.float32

if not os.path.exists(HQ_DIR):
    os.makedirs(HQ_DIR)
if not os.path.exists(GAME_DIR):
    os.makedirs(GAME_DIR)
if not os.path.exists(NUMBERS_HQ):
    os.makedirs(NUMBERS_HQ)
if not os.path.exists(NUMBERS_GAME):
    os.makedirs(NUMBERS_GAME)

# Models
bark_processor = None
bark_model = None
tango_model = None

def get_bark():
    global bark_processor, bark_model
    if bark_model is None:
        print("Loading Bark Large...")
        bark_processor = AutoProcessor.from_pretrained("suno/bark")
        bark_model = BarkModel.from_pretrained("suno/bark").to(DEVICE)
    return bark_processor, bark_model

def get_tango():
    global tango_model
    if tango_model is None:
        print("Loading TangoFlux...")
        if USE_DIFFUSERS_TANGO:
            tango_model = TangoFluxPipeline.from_pretrained("declare-lab/TangoFlux", torch_dtype=TORCH_DTYPE).to(DEVICE)
        else:
            tango_model = TangoFluxInference(name="declare-lab/TangoFlux", device=DEVICE)
    return tango_model

def gen_bark(text, filename, preset="v2/en_speaker_6", target_dir=HQ_DIR):
    print(f"Generating Bark (Voice): {filename} in {target_dir}...")
    processor, model = get_bark()
    inputs = processor(text, voice_preset=preset)
    with torch.no_grad():
        audio_array = model.generate(**inputs.to(DEVICE))
        audio_array = audio_array.cpu().numpy().squeeze()
    
    wav_path = os.path.join(target_dir, filename + ".wav")
    scipy.io.wavfile.write(wav_path, rate=model.generation_config.sample_rate, data=audio_array)
    return wav_path

def gen_tango(prompt, filename, duration=10.0, steps=25):
    print(f"Generating TangoFlux (SFX): {filename}...")
    model = get_tango()
    
    if USE_DIFFUSERS_TANGO:
        audio = model(prompt, num_inference_steps=steps, duration=duration).audios[0]
    else:
        # TangoFluxInference.generate returns a torch tensor [channels, samples]
        audio_tensor = model.generate(prompt, steps=steps, duration=duration)
        audio = audio_tensor.float().cpu().numpy()
        # If it's [channels, samples], and we want [samples] or similar
        if audio.ndim > 1:
            # Most diffusers output is mono or interleaved? 
            # TangoFlux output is usually [1, samples] or [2, samples]
            # soundfile/scipy expects [samples, channels]
            audio = audio.T
    
    # Normalize
    # Calculate RMS on the numpy array
    rms = np.sqrt(np.mean(audio**2))
    target_rms = 10**(-18.0 / 20)
    if rms > 0:
        audio = audio * (target_rms / (rms + 1e-9))
    peak = np.max(np.abs(audio))
    if peak > 0.95: 
        audio = audio * (0.95 / peak)

    # Loopable processing for long backgrounds
    if duration >= 15.0 and filename not in ["ending_synth", "backstory", "intro_synth"]:
        sample_rate = 44100 
        fade_samples = int(4.0 * sample_rate) # Use 4s fade for smoother 30s loops
        if len(audio) > fade_samples * 2:
            # Assuming mono for simplicity of blending logic if it was flattened or just take first channel
            if audio.ndim > 1:
                start_fade = audio[:fade_samples, :]
                end_fade = audio[-fade_samples:, :]
                middle = audio[fade_samples:-fade_samples, :]
                alpha = np.linspace(0, 1, fade_samples)[:, np.newaxis]
                blended = end_fade * (1 - alpha) + start_fade * alpha
                audio = np.concatenate([blended, middle])
            else:
                start_fade = audio[:fade_samples]
                end_fade = audio[-fade_samples:]
                middle = audio[fade_samples:-fade_samples]
                alpha = np.linspace(0, 1, fade_samples)
                blended = end_fade * (1 - alpha) + start_fade * alpha
                audio = np.concatenate([blended, middle])

    wav_path = os.path.join(HQ_DIR, filename + ".wav")
    # TangoFlux output is 44100Hz
    scipy.io.wavfile.write(wav_path, rate=44100, data=(audio * 32767).astype(np.int16))
    return wav_path

def convert_to_ogg(wav_path, ogg_name, quality=6, target_dir=GAME_DIR):
    print(f"Converting to {ogg_name}.ogg in {target_dir}...")
    ogg_path = os.path.join(target_dir, ogg_name + ".ogg")
    subprocess.run(['ffmpeg', '-y', '-i', wav_path, '-c:a', 'libvorbis', '-q:a', str(quality), ogg_path], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def mix_tape_log():
    print("Mixing Tape Log...")
    # Generate Voice
    voice_path = gen_bark(
        "[sigh] Log entry 4-1-2. We were hit. That meteor shower... it came out of nowhere. [pause] Hull breach in sector 7. Things went downhill fast. Life support is failing. [static] Everyone... disappeared into the tunnels. I'm the only one left.", 
        "tape_voice_raw"
    )
    # Generate BG
    bg_path = gen_tango("space station background humming, distant heavy explosions, metallic crashing, eerie silence", "tape_bg_raw", duration=20.0)
    
    final_wav = os.path.join(HQ_DIR, "tape_log.wav")
    # Mix with filters
    filter_complex = "[0:a]highpass=f=300,lowpass=f=3000,vibrato=f=6:d=0.1,volume=2.5[v];[1:a]volume=0.6[bg];[v][bg]amix=inputs=2:duration=first[out]"
    
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
    # 1. Backgrounds (10s)
    backgrounds = {
        "observation_dome": "Eerie whistling wind from a micro-leak in a glass dome, faint rhythmic mechanical clock ticking, 1950s space station ambiance",
        "comms_array": "Buzzing vacuum tube cabinets, harsh static hiss modulating, rhythmic thwack of a teletype machine",
        "security_hub": "Low frequency electrical hum of a heavy transformer, clicking relay switches, flickering CRT buzz",
        "elevator_lobby_alpha": "Distant echoing metallic groan from a lift shaft, industrial hum, cavernous acoustics",
        "mess_hall": "Ghostly distorted 1950s lounge music through a tinny intercom, occasional water drip on metal",
        "sleeping_pods": "Soft rhythmic wheezing of an old ventilation fan, crinkle of metallic blankets, quiet breathing",
        "medical_lab": "High pitched chemical valve drip, glass clattering softly, sterile electronic hum",
        "elevator_lobby_beta": "Rhythmic thumping of a hydraulic pump, buzzing flickering fluorescent light",
        "main_reactor": "Deep bone-shaking sub-bass thrum of a nuclear core, static electricity crackle",
        "fuel_storage": "Hollow echoing footsteps on metal grating, low moan of cold expanding pipes",
        "battery_bank": "Deep industrial humming, oscillating electrical thrum, low frequency pulses",
        "maintenance_tunnels": "Scuttling of small robots on metal, hiss of escaping steam, cramped acoustics",
        "cargo_loading": "Howling wind against heavy hangar doors, groaning stressed metal beams",
        "oxygen_scrubbers": "Deep wet gurgling of liquid tanks, rhythmic puffing of large bellows",
        "launch_control": "Frantic clicking of a geiger counter, steady electronic countdown beep",
        "escape_pod": "Loud steady mechanical whirring, spaceship ventilation fan, small padded cabin acoustics",
        "elevator_approach": "Distant low-frequency industrial drone slowly getting louder, mechanical vibration",
        "elevator_moving": "Heavy industrial lift moving, rattling chains, grinding gears, low frequency thrum",
        "elevator_death": "Sorrowful cinematic 1950s strings, low dark cello, peaceful but lonely ending theme"
    }

    # 2. SFX Triggers (2-5s)
    triggers = {
        "comms_uplink_chirp": "Sequence of high-pitched melodic electronic computer pings",
        "door_bolt_retract": "Heavy mechanical metal clunk, pneumatic hiss, vault door opening",
        "reactor_ignition_roar": "Rising electronic whine ending in a thunderous power-on hum",
        "pod_systems_active": "Rapid electronic beeps followed by a smooth turbine engine spool-up",
        "elevator_move": "Deep metallic vibration, heavy gears turning, industrial lift movement",
        "item_pickup": "Sharp mechanical click, short electronic hum",
        "puzzle_success": "Satisfying 50s-style three-note melodic chime, relay click",
        "airlock_hiss": "Sudden burst of high-pressure air, heavy mechanical seal locking",
        "battery_insert": "Heavy mechanical clunk, rising electrical buzz",
        "alien_death": "Growling combination of goat horse elephant car lion robot all mixed together with a loud trumpet sound",
        "airlock_rotate": "Heavy mechanical metal rotation, grinding gears, industrial airlock turning",
        "airlock_suck": "Powerful vacuum suction sound, air rushing out of a chamber, metallic resonance",
        "alien_sonar": "Pulsing organic clicking sound, echo-location pings, eerie alien presence",
        "lever_clonk": "Heavy industrial lever being thrown, metallic clonk and snap",
        "drawer_open": "Rusty metal drawer sliding open, screeching and rattling",
        "elevator_klonk": "Heavy metallic klonk, rusty screeching door opening, pneumatic air release",
        "crusher_broken": "Broken industrial rock crusher engine sputtering, stalling, metallic grinding, mechanical failure",
        "terminal_tick": "Single sharp mechanical typewriter tick, electronic high-frequency click, Alien movie computer style, short and crisp",
        "airlock_death": "Decompression explosive hiss, sudden rush of air, metallic katchong clunk followed by eerie silence",
        "airlock_death_seq": "Decompression explosive hiss, sudden rush of air, metallic katchong clunk followed by eerie silence",
        "elevator_button": "Heavy 1950s industrial push button click, mechanical snap"
    }

    # 3. Special Long SFX
    specials = {
        "intro_synth": ("Eerie mysterious 1950s space synth, pulsing drones, shimmering analog oscillations", 30.0),
        "ending_synth": ("Heroic triumphant 1950s sci-fi ending theme, triumphant analog brass and pads", 30.0),
        "backstory": ("Dramatic sci-fi film intro, low brass hits, rising orchestral tension, 1950s cinematic", 8.0),
        "train_rumble": ("Deep tectonic earthquake rumbling, massive low frequency vibration, heavy sub-bass roar", 15.0),
        "sleep_sounds": ("Person sleeping, snoring, heavy breathing, mumbling about the moon", 15.0)
    }

    # 4. Voices (Announcements & Countdown)
    announcements = {
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

    # 5. Reactions & Lever Feedback
    reactions = {
        "reaction_0": "[hesitation] What was that?",
        "reaction_1": "What in the...",
        "reaction_2": "I wonder what that is.",
        "reaction_3": "What in the world just happened?",
        "reaction_4": "I hope this place doesn't collapse.",
        "reaction_5": "Is that dust coming from the ceiling?!",
        "reaction_6": "Wow.",
        "lever_bad_0": "[hesitation] uh oh.",
        "lever_bad_1": "That wasn't good.",
        "lever_bad_2": "[sigh] ...",
        "lever_bad_3": "What happened to the lights?",
        "lever_good_0": "That's better.",
        "lever_good_1": "Alright.",
        "lever_good_2": "[gasps] much better."
    }

    # Generation Execution
    # SFX - TangoFlux
    for name, prompt in backgrounds.items():
        wav = gen_tango(prompt, name, duration=30.0)
        convert_to_ogg(wav, name)

    for name, prompt in triggers.items():
        duration = 1.0 if name == "terminal_tick" else 2.0 if name in ["elevator_button", "lever_clonk", "drawer_open"] else 5.0
        wav = gen_tango(prompt, name, duration=duration)
        convert_to_ogg(wav, name)

    for name, (prompt, dur) in specials.items():
        wav = gen_tango(prompt, name, duration=dur)
        convert_to_ogg(wav, name)

    # Voices - Bark Large
    for name, text in announcements.items():
        # Announcements use a more official/PA system voice preset if possible
        wav = gen_bark(text, name, preset="v2/en_speaker_9")
        convert_to_ogg(wav, name)

    for name, text in reactions.items():
        # Reactions use a more expressive voice
        wav = gen_bark(text, name, preset="v2/en_speaker_6")
        convert_to_ogg(wav, name)

    # Mixed Tape Log
    mix_tape_log()

    # 6. Numbers, Percentages and Units (Robotic Voice)
    print("Generating Numeric and Unit Library...")
    
    # Numbers 1..200
    for i in range(1, 201):
        name = f"number_{i}"
        wav = gen_bark(str(i), name, preset="v2/en_speaker_9", target_dir=NUMBERS_HQ)
        convert_to_ogg(wav, name, target_dir=NUMBERS_GAME)
    
    # "point"
    wav = gen_bark("point", "point", preset="v2/en_speaker_9", target_dir=NUMBERS_HQ)
    convert_to_ogg(wav, "point", target_dir=NUMBERS_GAME)
    
    # Percentages 0%, 5% .. 100%
    for i in range(0, 101, 5):
        name = f"percent_{i}"
        text = f"{i} percent"
        wav = gen_bark(text, name, preset="v2/en_speaker_9", target_dir=NUMBERS_HQ)
        convert_to_ogg(wav, name, target_dir=NUMBERS_GAME)
        
    # Units
    units = {
        "kg": "kilograms",
        "kilogram": "kilogram",
        "kilograms": "kilograms",
        "ton": "ton",
        "tons": "tons",
        "celsius": "degrees celsius",
        "degree": "degree",
        "degrees": "degrees",
        "ppm": "parts per million",
        "ppm_short": "P P M",
        "bar": "bar",
        "bars": "bars",
        "pascal": "pascal",
        "pascals": "pascals",
        "psi": "P S I",
        "percent": "percent"
    }
    for filename, text in units.items():
        wav = gen_bark(text, filename, preset="v2/en_speaker_9", target_dir=NUMBERS_HQ)
        convert_to_ogg(wav, filename, target_dir=NUMBERS_GAME)

    print("\nAll assets generated successfully!")

if __name__ == "__main__":
    main()
