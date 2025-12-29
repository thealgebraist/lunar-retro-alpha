import torch
from diffusers import AudioLDM2Pipeline
import scipy.io.wavfile
import numpy as np
import os
import subprocess

def main():
    model_id = "cvssp/audioldm2-large"
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    # AudioLDM2 Large is heavy, use float16 on MPS
    from transformers import GPT2LMHeadModel
    
    # Workaround for GPT2Model vs GPT2LMHeadModel issue
    lang_model = GPT2LMHeadModel.from_pretrained("cvssp/audioldm2-large", subfolder="language_model", torch_dtype=torch.float16 if device == "mps" else torch.float32)
    
    pipe = AudioLDM2Pipeline.from_pretrained(
        model_id, 
        language_model=lang_model,
        torch_dtype=torch.float16 if device == "mps" else torch.float32
    ).to(device)
    
    os.makedirs("moon_base_assets_hq", exist_ok=True)
    
    # Define all prompts
    sounds = {
        # Backgrounds (10s)
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
        
        # Triggers (5s)
        "comms_uplink_chirp": "Sequence of high-pitched melodic electronic computer pings",
        "door_bolt_retract": "Heavy mechanical metal clunk, pneumatic hiss, vault door opening",
        "reactor_ignition_roar": "Rising electronic whine ending in a thunderous power-on hum",
        "pod_systems_active": "Rapid electronic beeps followed by a smooth turbine engine spool-up",
        "elevator_move": "Deep metallic vibration, heavy gears turning, industrial lift movement",
        "item_pickup": "Sharp mechanical click, short electronic hum",
        "puzzle_success": "Satisfying 50s-style three-note melodic chime, relay click",
        "airlock_hiss": "Sudden burst of high-pressure air, heavy mechanical seal locking",
        "battery_insert": "Heavy mechanical clunk, rising electrical buzz",
        
        # Specials (30s / 8s)
        "intro_synth": "Eerie mysterious 1950s space synth, pulsing drones, shimmering analog oscillations",
        "ending_synth": "Heroic triumphant 1950s sci-fi ending theme, triumphant analog brass and pads",
        "backstory": "Dramatic sci-fi film intro, low brass hits, rising orchestral tension, 1950s cinematic"
    }

    negative_prompt = "low quality, noise, speech, drums, distorted"

    for name, prompt in sounds.items():
        output_wav = f"moon_base_assets_hq/{name}.wav"
        output_ogg = f"moon_base_assets/{name}.ogg"
        
        if os.path.exists(output_ogg):
            print(f"Skipping {name} (already exists in OGG)")
            continue

        print(f"Generating HQ: {name}...")
        
        duration = 10.0
        if name in ["intro_synth", "ending_synth"]: duration = 30.0
        if name == "backstory": duration = 8.0
        if name in ["comms_uplink_chirp", "door_bolt_retract", "item_pickup", "puzzle_success", "airlock_hiss", "battery_insert"]: duration = 5.0

        audio = pipe(
            prompt,
            negative_prompt=negative_prompt,
            num_inference_steps=30, # AudioLDM2 is slow, 30 steps is usually enough for HQ
            audio_length_in_s=duration
        ).audios[0]

        # Normalize
        rms = np.sqrt(np.mean(audio**2))
        target_rms = 10**(-18.0 / 20)
        audio = audio * (target_rms / rms)
        peak = np.max(np.abs(audio))
        if peak > 0.95: audio = audio * (0.95 / peak)

        # Loopable processing for backgrounds
        if duration >= 10.0 and name not in ["ending_synth", "backstory"]:
            sample_rate = 16000
            fade_samples = int(2.0 * sample_rate)
            start_fade = audio[:fade_samples]
            end_fade = audio[-fade_samples:]
            middle = audio[fade_samples:-fade_samples]
            alpha = np.linspace(0, 1, fade_samples)
            blended = end_fade * (1 - alpha) + start_fade * alpha
            audio = np.concatenate([blended, middle])

        scipy.io.wavfile.write(output_wav, 16000, (audio * 32767).astype(np.int16))
        
        # Convert to OGG
        subprocess.run(['ffmpeg', '-y', '-i', output_wav, '-c:a', 'libvorbis', '-q:a', '6', output_ogg], 
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    print("All HQ sounds generated and converted.")

if __name__ == "__main__":
    main()
