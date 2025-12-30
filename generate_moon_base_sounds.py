import torch
from diffusers import AudioLDMPipeline
import scipy.io.wavfile
import numpy as np
import os

def main():
    # Setup
    model_id = "cvssp/audioldm-s-full-v2"
    device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
    print(f"Loading {model_id} on {device}...")
    
    pipe = AudioLDMPipeline.from_pretrained(model_id, torch_dtype=torch.float16).to(device)
    
    os.makedirs("moon_base_assets", exist_ok=True)
    
    # Location sounds (10 seconds each)
    locations = {
        "observation_dome": "Thin, whistling wind from a micro-leak in a space station; the faint, rhythmic ticking of a mechanical clock, 1950s retro-futurism, eerie silence",
        "comms_array": "Harsh static hiss and electronic hum of a 1950s radio room; the rhythmic thwack-thwack of a teletype machine, buzzing cabinets",
        "security_hub": "Low-frequency buzz of a heavy-duty electric transformer; clicking and clacking of relay switches and mechanical dials",
        "elevator_lobby_alpha": "Distant, echoing metallic groan from an old elevator shaft; the low hum of a waiting lift, industrial ambiance",
        "mess_hall": "Occasional plink of water hitting a metal tray; ghostly, distorted recording of 1950s lounge music playing through a tinny intercom, empty cafeteria",
        "sleeping_pods": "Soft, rhythmic wheezing from an old ventilation fan; the crinkle of metallic blankets, quiet breathing, sleeping quarters",
        "medical_lab": "Steady, high-pitched drip of a chemical valve; glass-on-glass clatter of vials and test tubes, sterile but old laboratory",
        "elevator_lobby_beta": "Rhythmic thumping of a hydraulic pump; buzzing of a flickering fluorescent light, mechanical basement",
        "main_reactor": "Deep, bone-shaking sub-bass thrum of a nuclear reactor; crackle of static electricity jumping between coils, massive energy",
        "fuel_storage": "Hollow echoes of footsteps on metal grating; low moan of expanding metal pipes in a cold storage room",
        "battery_bank": "High-pitched electronic whine of capacitors charging; rhythmic electrical pulses, power storage room",
        "maintenance_tunnels": "Scuttling of small metal robots on metal pipes; hiss of escaping steam, cramped industrial tunnel",
        "cargo_loading": "Wind howling against large metal hangar doors; groaning of stressed metal beams, large empty warehouse",
        "oxygen_scrubbers": "Deep, wet gurgling of liquid in large tanks; rhythmic puffing and blowing of a large bellows, life support",
        "launch_control": "Frantic clicking of a Geiger counter; steady electronic beep of a countdown timer, tense control room",
        "escape_pod": "Dead silence in a small metallic cabin, occasional faint electrical hum"
    }
    
    # Trigger samples (5 seconds each)
    triggers = {
        "comms_uplink_chirp": "A sequence of high-pitched melodic electronic pings, futuristic 1950s computer sound",
        "door_bolt_retract": "A heavy mechanical metal clunk followed by a short pneumatic hiss, vault door opening",
        "reactor_ignition_roar": "A rising electronic whine ending in a thunderous power-on hum and roar, machine starting up",
        "pod_systems_active": "Series of rapid electronic beeps followed by a smooth turbine engine spooling up"
    }
    
    negative_prompt = "low quality, noise, speech, humming, music"
    
    # Generate Location Sounds
    for name, prompt in locations.items():
        output_file = f"moon_base_assets/{name}.wav"
        if os.path.exists(output_file):
            print(f"Skipping {output_file} (already exists)")
            continue
            
        print(f"Generating location: {name}...")
        audio = pipe(
            prompt,
            negative_prompt=negative_prompt if name != "mess_hall" else "low quality, noise, speech", # Allow music for mess hall
            num_inference_steps=30,
            audio_length_in_s=10.0
        ).audios[0]
        
        scipy.io.wavfile.write(output_file, 16000, (audio * 32767).astype(np.int16))

    # Generate Trigger Samples
    for name, prompt in triggers.items():
        output_file = f"moon_base_assets/{name}.wav"
        if os.path.exists(output_file):
            print(f"Skipping {output_file} (already exists)")
            continue

        print(f"Generating trigger: {name}...")
        audio = pipe(
            prompt,
            negative_prompt=negative_prompt,
            num_inference_steps=30,
            audio_length_in_s=5.0
        ).audios[0]
        
        scipy.io.wavfile.write(output_file, 16000, (audio * 32767).astype(np.int16))

    print("All sounds generated in 'moon_base_assets/'")

if __name__ == "__main__":
    main()
