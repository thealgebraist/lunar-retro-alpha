import os
import sys
import torch
import subprocess

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from diffusers import FluxPipeline

# Constants
IMAGE_DIR = "images"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
# Flux.1-schnell is heavy, we use bfloat16 for better memory efficiency
TORCH_DTYPE = torch.bfloat16

if not os.path.exists(IMAGE_DIR):
    os.makedirs(IMAGE_DIR)

def get_flux():
    print(f"Loading FLUX.1 [schnell] on {DEVICE}...")
    # Use FluxPipeline for FLUX.1 [schnell]
    # This might take a while to download/load
    pipe = FluxPipeline.from_pretrained(
        "black-forest-labs/FLUX.1-schnell", 
        torch_dtype=TORCH_DTYPE
    )
    pipe.enable_model_cpu_offload() # Helpful for lower VRAM/Memory environments
    return pipe

def main():
    locations = {
        "observation_dome": "Empty 1950s retro-futuristic space station observation dome, no people, massive circular reinforced glass windows looking out at a barren cratered moon surface, starry black space, eerie dramatic lighting, cinematic, high detail, masterpiece",
        "comms_array": "Retro-futuristic 1950s radio communication room, walls of buzzing vacuum tube cabinets, glowing dials, mechanical teletype machines, thick cables on floor, industrial sci-fi, cinematic",
        "security_hub": "1950s sci-fi security control room, flickering CRT monitors, banks of clicking relay switches, heavy steel furniture, dimly lit with red emergency lights, retro-tech",
        "elevator_lobby_alpha": "Grand industrial elevator lobby in a moon base, 1950s brutalist architecture, heavy brass elevator doors, flickering fluorescent lights, shadows, cinematic film noir",
        "mess_hall": "Abandoned 1950s space station cafeteria, plastic trays, round chrome tables, tinny intercom on wall, eerie silence, dust motes in light beams, retro-futurism",
        "sleeping_pods": "Cramped 1950s lunar sleeping quarters, metallic bunks, thin padded walls, small porthole window, claustrophobic industrial sci-fi",
        "medical_lab": "Cold 1950s lunar medical infirmary, stainless steel tables, glass vials, bubbling chemical canisters, sterile but aged, high contrast lighting",
        "elevator_lobby_beta": "Dank mechanical elevator basement, hydraulic pumps, exposed pipes, oily floors, heavy industrial machinery, 1950s retro-futurism",
        "main_reactor": "Massive 1950s nuclear fusion reactor core, pulsing blue light, sparking electrical coils, heavy lead shielding, gargantuan scale, cinematic",
        "fuel_storage": "Hollow echoing fuel depot on a moon base, giant spherical tanks, metal catwalks, cold blue shadows, 1950s sci-fi industrial",
        "battery_bank": "Electrical power storage vault, rows of massive lead-acid batteries, humming capacitors, sparking terminals, 1950s high-voltage lab",
        "maintenance_tunnels": "Cramped dark industrial maintenance tunnel, steam escaping from pipes, scuttling shadows, rusted metal gratings, 1950s retro-futuristic boiler room",
        "cargo_loading": "Large moon base cargo hangar, massive blast doors, heavy lifting cranes, crates with radioactive symbols, 1950s sci-fi warehouse",
        "oxygen_scrubbers": "Life support room with giant gurgling liquid vats, rhythmic mechanical bellows, pipes and valves, humid atmosphere, 1950s retro-tech",
        "launch_control": "Empty and abandoned 1950s lunar launch control center, no people, dusty consoles with glowing nixie tubes, radar screens, an intricate miniature model of an escape pod on a central table, dramatic lighting, cinematic masterpiece",
        "escape_pod": "Interior of a small 1950s escape pod, padded circular walls, many toggle switches and analog gauges, single flickering light, claustrophobic",
        "main_reactor": "Interior of a moon base power station, a massive thick lead-glass window looking into a deep pool of glowing blue water, the submerged nuclear reactor core emits a steady sapphire Cherenkov glow, no sparks, silent and powerful, cinematic industrial sci-fi",
        "elevator_death": "Sorrowful 1950s sci-fi scene, an abandoned spacesuit in a lonely lunar corridor, fading light, peaceful but tragic cinematic ending"
    }

    pipe = get_flux()

    # 1. Generate Location Images
    for name, prompt in locations.items():
        output_path = os.path.join(IMAGE_DIR, f"{name}.png")
        prompt_path = os.path.join(IMAGE_DIR, f"{name}.txt")
        
        # Only regenerate specific ones or if file doesn't exist
        force_regenerate = name in ["launch_control", "main_reactor", "observation_dome"]
        if os.path.exists(output_path) and not force_regenerate:
            print(f"Skipping {name} (already exists)")
            continue

        print(f"Generating Image: {name}...")
        # FLUX.1 [schnell] is optimized for 4 steps
        image = pipe(
            prompt,
            num_inference_steps=4,
            guidance_scale=0.0,
            width=1024,
            height=768,
            max_sequence_length=256
        ).images[0]

        image.save(output_path)
        with open(prompt_path, "w") as f:
            f.write(f"Model: black-forest-labs/FLUX.1-schnell\nPrompt: {prompt}\n")
        print(f"Saved to {output_path}")

    # 2. Generate Toilet Images (Mines Toilet Area)
    # ...
    for name, prompt in toilet_prompts.items():
        output_path = os.path.join(IMAGE_DIR, f"{name}.png")
        prompt_path = os.path.join(IMAGE_DIR, f"{name}.txt")
        if not os.path.exists(output_path):
            print(f"Generating Toilet Image: {name}...")
            image = pipe(prompt, num_inference_steps=4, guidance_scale=0.0, width=1024, height=768).images[0]
            image.save(output_path)
            with open(prompt_path, "w") as f:
                f.write(f"Model: black-forest-labs/FLUX.1-schnell\nPrompt: {prompt}\n")

    # 16 variations of flushing
    for i in range(16):
        name = f"toilet_flush_{i}"
        output_path = os.path.join(IMAGE_DIR, f"{name}.png")
        prompt_path = os.path.join(IMAGE_DIR, f"{name}.txt")
        if os.path.exists(output_path):
            continue
        
        print(f"Generating Toilet Flush Variation: {i}...")
        flush_prompt = f"1950s retro-futuristic lunar mine toilet flushing with swirling water, industrial metallic commode, rapid water movement, bubbles, cramped steel cubicle, cinematic lighting, variation {i}"
        image = pipe(flush_prompt, num_inference_steps=4, guidance_scale=0.0, width=1024, height=768).images[0]
        image.save(output_path)
        with open(prompt_path, "w") as f:
            f.write(f"Model: black-forest-labs/FLUX.1-schnell\nPrompt: {flush_prompt}\n")

    print("\nAll images generated successfully!")

if __name__ == "__main__":
    main()
