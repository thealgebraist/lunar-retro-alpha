import os
import sys
import torch

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from diffusers import FluxPipeline

# Constants
CLOSEUP_DIR = "images/closeups"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
TORCH_DTYPE = torch.bfloat16
MODEL_ID = "black-forest-labs/FLUX.1-schnell"

if not os.path.exists(CLOSEUP_DIR):
    os.makedirs(CLOSEUP_DIR)

def get_flux():
    print(f"Loading FLUX.1 [schnell] on {DEVICE}...")
    pipe = FluxPipeline.from_pretrained(
        MODEL_ID, 
        torch_dtype=TORCH_DTYPE
    )
    pipe.enable_model_cpu_offload()
    return pipe

def main():
    # Object data mapping for prompt generation
    objects = [
        {
            "name": "control_board",
            "prompt": "Extreme close-up of a 1950s retro-futuristic electronic control board, glowing vacuum tubes, complex colorful wiring, gold contacts, dusty glass, cinematic lighting.",
            "location": "Communications Array (Item)"
        },
        {
            "name": "battery",
            "prompt": "Close-up of a heavy lead-lined cylindrical battery cell, pulsing with a sapphire blue sapphire light, metallic finish, labeled 'LUNAR-CORE TYPE 4', 1950s industrial.",
            "location": "Sleeping Pods (Item)"
        },
        {
            "name": "airlock_wheel",
            "prompt": "Close-up of a heavy cast-iron emergency airlock wheel, painted red, bolted to a thick glass dome, frost patterns on the metal, 1950s brutalist moon base.",
            "location": "Observation Dome"
        },
        {
            "name": "nixie_tubes",
            "prompt": "Macro shot of a row of glowing nixie tubes displaying orange numbers, dark industrial console background, 1950s retro-tech, warm bokeh.",
            "location": "Launch Control / Security Hub"
        },
        {
            "name": "industrial_lever",
            "prompt": "Close-up of a massive industrial steel lever mounted on a rough rock wall, heavy mechanical gears, oily sheen, 1950s mining equipment.",
            "location": "Mine Storage"
        },
        {
            "name": "tape_recorder",
            "prompt": "Close-up of a 1950s reel-to-reel tape recorder on a wooden desk, magnetic tape spinning, chrome switches, grainy shadows, cinematic sci-fi noir.",
            "location": "Mine Work Room"
        },
        {
            "name": "crt_monitor",
            "prompt": "Close-up of a grainy curved CRT monitor screen showing a green-tinted camera feed of a lunar corridor, scanlines, plastic housing, 1950s tech.",
            "location": "Security Hub"
        },
        {
            "name": "elevator_button",
            "prompt": "Close-up of a single circular brass elevator button labeled 'LOWER LEVELS' in a retro font, recessed in a brushed aluminum panel, fingerprint smudges, 1950s industrial.",
            "location": "Elevator Lobbies"
        },
        {
            "name": "surgical_lamp",
            "prompt": "Close-up of a large multi-bulb stainless steel surgical lamp, bright cold white light, glass lenses, 1950s lunar medical infirmary atmosphere.",
            "location": "Medical Lab"
        },
        {
            "name": "algae_cylinder",
            "prompt": "Close-up of a giant glass cylinder filled with bubbling thick green algae, internal lights illuminating the water, metal clamps and pipes, 1950s life support.",
            "location": "Oxygen Scrubbers"
        },
        {
            "name": "yellow_forklift",
            "prompt": "Close-up of the front of a heavy yellow industrial forklift, worn tires, hydraulic pistons, massive lunar cargo hangar in background, 1950s design.",
            "location": "Cargo Loading"
        },
        {
            "name": "mining_pickaxe",
            "prompt": "Close-up of a heavy industrial pickaxe resting on a wooden crate, rusted steel head, lunar dust, 1950s mining area, harsh lighting.",
            "location": "Mine Storage"
        },
        {
            "name": "bunk_beds",
            "prompt": "Close-up of triple-stacked metallic bunk beds carved into moon rock, thin mattresses, quilted blankets, 1950s lunar living quarters.",
            "location": "Bunk Room"
        },
        {
            "name": "reading_lamp",
            "prompt": "Close-up of a small articulated metal reading lamp, warm incandescent glow, reflecting off a stack of aged magazines, 1950s retro interior.",
            "location": "Bunk Room"
        },
        {
            "name": "blueprints",
            "prompt": "Close-up of large blue blueprints spread on a grimy floor, showing technical drawings of a moon base, technical annotations, 1950s engineering.",
            "location": "Mine Work Room"
        },
        {
            "name": "quilted_padding",
            "prompt": "Macro shot of silver quilted metallic padding on an elevator wall, heavy industrial stitching, shadows, 1950s space station aesthetic.",
            "location": "Elevator Interior / Escape Pod"
        }
    ]

    pipe = get_flux()

    for obj in objects:
        name = obj["name"]
        prompt = obj["prompt"]
        output_path = os.path.join(CLOSEUP_DIR, f"{name}.png")
        prompt_path = os.path.join(CLOSEUP_DIR, f"{name}.txt")
        
        if os.path.exists(output_path):
            print(f"Skipping {name} (already exists)")
            continue

        print(f"Generating Closeup: {name} (Location: {obj['location']})...")
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
            f.write(f"Model: {MODEL_ID}\nLocation: {obj['location']}\nPrompt: {prompt}\n")
        print(f"Saved to {output_path}")

    print("\nAll object closeups generated successfully!")

if __name__ == "__main__":
    main()
