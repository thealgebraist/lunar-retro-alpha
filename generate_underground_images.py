import os
import sys
import torch

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from diffusers import FluxPipeline

# Constants
UNDERGROUND_DIR = "images/underground"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
TORCH_DTYPE = torch.bfloat16
MODEL_ID = "black-forest-labs/FLUX.1-schnell"

if not os.path.exists(UNDERGROUND_DIR):
    os.makedirs(UNDERGROUND_DIR)

def get_flux():
    print(f"Loading FLUX.1 [schnell] on {DEVICE}...")
    pipe = FluxPipeline.from_pretrained(
        MODEL_ID, 
        torch_dtype=TORCH_DTYPE
    )
    pipe.enable_model_cpu_offload()
    return pipe

def main():
    # Room descriptions mapping for prompt generation and markdown file
    room_data = [
        {
            "name": "Mine Level: Lobby",
            "desc": "Rough hewn rock walls reinforced with rusty steel beams. The elevator shaft goes up. Dust motes dance in the air.",
            "variations": 4
        },
        {
            "name": "Mine Level: Work Room",
            "desc": "A cluttered workspace. Blueprints scattered on the floor. A heavy desk sits against the wall with a tape recorder on it. A small, pixelated picture hangs on the wall.",
            "variations": 4
        },
        {
            "name": "Mine Level: Bunk Room",
            "desc": "Cramped living quarters. Triple-stacked bunk beds. A reading lamp flickers over a pile of old magazines.",
            "variations": 4
        },
        {
            "name": "Mine Level: Showers",
            "desc": "Communal showers. The tiles are cracked and yellowed. Water drips rhythmically.",
            "variations": 4
        },
        {
            "name": "Mine Level: Toilets",
            "desc": "A row of industrial toilets. The smell is ancient and metallic.",
            "variations": 4
        },
        {
            "name": "Stone Crushing Room",
            "desc": "Dominated by a massive, silent crushing machine. Conveyor belts sit idle. A dark opening leads to the tunnels.",
            "variations": 4
        },
        {
            "name": "Deep Tunnel Entrance",
            "desc": "The lights end here. A pitch-black tunnel descends into the crust. You hear strange robotic sounds echoing from the deep.",
            "variations": 4
        },
        {
            "name": "Mine Level: Storage",
            "desc": "Crates of mining explosives and pickaxes. A massive industrial lever is mounted on the wall. A heavy blast door leads to the crushing room.",
            "variations": 4
        }
    ]

    # Generate the descriptions file
    with open("undergrounddesc.md", "w") as f:
        f.write("# Underground Mining Area Photo Descriptions\n\n")
        for room in room_data:
            f.write(f"## {room['name']}\n")
            f.write(f"{room['desc']}\n\n")

    pipe = get_flux()
    
    total_images = 0
    for room in room_data:
        for v in range(room['variations']):
            name = f"{room['name'].lower().replace(' ', '_').replace(':', '')}_v{v}"
            output_path = os.path.join(UNDERGROUND_DIR, f"{name}.png")
            prompt_path = os.path.join(UNDERGROUND_DIR, f"{name}.txt")
            
            if os.path.exists(output_path):
                print(f"Skipping {name} (already exists)")
                continue

                        # Construct prompt for Flux - shortened to avoid CLIP truncation
                        prompt = f"1950s retro-futuristic photo of lunar mine {room['name']}: {room['desc']} Cinematic, industrial sci-fi, realistic, high detail, variation {v}"
                        print(f"Generating image {total_images+1}/32: {name}...")
            image = pipe(
                prompt,
                num_inference_steps=4,
                guidance_scale=0.0,
                width=1024,
                height=768,
                max_sequence_length=256
            ).images[0]

            image.save(output_path)
            with open(prompt_path, "w") as pf:
                pf.write(f"Model: {MODEL_ID}\nPrompt: {prompt}\n")
            
            total_images += 1

    print("\nAll underground images and descriptions generated successfully!")

if __name__ == "__main__":
    main()
