import os
import sys
import torch

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from diffusers import FluxPipeline

# Constants
BASE_DIR = "images/base"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
TORCH_DTYPE = torch.bfloat16
MODEL_ID = "black-forest-labs/FLUX.1-schnell"

if not os.path.exists(BASE_DIR):
    os.makedirs(BASE_DIR)

def get_flux():
    print(f"Loading FLUX.1 [schnell] on {DEVICE}...")
    pipe = FluxPipeline.from_pretrained(
        MODEL_ID, 
        torch_dtype=TORCH_DTYPE
    )
    pipe.enable_model_cpu_offload()
    return pipe

def main():
    # Prompt templates for different perspectives
    prompts = [
        "Wide shot of enormous 1950s brutalist moon base, concrete and chrome, lunar surface, distant earth, cinematic sci-fi.",
        "High-altitude aerial view of sprawling brutalist lunar station, cratered moon landscape, 1950s retro-futurism, vast scale.",
        "Close-up of massive reinforced glass observation dome on moon base, frost on edges, 1950s industrial detail, stars.",
        "Distant view of glowing moon base at night, sapphire blue reactor light leaking, harsh shadows, crater rim, noir.",
        "Close-up of heavy chrome airlock doors, bolted steel, 1950s brutalist architecture, lunar dust, high detail.",
        "Low-angle shot of towering communications antennas on moon base, pointing to earth, brutalist concrete, cinematic.",
        "View from crater ridge of enormous lunar station, industrial 1950s design, fleet of rockets nearby, majestic.",
        "Close-up of base exterior, rusted steel girders, rivets, brutalist form, harsh lunar sun, 35mm film grain."
    ]

    # Expand to 32 by using variations/seeds
    all_prompts = []
    for p in prompts:
        for v in range(4):
            all_prompts.append(f"{p} variation {v}")

    # Generate the descriptions file
    with open("basedesc.md", "w") as f:
        f.write("# Moon Base Exterior Photo Descriptions\n\n")
        for i, p in enumerate(all_prompts):
            f.write(f"## Photo {i:02d}\n")
            f.write(f"{p}\n\n")

    pipe = get_flux()
    
    for i, prompt in enumerate(all_prompts):
        name = f"base_photo_{i:02d}"
        output_path = os.path.join(BASE_DIR, f"{name}.png")
        prompt_path = os.path.join(BASE_DIR, f"{name}.txt")
        
        if os.path.exists(output_path):
            continue

        print(f"Generating Base Photo {i+1}/32: {name}...")
        image = pipe(
            prompt,
            num_inference_steps=4, # FLUX schnell is optimized for 4 steps
            guidance_scale=0.0,
            width=1024,
            height=768,
            max_sequence_length=256
        ).images[0]

        image.save(output_path)
        with open(prompt_path, "w") as pf:
            pf.write(f"Model: {MODEL_ID}\nPrompt: {prompt}\n")

    print("\nAll base photos and descriptions generated successfully!")

if __name__ == "__main__":
    main()
