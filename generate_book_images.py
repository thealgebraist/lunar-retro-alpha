import os
import sys
import torch

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

from diffusers import FluxPipeline

# Constants
BOOK_DIR = "book"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
TORCH_DTYPE = torch.bfloat16

if not os.path.exists(BOOK_DIR):
    os.makedirs(BOOK_DIR)

def get_flux():
    print(f"Loading FLUX.1 [schnell] on {DEVICE}...")
    pipe = FluxPipeline.from_pretrained(
        "black-forest-labs/FLUX.1-schnell", 
        torch_dtype=TORCH_DTYPE
    )
    pipe.enable_model_cpu_offload()
    return pipe

def main():
    # Base prompt for the book consistency
    # We describe the open book and the environment first, then the content of the pages
    base_prompt = "A high-quality close-up photograph of an old open hardcover book resting on a dark wooden table in a dimly lit library. The paper is aged and yellowed. On the open pages, there is a large, detailed black-and-white 1950s style photograph showing: "
    
    scenes = [
        "the very first foundations of the lunar observation dome being laid on the moon's cratered surface, construction cranes, astronaut workers, 1950s retro-futurism",
        "massive steel girders being welded together to form the moon base's primary skeleton, earth visible in the black sky, cinematic",
        "the completion of the main airlock, gleaming chrome and heavy bolts, retro-tech, 1950s sci-fi aesthetic",
        "a fleet of gargantuan 1950s-style rockets landing on the lunar surface, kicking up clouds of white dust, impressive scale",
        "hundreds of people in retro spacesuits disembarking from a huge rocket ship, arriving at their new lunar home, triumph",
        "families moving their belongings into the cramped but cozy sleeping pods, metallic bunks, 1950s domestic life in space",
        "the grand opening ceremony of the mess hall, scientists and workers sharing a meal, round chrome tables, 1950s optimism",
        "scientists working in the high-tech medical lab, glass vials and primitive computers, 1950s vision of the future",
        "engineers monitoring the vast array of glowing nixie tubes in the security hub, banks of switches, retro-tech",
        "miners in heavy industrial spacesuits descending into the dark, jagged entrance of the deep moon mines, 1950s industrial",
        "the high-speed lunar shuttle at a station in the mines, sleek aerodynamic 1950s design, metallic finish",
        "a blurry high-speed view from inside the lunar shuttle as it streaks through a dark tunnel, interior lights reflecting on glass",
        "the gargantuan underground fusion reactor core emitting a sapphire blue glow, seen from a high catwalk, immense scale",
        "people relaxing in the lunar vacation dome, artificial trees, a small pool, retro swimwear, 1950s luxury in space",
        "a 1950s newspaper advertisement with the headline 'YOUR NEW HOME ON THE MOON!', showing a stylized drawing of the base",
        "a colorized postcard showing the moon base glowing like a jewel in the dark lunar night, 'Greetings from Tycho Base'",
        "heavy drilling machinery extracting rare minerals from the lunar rock, sparks and dust, industrial masterpiece",
        "a panoramic view of the completed moon base under the dome, a sprawling 1950s city of the future",
        "the first lunar gardens, hydroponic rows of green plants under artificial lights, 1950s agricultural science",
        "a 1950s style technical blueprint of the base spread across the book's pages, detailed annotations, engineering",
        "a group of children looking out of the observation dome at the distant blue earth, wonder and awe",
        "the massive cargo hangar filled with crates and heavy lifting equipment, 1950s space logistics",
        "an intricate miniature model of the entire station on a display stand, 1950s museum exhibit",
        "the station's mainframe computer room, walls of spinning tape reels and blinking lights, retro-computing",
        "a 1950s comic book cover titled 'ADVENTURE ON THE MOON!', featuring the station and a brave astronaut",
        "the first lunar vehicle, a bulky 6-wheeled rover exploring a deep crater, 1950s exploration",
        "the communications array antennas pointing towards earth, harsh shadows and bright highlights, 1950s sci-fi",
        "a close-up of a worker's hand holding a piece of glowing lunar ore, industrial glove, cinematic",
        "the fuel storage depot with spherical tanks and metal catwalks, cold blue industrial lighting",
        "a crowded elevator lobby during a shift change, people in functional jumpsuits, 1950s industrial life",
        "the main power cables glowing with energy as they snake through a maintenance tunnel, sparks",
        "a final triumphant shot of the base with the American flag planted firmly in the foreground, 1950s space race"
    ]

    pipe = get_flux()

    for i, scene_prompt in enumerate(scenes):
        name = f"book_page_{i:02d}"
        output_path = os.path.join(BOOK_DIR, f"{name}.png")
        prompt_path = os.path.join(BOOK_DIR, f"{name}.txt")
        
        if os.path.exists(output_path):
            print(f"Skipping {name} (already exists)")
            continue

        full_prompt = base_prompt + scene_prompt
        print(f"Generating Book Image {i+1}/32: {scene_prompt[:50]}...")
        
        image = pipe(
            full_prompt,
            num_inference_steps=4,
            guidance_scale=0.0,
            width=1024,
            height=768,
            max_sequence_length=256
        ).images[0]

        image.save(output_path)
        with open(prompt_path, "w") as f:
            f.write(f"Model: black-forest-labs/FLUX.1-schnell\nPrompt: {full_prompt}\n")
        print(f"Saved to {output_path}")

    print("\nAll book images generated successfully!")

if __name__ == "__main__":
    main()
