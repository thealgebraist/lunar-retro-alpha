import os
import sys
import time
from typing import Final, Optional
from runwayml import RunwayML

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Configure API Key
API_KEY = os.environ.get("RUNWAYML_API_SECRET")
if not API_KEY:
    try:
        with open("runway_api_key.txt", "r") as f:
            API_KEY = f.read().strip()
    except FileNotFoundError:
        pass

# Constants
MODEL_NAME: Final[str] = "gen4_turbo"
PROMPT: Final[str] = (
    "A cinematic, high-detail wide shot of a derelict 1950s-style moon base. "
    "The base consists of rusted chrome domes and retro-futuristic antennas. "
    "The camera flies past slowly from a distance. Through the thick glass portholes, "
    "tiny silhouettes of people are visible moving inside. "
    "Lunar dust kicks up in the foreground. High contrast, 35mm film grain, sci-fi noir."
)

def generate_runway_video(prompt: str, output_path: str) -> Optional[str]:
    """
    Generates a video using Runway Gen-4 Turbo.
    """
    if not API_KEY:
        print("Error: RUNWAYML_API_SECRET is required for Runway generation.")
        return None

    print(f"Initializing RunwayML client...")
    client = RunwayML(api_key=API_KEY)

    print(f"Starting video generation for prompt: {prompt}")
    try:
        # Submit the generation request
        # Runway Gen-4 Turbo typically uses image_to_video or similar depending on exact SDK
        # For text-to-video, check supported methods
        task = client.image_to_video.create(
            model=MODEL_NAME,
            prompt_text=prompt,
            # Note: For pure text-to-video, some SDKs might use different endpoints
            # but Gen-4 Turbo often excels with image prompts.
        )
        
        task_id = task.id
        print(f"Generation task started. ID: {task_id}")
        print("Waiting for video generation to complete...")
        
        # Poll for completion
        while True:
            task = client.tasks.retrieve(task_id)
            status = task.status
            print(f"Task status: {status}")
            
            if status == "SUCCEEDED":
                print("Video generation complete!")
                video_url = task.output[0]
                print(f"Video URL: {video_url}")
                
                # Save metadata
                with open(output_path.replace(".mp4", ".metadata.txt"), "w") as f:
                    f.write(str(task))
                
                # Download logic would go here
                return output_path
            elif status == "FAILED":
                print(f"Task failed: {task.error}")
                return None
            
            time.sleep(10)

    except Exception as e:
        print(f"Error during Runway generation: {e}")
        return None

def main() -> None:
    if not API_KEY:
        print("Please set the RUNWAYML_API_SECRET environment variable or create runway_api_key.txt")
        return

    output_filename = "moon_base_cinematic.mp4"
    print("Starting generation using Runway Gen-4 Turbo...")
    result_path = generate_runway_video(PROMPT, output_filename)

    if result_path:
        print(f"Process complete. Metadata saved for: {result_path}")
    else:
        print("Generation failed.")

if __name__ == "__main__":
    main()
