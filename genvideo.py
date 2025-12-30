import os
import sys
import time
from typing import Final, Optional
from google import genai
from google.genai import types

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Configure API Key
API_KEY = os.environ.get("GOOGLE_API_KEY")
if not API_KEY:
    try:
        with open("google_api_key.txt", "r") as f:
            API_KEY = f.read().strip()
    except FileNotFoundError:
        pass

# Constants
MODEL_NAME: Final[str] = "veo-3.1-generate-preview"
PROMPT: Final[str] = (
    "A cinematic, high-detail wide shot of a derelict 1950s-style moon base. "
    "The base consists of rusted chrome domes and retro-futuristic antennas. "
    "The camera flies past slowly from a distance. Through the thick glass portholes, "
    "tiny silhouettes of people are visible moving inside. "
    "Lunar dust kicks up in the foreground. High contrast, 35mm film grain, sci-fi noir."
)

def generate_veo_video(prompt: str, output_path: str) -> Optional[str]:
    """
    Generates a video using Google DeepMind Veo via the new GenAI SDK.
    """
    if not API_KEY:
        print("Error: API Key is required for Veo generation.")
        return None

    print(f"Initializing GenAI client for Veo 3.1...")
    client = genai.Client(api_key=API_KEY, http_options={'api_version': 'v1alpha'})

    print(f"Starting video generation for prompt: {prompt}")
    try:
        # Use the correct method for video generation
        operation = client.models.generate_videos(
            model=MODEL_NAME,
            prompt=prompt,
            config=types.GenerateVideosConfig(
                number_of_videos=1,
            )
        )
        
        print(f"Generation operation started. ID: {operation.name}")
        print("Waiting for video generation to complete (this can take several minutes)...")
        
        # Poll for completion
        while not operation.done:
            print("Polling for results...")
            time.sleep(30)
            operation = client.operations.get(operation.name)
            
        if operation.result:
            print("Video generation complete!")
            # The result structure contains video data or URIs
            # For Veo, it often returns a URI or direct bytes depending on the platform
            video = operation.result.generated_videos[0]
            print(f"Video result: {video}")
            
            # Save metadata
            with open(output_path.replace(".mp4", ".metadata.txt"), "w") as f:
                f.write(str(video))
            
            # Download/save logic would go here if direct bytes/URI provided
            # Note: This SDK might require specific file handling to save to disk
            return output_path
        else:
            print("Operation finished but no result found.")
            return None

    except Exception as e:
        print(f"Error during Veo generation: {e}")
        return None

def main() -> None:
    if not API_KEY:
        print("Please set the GOOGLE_API_KEY environment variable or create google_api_key.txt")
        return

    output_filename = "moon_base_cinematic.mp4"
    print("Starting generation using Google DeepMind Veo (GenAI SDK)...")
    result_path = generate_veo_video(PROMPT, output_filename)

    if result_path:
        print(f"Process complete. Metadata saved for: {result_path}")
    else:
        print("Generation failed.")

if __name__ == "__main__":
    main()