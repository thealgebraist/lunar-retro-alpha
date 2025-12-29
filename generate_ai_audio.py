import os
import torch
import scipy.io.wavfile
from transformers import AutoProcessor, BarkModel, AudioLDM2GeneratorPipeline

def generate_voice():
    print("Generating voice with bark-small...")
    device = "cuda" if torch.cuda.is_available() else "cpu"
    # Note: On Mac, "mps" is available but Bark might have issues with it, sticking to cpu for stability if not cuda.
    
    processor = AutoProcessor.from_pretrained("suno/bark-small")
    model = BarkModel.from_pretrained("suno/bark-small").to(device)
    
    # Text with cues for bark
    text_prompt = "[sigh] Log entry 4-1-2. We were hit. That meteor shower... it came out of nowhere. [pause] Hull breach in sector 7. Things went downhill fast. Life support is failing. [static] Everyone... disappeared into the tunnels. I'm the only one left."
    
    inputs = processor(text_prompt, voice_preset="v2/en_speaker_6") # A clear male voice
    
    with torch.no_grad():
        audio_array = model.generate(**inputs.to(device))
        audio_array = audio_array.cpu().numpy().squeeze()
    
    sample_rate = model.generation_config.sample_rate
    scipy.io.wavfile.write("moon_base_assets/bark_voice.wav", rate=sample_rate, data=audio_array)
    print("Bark voice generated.")

def generate_background():
    print("Generating background with audioldm2-large...")
    device = "cuda" if torch.cuda.is_available() else "cpu"
    
    # If on Mac and no cuda, try to use a smaller model if needed, but the user said audioldm2-large is in cache
    repo_id = "cvssp/audioldm2-large"
    pipe = AudioLDM2GeneratorPipeline.from_pretrained(repo_id, torch_dtype=torch.float32)
    pipe.to(device)
    
    prompt = "space station background humming, distant explosions, metal crashing, eerie silence"
    negative_prompt = "low quality, music"
    
    audio = pipe(prompt, negative_prompt=negative_prompt, num_inference_steps=20, audio_length_in_s=30).audios[0]
    
    scipy.io.wavfile.write("moon_base_assets/background_hum.wav", rate=16000, data=audio)
    print("Background audio generated.")

def mix_audio():
    print("Mixing audio with ffmpeg...")
    cmd = [
        "ffmpeg", "-y",
        "-i", "moon_base_assets/bark_voice.wav",
        "-i", "moon_base_assets/background_hum.wav",
        "-filter_complex", "[0:a]volume=2.0,highpass=f=200,lowpass=f=3500[v];[1:a]volume=0.5[bg];[v][bg]amix=inputs=2:duration=longest[out]",
        "-map", "[out]",
        "-c:a", "libvorbis",
        "moon_base_assets/tape_log.ogg"
    ]
    import subprocess
    subprocess.run(cmd)
    print("Final tape log mixed.")

if __name__ == "__main__":
    if not os.path.exists("moon_base_assets"):
        os.makedirs("moon_base_assets")
        
    try:
        generate_voice()
    except Exception as e:
        print(f"Bark generation failed: {e}")
        
    try:
        generate_background()
    except Exception as e:
        print(f"AudioLDM2 generation failed: {e}")
        
    mix_audio()
