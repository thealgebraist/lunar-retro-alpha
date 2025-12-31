import os
import sys
import torch
import scipy.io.wavfile
import numpy as np
import subprocess
from transformers import AutoProcessor, BarkModel

# Add local libs
sys.path.insert(0, os.path.abspath("local_libs"))

# Constants
HQ_DIR = "moon_base_assets_hq"
GAME_DIR = "moon_base_assets"
DEVICE = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"

if not os.path.exists(HQ_DIR):
    os.makedirs(HQ_DIR)
if not os.path.exists(GAME_DIR):
    os.makedirs(GAME_DIR)

# Model
bark_processor = None
bark_model = None

def get_bark():
    global bark_processor, bark_model
    if bark_model is None:
        print("Loading Bark Large...")
        bark_processor = AutoProcessor.from_pretrained("suno/bark")
        bark_model = BarkModel.from_pretrained("suno/bark").to(DEVICE)
    return bark_processor, bark_model

def gen_history_segment(text, filename, preset="v2/en_speaker_6"):
    wav_path = os.path.join(HQ_DIR, filename + ".wav")
    if os.path.exists(wav_path):
        # Always overwrite for the 180s expansion
        pass

    print(f"Generating Long History Segment: {filename}...")
    processor, model = get_bark()
    
    # Bark is limited to ~14s per generation. We must split the text.
    # Split by common sentence delimiters
    import re
    chunks = re.split(r'([.!?])', text)
    # Recombine delimiters with sentences
    sentences = []
    for i in range(0, len(chunks)-1, 2):
        sentences.append(chunks[i] + chunks[i+1])
    if len(chunks) % 2 != 0:
        sentences.append(chunks[-1])
    
    full_audio = []
    for sentence in sentences:
        if not sentence.strip(): continue
        print(f"  Generating chunk: {sentence[:30]}...")
        inputs = processor(sentence.strip(), voice_preset=preset)
        with torch.no_grad():
            audio_array = model.generate(**inputs.to(DEVICE))
            full_audio.append(audio_array.cpu().numpy().squeeze())
    
    final_audio = np.concatenate(full_audio)
    scipy.io.wavfile.write(wav_path, rate=model.generation_config.sample_rate, data=final_audio)
    return wav_path

def convert_to_ogg(wav_path, ogg_name):
    print(f"Converting to {ogg_name}.ogg...")
    ogg_path = os.path.join(GAME_DIR, ogg_name + ".ogg")
    # Tape-like quality
    filter_cmd = ["-af", "highpass=f=200,lowpass=f=3500,volume=1.5"]
    subprocess.run(['ffmpeg', '-y', '-i', wav_path] + filter_cmd + ['-c:a', 'libvorbis', '-q:a', '4', ogg_path], 
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():
    history_segments = [
        {
            "name": "history_1_origins",
            "text": "[clears throat] Log entry one. September twelfth, nineteen fifty-four. The construction of the primary observation dome is officially complete. Standing here, looking through the reinforced glass, it is hard to put into words the sheer scale of our achievement. Above us, the stars are not points of light, but brilliant, unblinking beacons. And Earth... it hangs there, a fragile blue marble in the infinite dark. We are the first true pioneers. Every rivet, every weld, represents the pinnacle of human ingenuity. We're here to stay, building a future where science and progress know no bounds. It's a new frontier, and we are its masters. The initial deployment was fraught with challenges. The lunar dust, finer than flour and sharper than glass, infiltrated our early prototypes within hours. I remember the frantic repairs in the makeshift airlocks, the smell of ozone and fear. But we persevered. We learned to respect the silence of the moon. We built our concrete brutalist monoliths into the very crust, deep enough to shield us from the relentless solar radiation. This isn't just a research outpost; it's the first city of a new era. I can see the lights of the cargo bay from here, glowing like embers in the dark. We are no longer guests here. We are the architects of a lunar civilization. Every day, more rockets arrive, bringing more supplies, more scientists, more dreamers. We are carving our names into history, one ton of lunar regolith at a time. The air in the dome still smells of new plastic and fresh oxygen, a scent I've come to associate with hope. We're doing it. We're really doing it.",
            "preset": "v2/en_speaker_6"
        },
        {
            "name": "history_2_life",
            "text": "Life on Tycho Station has settled into a rhythmic, if cramped, routine. It isn't all scientific breakthroughs and mapping craters. Last night, we had our first real 'mess hall night'. [laughs] Dr. Aris managed to sneak in some old jazz tapes, and for a few hours, the sound of a saxophone filled the metal corridors. The coffee is still absolutely terrible—honestly, it tastes like recycled plastic and industrial lubricant—but the camaraderie... that's what keeps us sane. We're a family up here, two hundred thousand miles from the nearest home, sharing stories of the lives we left behind while staring out at the silent lunar plains. We make our own warmth in this cold, grey world. We've developed our own culture, our own slang. We talk about 'dusting' when we have to go out on EVA, and 'venting' when we just need to shout into the void. The bunk rooms are small, yes, but they are ours. I've pinned a picture of my wife and children to the metal wall above my bed, a constant reminder of why we are here. We're building a world where they can one day walk under a blue sky without a suit. The work is hard, the hours are long, and the environment is unforgiving, but there's a sense of purpose that you just don't find back on Earth. Every successful harvest in the hydroponics bay, every new kilometer of tunnel mapped, feels like a personal victory for all of us. We share our meals, our jokes, and our fears. When the lights dim for the 'night' cycle, and the station hums with the sound of the air scrubbers, I feel a strange sense of peace. We are the lucky ones. We are the ones who dared to look up and stay there. Even the recycled water, with its faint metallic tang, is a reminder of our survival and our progress. We are living the dream of a thousand generations.",
            "preset": "v2/en_speaker_6"
        },
        {
            "name": "history_3_golden",
            "text": "The golden age of lunar exploration is upon us. The reactor is humming at full capacity, providing more power than we ever dreamed possible. Our teams have successfully mapped the entire interior of the Tycho crater, and the geological findings are beyond belief. [sigh] There's even serious talk at HQ about establishing a second base in the Mare Serenitatis. Everything was perfect. We were the kings of the moon, living in a brutalist paradise of concrete and chrome. I remember standing on the upper gantry, watching the cargo shuttles arrive with fresh supplies and new faces, feeling a sense of absolute certainty. We were the future. I truly believed this would last forever, that we had conquered the void. The station was a hub of activity, a vibrant ecosystem of science and industry. We were discovering rare isotopes, testing new propulsion systems, and even experimenting with low-gravity manufacturing. The dividends from our research were starting to change life back on Earth, and we felt like the heroes of a new age. There was talk of a permanent colony, of children being born on the moon. We were no longer just scientists; we were the founding fathers of a lunar nation. The pride we felt was palpable. Every time a new module was pressurized, every time the comms uplink to Earth showed a clear signal, we celebrated. We were the pinnacle of human achievement, the shining city on a hill—or rather, the shining dome in a crater. The possibilities seemed endless. We were even planning the first manned mission to Mars, using Tycho Base as our primary staging point. It was a time of unbridled optimism, a time when we believed that anything was possible if we just had enough concrete, enough steel, and enough will. We were untouchable. The void wasn't our enemy; it was our canvas.",
            "preset": "v2/en_speaker_6"
        },
        {
            "name": "history_4_downfall",
            "text": "[breathing heavily and erratically] Everything happened so fast. Too fast. The breach in sector seven... it wasn't just a simple hull leak like the alarms suggested. [loud static noise] Something is fundamentally wrong with the air scrubbers. People... they're changing. I can hear them scratching at the bulkhead doors. I've locked myself in the comms array, the last secure room on this level. The sapphire glow of the reactor is flickering, dying. If anyone, anywhere, finds this recording... [whispers] please, stay away. Do not come looking for us. Whatever we found in the deep mines, it wasn't meant for human eyes. It's over. The station is silent now, except for the scratching. The evacuation pods were sabotaged, or maybe just failed in the panic. I watched the last one drift away, empty, into the black. My colleagues, my friends... I don't recognize them anymore. Their eyes... they glow with a strange, sickly light. They don't speak; they just make that horrible scratching sound. The power is failing throughout the station. The life support systems are groaning under the strain. I've got enough oxygen for maybe another hour, if I don't panic. But what's the point? There's nowhere to go. The Earth looks so beautiful from here, so calm and peaceful. They have no idea what's happening up here. They'll just see the lights of Tycho Base go out, one by one, and wonder why. [loud crash in the distance] They're through the first bulkhead. I can hear their footsteps on the metal grating. They're coming for me. I've got my sidearm, but I only have three rounds left. I won't let them take me alive. I won't become... whatever they are. [sobbing quietly] To my wife, my children... I love you. I'm so sorry. I thought we were building a future. I didn't know we were digging our own grave. The scratching... it's right outside the door now. [static intensifies, then silence]",
            "preset": "v2/en_speaker_6"
        }
    ]

    for seg in history_segments:
        wav = gen_history_segment(seg["text"], seg["name"], preset=seg["preset"])
        convert_to_ogg(wav, seg["name"])

    print("\nHistory tapes generated successfully!")

if __name__ == "__main__":
    main()